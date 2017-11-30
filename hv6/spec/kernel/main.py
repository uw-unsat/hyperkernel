#
# Copyright 2017 Hyperkernel Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

import sys
import argparse
import copy
import unittest
import inspect

import libirpy
import libirpy.util as util
import libirpy.solver as solver
import libirpy.ex as ex
import libirpy.itypes as itypes
from libirpy.datatypes import BitcastPointer

import hv6py.kernel.impl as hv6

import syscall_spec
import datatypes as dt
import z3
import spec


INTERACTIVE = False
# generate / minimize model declarative specs
MODEL_HI = False
Solver = solver.Solver


_syscalls = [
    "sys_map_pml4",
    "sys_map_page_desc",
    "sys_map_proc",
    "sys_map_dev",
    "sys_map_file",
    "sys_alloc_pdpt",
    "sys_alloc_pd",
    "sys_alloc_pt",
    "sys_alloc_frame",
    "sys_copy_frame",
    "sys_protect_frame",
    "sys_free_pdpt",
    "sys_free_pd",
    "sys_free_pt",
    "sys_free_frame",
    "sys_reclaim_page",
    "clone_proc", # sys_clone
    "sys_set_proc_name",
    "sys_set_runnable",
    "switch_proc", # sys_switch
    "sys_kill",
    "sys_reap",
    "sys_reparent",
    "send_proc", # sys_send
    "recv_proc", # sys_recv
    "reply_wait_proc", # sys_reply_wait
    "call_proc", # sys_call
    "sys_create",
    "sys_close",
    "sys_dup",
    "sys_dup2",
    "sys_lseek",
    "sys_map_pcipage",
    "sys_alloc_iommu_root",
    "sys_alloc_iommu_pdpt",
    "sys_alloc_iommu_pd",
    "sys_alloc_iommu_pt",
    "sys_alloc_iommu_frame",
    "sys_map_iommu_frame",
    "sys_reclaim_iommu_frame",
    "sys_reclaim_iommu_root",
    "sys_alloc_vector",
    "sys_reclaim_vector",
    "sys_alloc_intremap",
    "sys_reclaim_intremap",
    "sys_ack_intr",
    "sys_alloc_io_bitmap",
    "sys_alloc_port",
    "sys_reclaim_port",
    "extintr",
]


def panic(ctx, *args, **kwargs):
    ue = ex.UnreachableException(ctx.path_condition[-1])
    ue.stacktrace = copy.deepcopy(ctx.stacktrace[-1])


def putchar(ctx, *args, **kwargs):
    return


def memcpy(ctx, dst, src, size):
    if isinstance(dst, BitcastPointer):
        dst = dst._ptr

    if isinstance(src, BitcastPointer):
        src = src._ptr

    # Same paranoid checks
    assert dst.type().is_pointer()
    assert src.type().is_pointer()

    assert dst.type().deref().is_array()
    assert src.type().deref().is_array()

    assert dst.type().deref().size() == src.type().deref().size()
    assert dst.type().deref().length() == src.type().deref().length()

    dst_start = dst.getelementptr(ctx, util.i64(0), util.i64(0))
    src_start = src.getelementptr(ctx, util.i64(0), util.i64(0))

    dst_end = dst.getelementptr(ctx, util.i64(0), util.i64(0))
    src_end = src.getelementptr(ctx, util.i64(0), util.i64(0))

    dst_start_path = dst_start.canonical_path()
    src_start_path = src_start.canonical_path()

    dst_end_path = dst_end.canonical_path()
    src_end_path = src_end.canonical_path()

    assert dst_start_path[-1].as_long() == src_start_path[-1].as_long()
    assert dst_end_path[-1].as_long() == src_end_path[-1].as_long()

    dst_tup, dst_start_args = dst._ref.build_field_tuple_and_path(
        ctx, dst_start_path)
    src_tup, src_start_args = src._ref.build_field_tuple_and_path(
        ctx, src_start_path)

    _, dst_end_args = dst._ref.build_field_tuple_and_path(ctx, dst_end_path)
    _, src_end_args = src._ref.build_field_tuple_and_path(ctx, src_end_path)

    dst_end_args[-1] += size
    src_end_args[-1] += size

    assert len(dst_start_args) == len(dst_end_args)
    assert len(dst_end_args) == len(src_end_args)

    dstfn = ctx['references'][dst._ref._name][dst_tup]
    srcfn = ctx['references'][src._ref._name][src_tup]

    # At this point we know that the src and dst are same-sized arrays.
    # They are both indexed starting from 0 up to length - 1.
    # So, we just do update the uf using an ite of the form
    # arg1 == dst_arg1, arg2 == dst_arg2, .. dst_argn_start <= arg1 < dst_argn_end

    def newf(*args):
        assert len(args) == len(dst_end_args)
        cond = []
        for a, b in zip(args[:-1], dst_start_args[:-1]):
            cond.append(a == b)

        cond.append(z3.UGE(args[-1], dst_start_args[-1]))
        cond.append(z3.ULT(args[-1], dst_end_args[-1]))

        cond = z3.And(*cond)

        srcargs = src_start_args[:-1] + [args[-1]]

        return util.If(cond, srcfn(*srcargs), dstfn(*args))

    ctx['references'][dst._ref._name][dst_tup] = newf

    return dst


def memset(ctx, ptr, val, size):
    val = z3.Extract(7, 0, val)

    size = size.as_long()

    # If we're passed a bitcasted pointer we just check if the write size is a
    # multiple of the underlying types write size, then we can just ignore the bitcast.
    if isinstance(ptr, BitcastPointer):
        ptr = ptr._ptr

    inner = ptr.type().deref()

    # We are memsetting an array whose inner type matches the size of the val
    assert inner.is_array()
    assert inner.deref().size() % val.size() == 0

    val = z3.Concat(*([val] * (inner.deref().size() / val.size())))

    if inner.deref().is_int():
        array_len = ptr.type().deref().length()

        dst_start = ptr.getelementptr(ctx, util.i64(0), util.i64(0))
        dst_end = ptr.getelementptr(
            ctx, util.i64(0), util.i64(array_len - 1))

        dst_start_path = dst_start.canonical_path()
        dst_end_path = dst_end.canonical_path()

        dst_tup, dst_start_args = ptr._ref.build_field_tuple_and_path(
            ctx, dst_start_path)
        _, dst_end_args = ptr._ref.build_field_tuple_and_path(
            ctx, dst_end_path)

        dstfn = ctx['references'][ptr._ref._name][dst_tup]

        def newf(*args):
            assert len(args) == len(dst_end_args)
            cond = []
            for a, b in zip(args[:-1], dst_start_args[:-1]):
                cond.append(a == b)

            cond.append(z3.UGE(args[-1], dst_start_args[-1]))
            cond.append(z3.ULE(args[-1], dst_end_args[-1]))

            cond = z3.And(*cond)

            return util.If(cond, val, dstfn(*args))

        ctx['references'][ptr._ref._name][dst_tup] = newf
        return ptr

    else:
        raise NotImplementedError(
            "Don't know how to memset {!r}".format(inner))


def bzero(ctx, ptr, size):
    size = size.as_long()

    # If we're passed a bitcasted pointer we just check if the write size is a
    # multiple of the underlying types write size, then we can just ignore the bitcast.
    if isinstance(ptr, BitcastPointer):
        ptr = ptr._ptr

    inner = ptr.type().deref()

    if inner.is_int():
        assert size * 8 <= 64
        ptr.write(ctx, z3.BitVecVal(0, size * 8))
    elif inner.is_struct():
        assert inner.size() / \
            8 == size, "Can not partially bzero a struct: {} v {}".format(
                inner.size() / 8, size)

        for i, field in enumerate(inner.fields()):
            subptr = ptr.getelementptr(ctx, util.i64(0), util.i64(i),
                                       type=itypes.PointerType(field))
            bzero(ctx, subptr, z3.simplify(z3.BitVecVal(field.size() / 8, 64)))
    elif inner.is_array():
        write_size = inner.deref().size()

        if inner.deref().is_int():

            array_len = ptr.type().deref().length()

            dst_start = ptr.getelementptr(ctx, util.i64(0), util.i64(0))
            dst_end = ptr.getelementptr(
                ctx, util.i64(0), util.i64(array_len - 1))

            dst_start_path = dst_start.canonical_path()
            dst_end_path = dst_end.canonical_path()

            dst_tup, dst_start_args = ptr._ref.build_field_tuple_and_path(
                ctx, dst_start_path)
            _, dst_end_args = ptr._ref.build_field_tuple_and_path(
                ctx, dst_end_path)

            dstfn = ctx['references'][ptr._ref._name][dst_tup]

            def newf(*args):
                assert len(args) == len(dst_end_args)
                cond = []
                for a, b in zip(args[:-1], dst_start_args[:-1]):
                    cond.append(a == b)

                cond.append(z3.UGE(args[-1], dst_start_args[-1]))
                cond.append(z3.ULE(args[-1], dst_end_args[-1]))

                cond = z3.And(*cond)

                return util.If(cond, z3.BitVecVal(0, write_size), dstfn(*args))

            ctx['references'][ptr._ref._name][dst_tup] = newf

        else:
            raise NotImplementedError(
                "Don't know how to bzero {!r}".format(inner))

    else:
        raise NotImplementedError("Don't know how to bzero {!r}".format(inner))


def hvm_set_cr3(ctx, *args, **kwargs):
    pass
hvm_set_cr3.read = lambda *args: hvm_set_cr3


def hvm_set_timer(ctx, *args, **kwargs):
    pass
hvm_set_timer.read = lambda *args: hvm_set_timer


def hvm_set_io_bitmap(ctx, *args, **kwargs):
    pass
hvm_set_io_bitmap.read = lambda *args: hvm_set_io_bitmap


def hvm_copy(ctx, *args, **kwargs):
    pass
hvm_copy.read = lambda *args: hvm_copy


def hvm_flush(ctx, *args, **kwargs):
    pass
hvm_flush.read = lambda *args: hvm_flush


def hvm_invalidate_tlb(ctx, pid):
    uf = ctx.globals['#tlbinv']
    ctx.globals['#tlbinv'] = util.partial_update(uf, (pid,), z3.BoolVal(True))
hvm_invalidate_tlb.read = lambda *args: hvm_invalidate_tlb


def hvm_switch(ctx, *args, **kwargs):
    raise util.NoReturn()
hvm_switch.read = lambda *args: hvm_switch


def iommu_set_dev_root(ctx, devid, addr):
    pass
iommu_set_dev_root.read = lambda *args: iommu_set_dev_root


def iommu_get_dev_root(ctx, devid):
    pass
iommu_get_dev_root.read = lambda *args: iommu_get_dev_root


def iommu_set_intremap(ctx, index, id, irq):
    pass
iommu_set_intremap.read = lambda *args: iommu_set_intremap


def iommu_reset_dev_root(ctx, devid):
    pass
iommu_reset_dev_root.read = lambda *args: iommu_reset_dev_root


def iommu_reset_intremap(ctx, index):
    pass
iommu_reset_intremap.read = lambda *args: iommu_reset_intremap


def iommu_flush(ctx):
    ctx.globals['#iotlbinv'] = z3.BoolVal(True)
iommu_flush.read = lambda *args: iommu_flush


def iommu_hack_root(ctx, addr4, addr3):
    pass
iommu_hack_root.read = lambda *args: iommu_hack_root


def iommu_entry(ctx, addr, perm, level):
    return addr | perm
iommu_entry.read = lambda *args: iommu_entry


def ms_to_cycles(ctx, ms):
    return util.FreshBitVec('cycles', dt.uint64_t)
ms_to_cycles.read = lambda *args: ms_to_cycles


def pdb(ctx, *args):
    from ipdb import set_trace
    set_trace()
    return util.i64(0)
pdb.read = lambda *args: pdb


def syslog(ctx, *args):
    pass
syslog.read = lambda *args: syslog


class HV6Meta(type):
    def __new__(cls, name, parents, dct):
        cls._add_funcs(name, parents, dct)
        return super(HV6Meta, cls).__new__(cls, name, parents, dct)

    @classmethod
    def _add_funcs(cls, name, parents, dct):
        syscalls = dct.get('syscalls_generic', [])

        for syscall in syscalls:
            dct['test_{}'.format(syscall)] = lambda self, syscall=syscall: \
                self._syscall_generic(syscall)


class HV6Base(unittest.TestCase):
    __metaclass__ = HV6Meta

    def _prove(self, cond, pre=None, return_model=False, minimize=True):
        if minimize:
            self.solver.push()
        self.solver.add(z3.Not(cond))

        res = self.solver.check()
        if res != z3.unsat:
            if not minimize and not return_model:
                self.assertEquals(res, z3.unsat)

            model = self.solver.model()
            if return_model:
                return model

            print "Could not prove, trying to find a minimal ce"
            assert res != z3.unknown
            if z3.is_and(cond):
                self.solver.pop()
                # Condition is a conjunction of some child clauses.
                # See if we can find something smaller that is sat.

                if pre is not None:
                    ccond = sorted(
                        zip(cond.children(), pre.children()), key=lambda x: len(str(x[0])))
                else:
                    ccond = sorted(cond.children(), key=lambda x: len(str(x)))

                for i in ccond:
                    self.solver.push()
                    if isinstance(i, tuple):
                        self._prove(i[0], pre=i[1])
                    else:
                        self._prove(i)
                    self.solver.pop()

            print "Can not minimize condition further"
            if pre is not None:
                print "Precondition"
                print pre
                print "does not imply"
            print cond
            self.assertEquals(model, [])


def newctx():
    ctx = libirpy.newctx()
    # If we don't need the values of any constants we don't have to
    # initialize them, slightly faster execution time.
    ctx.eval.declare_global_constant = ctx.eval.declare_global_variable
    libirpy.initctx(ctx, hv6)

    ctx.globals['#tlbinv'] = util.FreshFunction('tlbinv', dt.pid_t, dt.bool_t)
    ctx.globals['#iotlbinv'] = util.FreshBool('iotlbinv')

    ctx.globals['@panic'] = panic
    ctx.globals['@bzero'] = bzero
    ctx.globals['@memset'] = memset
    ctx.globals['@memcpy'] = memcpy
    ctx.globals['@putchar'] = putchar
    ctx.globals['@hvm_set_cr3'] = hvm_set_cr3
    ctx.globals['@hvm_copy'] = hvm_copy
    ctx.globals['@hvm_flush'] = hvm_flush
    ctx.globals['@hvm_set_timer'] = hvm_set_timer
    ctx.globals['@hvm_set_io_bitmap'] = hvm_set_io_bitmap
    ctx.globals['@hvm_invalidate_tlb'] = hvm_invalidate_tlb
    ctx.globals['@hvm_switch'] = hvm_switch
    ctx.globals['@pdb'] = pdb
    ctx.globals['@syslog'] = syslog

    # iommu fns
    ctx.globals['@iommu_set_dev_root'] = iommu_set_dev_root
    ctx.globals['@iommu_get_dev_root'] = iommu_get_dev_root
    ctx.globals['@iommu_set_intremap'] = iommu_set_intremap
    ctx.globals['@iommu_reset_intremap'] = iommu_reset_intremap
    ctx.globals['@iommu_reset_dev_root'] = iommu_reset_dev_root
    ctx.globals['@iommu_flush'] = iommu_flush
    ctx.globals['@iommu_hack_root'] = iommu_hack_root
    ctx.globals['@iommu_entry'] = iommu_entry
    ctx.globals['@ms_to_cycles'] = ms_to_cycles

    # Provide the "integer value" of some globals
    ctx.ptr_to_int[ctx.globals['@pages']._ref._name] = util.FreshBitVec( '(uintptr)@pages', 64)
    ctx.ptr_to_int[ctx.globals['@proc_table']._ref._name] = util.FreshBitVec( '(uintptr)@proc_table', 64)
    ctx.ptr_to_int[ctx.globals['@page_desc_table']._ref._name] = util.FreshBitVec( '(uintptr)@page_desc_table', 64)
    ctx.ptr_to_int[ctx.globals['@file_table']._ref._name] = util.FreshBitVec( '(uintptr)@file_table', 64)
    ctx.ptr_to_int[ctx.globals['@devices']._ref._name] = util.FreshBitVec( '(uintptr)@devices', 64)
    ctx.ptr_to_int[ctx.globals['@devices']._ref._name] = util.FreshBitVec( '(uintptr)@devices', 64)
    ctx.ptr_to_int[ctx.globals['@dmapages']._ref._name] = util.FreshBitVec( '(uintptr)@dmapages', 64)

    return ctx


class HV6(HV6Base):
    def setUp(self):
        self.ctx = newctx()
        self.state = dt.KernelState()

        self.solver = Solver()
        self.solver.set(AUTO_CONFIG=False)

        self._pre_state = spec.state_equiv(self.ctx, self.state)
        self.ctx.add_assumption(spec.impl_invariants(self.ctx))
        self.solver.add(self._pre_state)

    def tearDown(self):
        if isinstance(self.solver, solver.Solver):
            del self.solver

    def test_preempt(self):
        with self.assertRaises(util.NoReturn):
            self.ctx.call('@preempt')
        pid = util.FreshBitVec('pid', dt.pid_t)
        newstate = spec.switch_proc(self.state, pid)[1]
        self._prove(z3.Exists([pid], spec.state_equiv(self.ctx, newstate)))

    def test_fault(self):
        with self.assertRaises(util.NoReturn):
            self.ctx.call('@fault')
        pid = util.FreshBitVec('pid', dt.pid_t)
        s = self.state.copy()
        s.procs[s.current].killed = z3.BoolVal(True)
        newstate = spec.switch_proc(s, pid)[1]
        self._prove(z3.Exists([pid], spec.state_equiv(self.ctx, newstate)))

    def _syscall_generic(self, name):
        args = syscall_spec.get_syscall_args(name)
        res = self.ctx.call('@' + name, *args)
        cond, newstate = getattr(spec, name)(self.state, *args)
        model = self._prove(z3.And(spec.state_equiv(self.ctx, newstate),
                                   cond == (res == util.i32(0))),
                            pre=z3.And(self._pre_state, z3.BoolVal(True)),
                            return_model=INTERACTIVE)
        if INTERACTIVE and model:
            from ipdb import set_trace
            set_trace()

    syscalls_generic = _syscalls


# Test cases to check if python and c versions of implementation invariants match
class HV6ImplInvs(HV6Base):
    def setUp(self):
        self.solver = Solver()
        self.solver.set(AUTO_CONFIG=False)
        self.ctx = newctx()

    def test_inv_py_imply_c(self):
        self._prove(z3.Implies(spec.impl_invariants_py(
            self.ctx), spec.impl_invariants_c(self.ctx)))

    def test_inv_c_imply_py(self):
        self._prove(z3.Implies(spec.impl_invariants_c(
            self.ctx), spec.impl_invariants_py(self.ctx)))


class HV6SpecMeta(HV6Meta):
    @classmethod
    def _add_funcs(cls, name, parents, dct):
        syscalls = dct.get('syscalls_generic', [])
        lemmas = dct.get('lemmas', [])
        corollaries = dct.get('corollaries', [])

        for lemma in lemmas:
            for syscall in syscalls:
                dct['test_{}_{}'.format(syscall, lemma)] = lambda self, syscall=syscall, lemma=lemma: \
                    self._check_invariant(syscall, lemma)
                dct['test_{}_initial'.format(lemma)] = lambda self, lemma=lemma: self._check_initial(lemma)

        for pre, post in corollaries:
                dct['test_{}_implies_{}'.format(pre, post)] = lambda self, pre=pre, post=post: \
                        self._check_corollary(pre, post)


class HV6TopLemmas(HV6Base):
    __metaclass__ = HV6SpecMeta

    def setUp(self):
        self.solver = Solver()
        self.solver.set(AUTO_CONFIG=False)
        self.solver.set(MODEL=MODEL_HI)

        self.state = dt.KernelState()

    def tearDown(self):
        # make sure the solver and solver process are killed
        # For some reason python is keeping them around for a long time
        # eating up a bunch of ram.
        if isinstance(self.solver, solver.Solver):
            del self.solver

    def _check_invariant(self, syscall, lemma):
        inv = getattr(spec, 'spec_lemma_{}'.format(lemma))
        args = syscall_spec.get_syscall_args(syscall)

        kwargs = {}

        if 'syscall' in inspect.getargspec(inv)[0]:
            kwargs['syscall'] = syscall
        if 'oldstate' in inspect.getargspec(inv)[0]:
            kwargs['oldstate'] = self.state

        pre = z3.And(spec.spec_invariants(self.state), inv(self.state, **kwargs))

        self.solver.add(pre)
        cond, newstate = getattr(spec, syscall)(self.state, *args)
        model = self._prove(z3.And(spec.spec_invariants(newstate), inv(newstate, **kwargs)),
                            pre=pre, return_model=INTERACTIVE, minimize=MODEL_HI)

        if INTERACTIVE and model:
            from ipdb import set_trace
            set_trace()

    def _check_corollary(self, pre, post):
        pre = getattr(spec, 'spec_lemma_{}'.format(pre))
        post = getattr(spec, 'spec_corollary_{}'.format(post))

        self._prove(z3.Implies(z3.And(pre(self.state), spec.spec_invariants(self.state)),
                               post(self.state)))

        self.setUp()

        self.state = self.state.initial()
        constraints = z3.And(spec.spec_invariants(self.state), post(self.state))
        self.solver.add(constraints)
        self.assertEquals(self.solver.check(), z3.sat)

    def _check_initial(self, lemma):
        self.state = self.state.initial()
        inv = getattr(spec, 'spec_lemma_{}'.format(lemma))
        constraints = z3.And(spec.spec_invariants(self.state), inv(self.state))
        self.solver.add(constraints)
        self.assertEquals(self.solver.check(), z3.sat)

    syscalls_generic = _syscalls

    lemmas = [
        "isolation",
        "iommu_isolation",
        "nr_children_refcnt",
        "nr_fds_refcnt",
        # "nr_pages_refcnt",  ## This one is included in both isolation proofs
        "nr_dmapages_refcnt",
        # "nr_devs_refcnt",  ## This one is included in iommu_isolation
        "nr_ports_refcnt",
        "nr_vectors",
        "nr_intremaps",
        "files_refcnt",
        "tlb_ok",
        "iommu_tlb_ok",
    ]

    corollaries = [
        ("isolation", "pgwalk"),
        ("iommu_isolation", "iommu_pgwalk"),
    ]


if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument('--interactive', type=bool, nargs='?',
            default=INTERACTIVE, const=True)
    parser.add_argument('--model-hi', type=bool, nargs='?',
            default=MODEL_HI, const=True)
    args, unknown = parser.parse_known_args(sys.argv)

    INTERACTIVE = args.interactive
    MODEL_HI = args.model_hi

    del sys.argv[:]
    sys.argv.extend(unknown)

    if INTERACTIVE:
        Solver = z3.Solver

    print "Using z3 v" + '.'.join(map(str, z3.get_version()))

    unittest.main()
