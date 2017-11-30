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

import z3

import itypes
import datatypes as dt
import util
from eval import BaseIRPyEvaluator
import ex


class BaseZ3IRPyEval(BaseIRPyEvaluator):

    #############################
    # Helpers
    #############################
    def assertion(self, ctx, cond, msg=None, stacktrace=None):
        if not cond:
            util.print_stacktrace(ctx, stacktrace=stacktrace)
            if hasattr(cond, '_dbg'):
                print cond._dbg
        assert cond, msg

    def get_poison(self, type):
        if type.is_int():
            if type.size() == 1:
                return util.FreshBool('poison')
            else:
                return util.FreshBitVec('poison', type.size())
        assert False, "Can't get posion for {!r}".format(type)

    #############################
    # Binary Ops
    #############################
    def add(self, ctx, return_type, a, atype, b, btype, nuw=False, nsw=False):
        assert atype == return_type
        assert atype == btype
        if nuw:
            assert util.path_condition_implies(
                ctx, util.bvadd_no_overflow(a, b, signed=False), print_model=True)
        if nsw:
            assert util.path_condition_implies(
                ctx, util.bvadd_no_overflow(a, b, signed=True), print_model=True)
        return a + b

    def sub(self, ctx, return_type, a, atype, b, btype, nuw=False, nsw=False):
        assert atype == return_type
        assert atype == btype
        assert not nuw and not nsw
        return a - b

    def mul(self, ctx, return_type, a, atype, b, btype, nuw=False, nsw=False):
        assert atype == return_type
        assert atype == btype
        assert not nuw and not nsw
        return a * b

    def udiv(self, ctx, return_type, a, atype, b, btype, nuw=False, nsw=False, exact=False):
        assert atype == return_type
        assert atype == btype
        assert not nuw and not nsw and not exact
        assert util.path_condition_implies(
            ctx, b != z3.BitVecVal(0, btype.size()), print_model=True), "udiv by zero"
        return z3.UDiv(a, b)

    def sdiv(self, ctx, return_type, a, atype, b, btype, nuw=False, nsw=False, exact=False):
        assert atype == return_type
        assert atype == btype
        assert not nuw and not nsw and not exact
        assert util.path_condition_implies(
            ctx, b != z3.BitVecVal(0, btype.size()), print_model=True), "sdiv by zero"
        return a / b

    def urem(self, ctx, return_type, a, atype, b, btype, nuw=False, nsw=False, exact=False):
        assert atype == return_type
        assert atype == btype
        assert not nuw and not nsw and not exact
        assert util.path_condition_implies(
            ctx, b != z3.BitVecVal(0, btype.size())), "urem by zero"
        return z3.URem(a, b)

    def srem(self, ctx, return_type, a, atype, b, btype, nuw=False, nsw=False, exact=False):
        assert atype == return_type
        assert atype == btype
        assert not nuw and not nsw and not exact
        assert util.path_condition_implies(
            ctx, b != z3.BitVecVal(0, btype.size())), "srem by zero"
        return z3.SRem(a, b)

    #############################
    # Logical Ops
    #############################
    def shl(self, ctx, return_type, a, atype, b, btype, nuw=False, nsw=False):
        assert atype == return_type
        assert atype == btype
        assert not nuw and not nsw
        return util.partial_eval(ctx,
                util.If(z3.ULT(b, z3.BitVecVal(btype.size(), btype.size())), a << b, self.get_poison(btype)))

    def lshr(self, ctx, return_type, a, atype, b, btype, nuw=False, nsw=False):
        assert atype == return_type
        assert atype == btype
        assert not nuw and not nsw
        return util.partial_eval(ctx,
                util.If(z3.ULT(b, z3.BitVecVal(btype.size(), btype.size())), z3.LShR(a, b), self.get_poison(btype)))

    def ashr(self, ctx, return_type, a, atype, b, btype, nuw=False, nsw=False):
        assert atype == return_type
        assert atype == btype
        assert not nuw and not nsw
        return util.partial_eval(ctx,
                util.If(z3.ULT(b, z3.BitVecVal(btype.size(), btype.size())), a >> b, self.get_poison(btype)))

    def and_(self, ctx, return_type, a, atype, b, btype):
        assert atype == return_type
        assert atype == btype

        if z3.is_bool(a) or z3.is_bool(b):
            a = util.as_bool(a)
            b = util.as_bool(b)
            assert return_type.size() == 1
            return z3.And(a, b)
        else:
            return a & b

    def or_(self, ctx, return_type, a, atype, b, btype):
        assert atype == return_type
        assert atype == btype

        if z3.is_bool(a) or z3.is_bool(b):
            a = util.as_bool(a)
            b = util.as_bool(b)
            assert return_type.size() == 1
            return z3.Or(a, b)
        else:
            return a | b

    def xor(self, ctx, return_type, a, atype, b, btype):
        assert atype == return_type
        assert atype == btype

        if z3.is_bool(a) or z3.is_bool(b):
            a = util.as_bool(a)
            b = util.as_bool(b)
            assert return_type.size() == 1
            return z3.Xor(a, b)
        else:
            return a ^ b

    #############################
    # Cast Ops
    #############################
    def trunc(self, ctx, return_type, a, atype, **kwargs):
        outsize = itypes.integer_size(return_type)
        insize = itypes.integer_size(atype)
        assert insize > outsize
        return z3.Extract(outsize - 1, 0, a)

    def zext(self, ctx, return_type, a, atype, **kwargs):
        outsize = itypes.integer_size(return_type)
        insize = itypes.integer_size(atype)
        assert outsize > insize
        if z3.is_bool(a):
            return util.If(a, z3.BitVecVal(1, outsize), z3.BitVecVal(0, outsize))
        return z3.ZeroExt(outsize - insize, a)

    def sext(self, ctx, return_type, a, atype, **kwargs):
        outsize = itypes.integer_size(return_type)
        insize = itypes.integer_size(atype)
        assert outsize > insize
        if z3.is_bool(a):
            return util.If(a, z3.BitVecVal(1, outsize), z3.BitVecVal(0, outsize))
        return z3.SignExt(outsize - insize, a)

    #############################
    # Predicates
    #############################
    def eq(self, ctx, return_type, a, atype, b, btype, **kwargs):
        assert atype == btype
        return a == b

    def ne(self, ctx, return_type, a, atype, b, btype, **kwargs):
        assert atype == btype
        return a != b

    def ugt(self, ctx, return_type, a, atype, b, btype, **kwargs):
        assert atype == btype
        return z3.UGT(a, b)

    def uge(self, ctx, return_type, a, atype, b, btype, **kwargs):
        assert atype == btype
        return z3.UGE(a, b)

    def ult(self, ctx, return_type, a, atype, b, btype, **kwargs):
        assert atype == btype
        return z3.ULT(a, b)

    def ule(self, ctx, return_type, a, atype, b, btype, **kwargs):
        assert atype == btype
        return z3.ULE(a, b)

    def sgt(self, ctx, return_type, a, atype, b, btype, **kwargs):
        assert atype == btype
        return a > b

    def sge(self, ctx, return_type, a, atype, b, btype, **kwargs):
        assert atype == btype
        return a >= b

    def slt(self, ctx, return_type, a, atype, b, btype, **kwargs):
        assert atype == btype
        return a < b

    def sle(self, ctx, return_type, a, atype, b, btype, **kwargs):
        assert atype == btype
        return a < b

    #############################
    # Other Ops
    #############################
    def constant_int(self, ctx, value, size):
        if size == 1:
            return z3.BoolVal(True if value == 1 else False)
        return z3.BitVecVal(value, size)

    def constant_data(self, ctx, value, size):
        return value

    def constant_data_array(self, ctx, return_type, values):
        return values

    def constant_array(self, ctx, value, size):
        return value

    def constant_aggregate_zero(self, ctx, type, value):
        return value

    def symbolic_aggregate(self, ctx, type, value):
        return value

    def constant_pointer_null(self, ctx, type):
        pass


class Z3IRPyEval(BaseZ3IRPyEval):
    #############################
    # Memory Ops
    #############################
    def alloca(self, ctx, return_type, size, size_type, **kwargs):
        assert return_type.is_pointer()
        return dt.fresh_ptr(ctx, util.fresh_name('alloca'), return_type)

    def load(self, ctx, return_type, target, target_type, **kwargs):
        assert return_type == target_type.deref()
        return target.read(ctx)

    def store(self, ctx, return_type, target, target_type, dest, dest_type, **kwargs):
        assert dest_type.deref() == target_type
        dest.write(ctx, target)
        assert return_type == itypes.VoidType()

    def get_element_ptr(self, ctx, return_type, target, target_type, *args, **kwargs):
        return target.getelementptr(ctx, *list(args)[::2], type=return_type)
    getelementptr = get_element_ptr

    #############################
    # Cast Ops
    #############################
    def ptr_to_int(self, ctx, return_type, value, value_type, **kwargs):
        assert value_type.is_pointer()
        if isinstance(value, dt.BitcastPointer):
            assert not value._geps
            value = value._ptr
        path = value.canonical_path()
        assert len(path) <= 2
        base = ctx.ptr_to_int[value._ref._name]
        if len(path) == 2:
            return base + path[-1] * value_type.deref().size() / 8
        else:
            return base
    ptrtoint = ptr_to_int

    def int_to_ptr(self, *args, **kwargs):
        raise NotImplementedError()
    inttoptr = int_to_ptr

    def bitcast(self, ctx, return_type, value, value_type, **kwargs):
        assert return_type.is_pointer()
        assert value_type.is_pointer()
        assert isinstance(value, dt.Pointer)
        return value.bitcast(return_type)

    #############################
    # Other Ops
    #############################
    def declare_global_variable(self, ctx, name, global_type, value=None, value_type=None):
        def unknown_function(*args, **kwargs):
            assert False, "Calling unknown function {}".format(name)
        unknown_function.read = lambda *args, **kwargs: unknown_function
        if global_type.deref(True).is_function():
            ctx['globals'][name] = unknown_function
        else:
            ctx['globals'][name] = dt.fresh_ptr(ctx, name, global_type)

    def declare_global_constant(self, ctx, name, global_type, value=None, value_type=None):
        ctx['globals'][name] = dt.fresh_ptr(ctx, name, global_type)
        if value_type.is_array() and value_type.deref().is_int():
            inner_size = value_type.deref().size()
            for n, i in enumerate(util.parse_constant_array(value)):
                ctx['globals'][name].getelementptr(ctx, util.i64(
                    0), util.i64(n)).write(ctx, z3.BitVecVal(i, inner_size))

    def call(self, ctx, return_type, *args, **kwargs):
        args = list(args)

        fn_type = args.pop()
        assert fn_type.deref().return_type(
        ) == return_type, "{!r} != {!r}".format(fn_type, return_type)

        fn = args.pop()
        fargs = []
        for i in range(0, len(args), 2):
            assert itypes.has_type(
                ctx, args[i], args[i + 1]), "{!r} vs {!r}".format(args[i], args[i + 1])
            fargs.append(args[i])

        try:
            ctx['locals'].append({})
            ctx['stacktrace'].append({})
            return fn(ctx, *fargs)
        finally:
            ctx['locals'].pop()
            ctx['stacktrace'].pop()

    def select(self, ctx, return_type, cond, cond_type, trueval, trueval_type, falseval, falseval_type):
        self.assertion(ctx, not cond.is_poison(), "path condition is poison")
        assert itypes.integer_size(cond_type) == 1
        assert return_type == trueval_type
        assert trueval_type == falseval_type
        return util.If(cond, trueval, falseval)

    def branch(self, ctx, cond, cond_type, iftrue, iffalse):
        self.assertion(ctx, not cond.is_poison(), "path condition is poison")
        assert itypes.integer_size(cond_type) == 1

        scond = util.simplify(cond)

        can_be_true = not z3.is_false(scond)
        can_be_false = not z3.is_true(scond)

        if ctx['depth'] >= ctx['prune_depth']:
            can_be_true = not z3.is_false(
                scond) and not util.path_condition_implies(ctx, z3.Not(scond))
            can_be_false = not can_be_true or (not z3.is_true(
                scond) and not util.path_condition_implies(ctx, scond))

        true_branch_exc = None
        false_branch_exc = None

        trueval = None
        falseval = None

        if can_be_true:
            try:
                ctx.push(path_condition=scond)
                trueval = iftrue()
            except ex.UnreachableException, e:
                stacktrace = getattr(e, 'stacktrace', None)
                self.assertion(ctx, util.path_condition_implies(ctx, z3.BoolVal(
                    False), print_model=True), "Panic " + repr(e), stacktrace=stacktrace)
                can_be_true = False
            except BaseException, e:
                true_branch_exc = e
            finally:
                true_ctx = ctx.pop()

        if can_be_false:
            try:
                ctx.push(path_condition=z3.Not(scond))
                falseval = iffalse()
            except ex.UnreachableException, e:
                stacktrace = getattr(e, 'stacktrace', None)
                self.assertion(ctx, util.path_condition_implies(ctx, z3.BoolVal(
                    False), print_model=True), "Panic " + repr(e), stacktrace=stacktrace)
                can_be_false = False
            except BaseException, e:
                false_branch_exc = e
            finally:
                false_ctx = ctx.pop()

        if not can_be_false and not can_be_true:
            raise ex.UnreachableException('Branch unreachable', cond)

        if not can_be_false:
            ctx.restore(true_ctx)
            if true_branch_exc is not None:
                raise true_branch_exc
            return trueval
        elif not can_be_true:
            ctx.restore(false_ctx)
            if false_branch_exc is not None:
                raise false_branch_exc
            return falseval

        ctx.merge(scond, true_ctx, false_ctx)

        if true_branch_exc is not None:
            raise true_branch_exc
        elif false_branch_exc is not None:
            raise false_branch_exc

        if trueval is None:
            assert falseval is None, "Neither or both should be None: {!r} v {!r}".format(trueval, falseval)
            return
        else:
            return util.If(cond, trueval, falseval)

    def switch(self, ctx, value, value_type, default_case, *cases):
        if not cases:
            return default_case()

        case_value, case_value_type, case_branch = cases[0]
        cases = cases[1:]

        assert value_type == case_value_type

        def rest(): return self.switch(ctx, value, value_type, default_case, *cases)

        return self.branch(ctx, value == case_value, itypes.IntType(1), case_branch, rest)

    def undef(self, ctx, type):
        return self.get_poison(type)

    def unreachable(self, ctx, *args, **kwargs):
        raise ex.UnreachableException(ctx.path_condition[-1])

    def global_value(self, ctx, return_type, name):
        return ctx['globals'][name]

    def debug_loc(self, ctx, name, dbg):
        file, line, column, inlined = util.parse_debug_info(dbg)
        # Shouldn't change within a function, but inlining and stuff maybe
        ctx['stacktrace'][-1]['file'] = file
        ctx['stacktrace'][-1]['line'] = line
        ctx['stacktrace'][-1]['column'] = column
        ctx['stacktrace'][-1]['inlined'] = inlined
        if name in ctx['locals'][-1]:
            ctx['locals'][-1][name]._dbg = ctx['stacktrace'][-1]

    def declare_metadata(self, ctx, identifier, metadata):
        ctx['metadata'][identifier] = util.parse_metadata(metadata)

    def asm(self, ctx, inline_assembly):
        raise NotImplementedError()
