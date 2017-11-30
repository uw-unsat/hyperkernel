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
from libirpy import util
from libirpy import solver
import hv6py.kernel.spec.datatypes as dt

from helpers import (
        is_fd_valid,
        is_fn_valid,
        is_pid_bounded,
        is_pid_valid,
        is_pn_valid,
        is_status_live,
        pn_has_owner_and_type,
)


__all__ = ['impl_invariants_c', 'impl_invariants_py', 'impl_invariants', 'spec_invariants']


def impl_invariants_c(ctx):
    conj = []

    pid = util.FreshBitVec('pid', dt.pid_t)
    pn = util.FreshBitVec('pn', dt.pn_t)
    fd = util.FreshBitVec('fd', dt.fd_t)

    try:
        old_solver = ctx.solver
        old_globals = ctx.globals

        def implies(ctx, a, b):
            return z3.Implies(a, b)

        def and_(ctx, *args):
            return z3.And(*args)

        def or_(ctx, *args):
            return z3.Or(*args)

        ctx.globals['@implies'] = implies
        ctx.globals['@and2'] = and_
        ctx.globals['@and3'] = and_
        ctx.globals['@and4'] = and_
        ctx.globals['@and5'] = and_
        ctx.globals['@and6'] = and_
        ctx.globals['@and7'] = and_
        ctx.globals['@and8'] = and_
        ctx.globals['@and9'] = and_
        ctx.globals['@or2'] = or_
        ctx.globals['@or3'] = or_
        ctx.globals['@or4'] = or_

        ctx.solver = solver.Solver()
        ctx.solver.add(z3.BoolVal(False))

        conj.append(z3.ForAll([pid], ctx.call('@inv_proc_owns_pns', pid)))
        conj.append(z3.ForAll([pid], ctx.call(
            '@inv_sleeping_proc_owns_ipc', pid)))
        conj.append(z3.ForAll([pid], ctx.call(
            '@inv_sleeping_proc_ipc_fd_valid_empty', pid)))
        conj.append(z3.ForAll([pid], ctx.call('@inv_proc_pns_valid', pid)))
        conj.append(z3.ForAll([pid], ctx.call('@inv_io_bitmap', pid)))
        conj.append(z3.ForAll([pn], ctx.call('@inv_page_owner', pn)))
        conj.append(z3.ForAll([pn], ctx.call('@inv_proc_unused_refs', pn)))
        conj.append(z3.ForAll([pid, fd], ctx.call( '@inv_proc_fds_valid', pid, fd)))
        conj.append(z3.ForAll([pn], ctx.call('@inv_page_freelist_valid', pn)))
        conj.append(z3.ForAll([pid], ctx.call('@inv_proc_freelist_valid', pid)))
        conj.append(ctx.call('@inv_current_valid'))
        conj.append(ctx.call('@inv_current_running'))

    finally:
        ctx.solver = old_solver
        ctx.globals = old_globals

    return z3.And(*conj)


def impl_invariants_py(ctx):
    conj = []

    pid = util.FreshBitVec('pid', dt.pid_t)
    pn = util.FreshBitVec('pn', dt.pn_t)
    fd = util.FreshBitVec('fd', dt.fd_t)
    # fn = util.FreshBitVec('fn', dt.fn_t)

    # embryos, runnable or running processes own the pages in their structs
    conj.append(z3.ForAll([pid], z3.Implies(
        z3.Or(util.global_field_element(ctx, '@proc_table', 'state', pid) == dt.proc_state.PROC_EMBRYO,
              util.global_field_element(
                  ctx, '@proc_table', 'state', pid) == dt.proc_state.PROC_RUNNING,
              util.global_field_element(
                  ctx, '@proc_table', 'state', pid) == dt.proc_state.PROC_RUNNABLE,
              util.global_field_element(ctx, '@proc_table', 'state', pid) == dt.proc_state.PROC_SLEEPING),
        z3.And(
            pn_has_owner_and_type(ctx, util.global_field_element(
                ctx, '@proc_table', 'page_table_root', pid), pid, dt.page_type.PAGE_TYPE_X86_PML4),
            pn_has_owner_and_type(ctx, util.global_field_element(
                ctx, '@proc_table', 'hvm', pid), pid, dt.page_type.PAGE_TYPE_PROC_DATA),
            pn_has_owner_and_type(ctx, util.global_field_element(
                ctx, '@proc_table', 'stack', pid), pid, dt.page_type.PAGE_TYPE_PROC_DATA),
        ))))

    # sleeping processes own their ipc_page
    conj.append(z3.ForAll([pid], z3.Implies(z3.And(is_pid_valid(pid),
        util.global_field_element(ctx, '@proc_table', 'state', pid) != dt.proc_state.PROC_ZOMBIE),
        z3.Implies(util.global_field_element(ctx, '@proc_table', 'use_io_bitmap', pid) != 0,
            z3.And(
                is_pn_valid(util.global_field_element(ctx, '@proc_table', 'io_bitmap_a', pid)),
                is_pn_valid(util.global_field_element(ctx, '@proc_table', 'io_bitmap_b', pid)),
                pn_has_owner_and_type(ctx, util.global_field_element(ctx, '@proc_table', 'io_bitmap_a', pid), pid, dt.page_type.PAGE_TYPE_PROC_DATA),
                pn_has_owner_and_type(ctx, util.global_field_element(ctx, '@proc_table', 'io_bitmap_b', pid), pid, dt.page_type.PAGE_TYPE_PROC_DATA))))))

    # sleeping processes own their ipc_page
    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        z3.Implies(util.global_field_element(ctx, '@proc_table', 'state', pid) == dt.proc_state.PROC_SLEEPING,
            pn_has_owner_and_type(ctx, util.global_field_element(ctx, '@proc_table', 'ipc_page', pid), pid, dt.page_type.PAGE_TYPE_FRAME)))))

    conj.append(z3.ForAll([pid],
                          z3.And(
        is_pn_valid(util.global_field_element(
                ctx, '@proc_table', 'page_table_root', pid)),
        is_pn_valid(util.global_field_element(
            ctx, '@proc_table', 'hvm', pid)),
        is_pn_valid(util.global_field_element(ctx, '@proc_table', 'stack', pid)))))

    # sleeping processes' ipc fd are empty if valid
    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        z3.Implies(util.global_field_element(ctx, '@proc_table', 'state', pid) == dt.proc_state.PROC_SLEEPING,
            z3.Implies(is_fd_valid(util.global_field_element(ctx, '@proc_table', 'ipc_fd', pid)),
                util.global_field_element(ctx, '@proc_table', 'ofile', pid,
                    z3.ZeroExt(32, util.global_field_element(ctx, '@proc_table', 'ipc_fd', pid))) == z3.BitVecVal(0, dt.fn_t))))))

    conj.append(z3.ForAll([pid],
                          z3.And(
        is_pn_valid(util.global_field_element(
                ctx, '@proc_table', 'page_table_root', pid)),
        is_pn_valid(util.global_field_element(
            ctx, '@proc_table', 'hvm', pid)),
        is_pn_valid(util.global_field_element(ctx, '@proc_table', 'stack', pid)))))

    # page has an owner <=> page is not free
    conj.append(z3.ForAll([pn], z3.Implies(is_pn_valid(pn),
        is_pid_valid(util.global_field_element(ctx, '@page_desc_table', 'pid', pn)) ==
        (util.global_field_element(ctx, '@page_desc_table', 'type', pn) != dt.page_type.PAGE_TYPE_FREE))))

    # unused procs have zero refcnt
    conj.append(z3.ForAll([pid], z3.Implies(
        z3.And(
            is_pid_valid(pid),
            util.global_field_element(ctx, '@proc_table', 'state', pid) == dt.proc_state.PROC_UNUSED),
        z3.And(
            util.global_field_element(ctx, '@proc_table', 'nr_children', pid) == z3.BitVecVal(0, dt.size_t),
            util.global_field_element(ctx, '@proc_table', 'nr_fds', pid) == z3.BitVecVal(0, dt.size_t),
            util.global_field_element(ctx, '@proc_table', 'nr_pages', pid) == z3.BitVecVal(0, dt.size_t),
            util.global_field_element(ctx, '@proc_table', 'nr_dmapages', pid) == z3.BitVecVal(0, dt.size_t),
            util.global_field_element(ctx, '@proc_table', 'nr_devs', pid) == z3.BitVecVal(0, dt.size_t),
            util.global_field_element(ctx, '@proc_table', 'nr_ports', pid) == z3.BitVecVal(0, dt.size_t),
            util.global_field_element(ctx, '@proc_table', 'nr_vectors', pid) == z3.BitVecVal(0, dt.size_t),
            util.global_field_element(ctx, '@proc_table', 'nr_intremaps', pid) == z3.BitVecVal(0, dt.size_t)))))

    # conj.append(z3.ForAll([pid, fd], z3.Implies(z3.And(is_pid_valid(pid), is_fd_valid(fd)),
    #     z3.Implies(
    #         util.global_field_element(ctx, '@proc_table', 'nr_fds', pid) == z3.BitVecVal(0, dt.size_t),
    #         z3.Not(is_fn_valid(util.global_field_element(ctx, '@proc_table', 'ofile', pid, z3.ZeroExt(32, fd))))))))

    # # unused procs have zero fds
    # conj.append(z3.ForAll([pid, fd], z3.Implies(z3.And(is_pid_valid(pid), is_fd_valid(fd)),
    #     z3.Implies(
    #         util.global_field_element(ctx, '@proc_table', 'state', pid) == dt.proc_state.PROC_UNUSED,
    #         util.global_field_element(ctx, '@proc_table', 'ofile', pid, z3.ZeroExt(32, fd)) == z3.BitVecVal(0, dt.fn_t)))))

    # fds valid
    conj.append(z3.ForAll([pid, fd], z3.Implies(z3.And(is_pid_valid(pid), is_fd_valid(fd)),
        z3.Or(
            util.global_field_element(ctx, '@proc_table', 'ofile', pid, z3.ZeroExt(32, fd)) == z3.BitVecVal(0, dt.fn_t),
            is_fn_valid(util.global_field_element(ctx, '@proc_table', 'ofile', pid, z3.ZeroExt(32, fd)))))))

    # # FD_NONE's refcount is 0
    # conj.append(z3.ForAll([fn], z3.Implies(
    #     z3.And(
    #         is_fn_valid(fn),
    #         util.global_field_element(ctx, '@file_table', 'type', fn) == dt.file_type.FD_NONE),
    #     util.global_field_element(ctx, '@file_table', 'refcnt', fn) == z3.BitVecVal(0, dt.size_t))))

    # # FD never points to FD_NONE
    # conj.append(z3.ForAll([pid, fd], z3.Implies(
    #     z3.And(
    #         is_pid_valid(pid),
    #         is_fd_valid(fd),
    #         is_fn_valid(util.global_field_element(ctx, '@proc_table', 'ofile', pid, z3.ZeroExt(32, fd)))),
    #     util.global_field_element(ctx, '@file_table', 'type',
    #         util.global_field_element(ctx, '@proc_table', 'ofile', pid, z3.ZeroExt(32, fd))) != dt.file_type.FD_NONE)))

    # page freelist is well formed
    conj.append(z3.ForAll([pn], z3.Implies(is_pn_valid(pn),
        z3.And(
            is_pn_valid(util.global_field_element(ctx, '@page_desc_table', ['link', 'prev'], pn)),
            is_pn_valid(util.global_field_element(ctx, '@page_desc_table', ['link', 'next'], pn))))))

    # ready queue is well formed
    # don't use is_pid_valid as some ->prev and ->next are zeros
    conj.append(z3.ForAll([pid], z3.Implies(is_pid_bounded(pid),
        z3.And(
            is_pid_bounded(util.global_field_element(ctx, '@proc_table', ['ready', 'prev'], pid)),
            is_pid_bounded(util.global_field_element(ctx, '@proc_table', ['ready', 'next'], pid))))))

    # Current is always a valid and running
    conj.append(is_pid_valid(util.global_value(ctx, '@current')))

    conj.append(util.global_field_element(ctx, '@proc_table', 'state', util.global_value(ctx, '@current')) == dt.proc_state.PROC_RUNNING)

    return z3.And(*conj)


impl_invariants = impl_invariants_py


# Generic invariants
def spec_invariants(kernelstate):
    conj = []

    pid = util.FreshBitVec('pid', dt.pid_t)
    pn = util.FreshBitVec('pn', dt.pn_t)

    #
    # procs' page table, hvm and stack are
    #
    # 1) valid
    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        z3.And(
            is_pn_valid(kernelstate.procs[pid].page_table_root),
            is_pn_valid(kernelstate.procs[pid].hvm),
            is_pn_valid(kernelstate.procs[pid].stack)))))
    # 2) owned by that proc
    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        z3.Implies(
            is_status_live(kernelstate.procs[pid].state),
            z3.And(
                kernelstate.pages[kernelstate.procs[pid].page_table_root].owner == pid,
                kernelstate.pages[kernelstate.procs[pid].hvm].owner == pid,
                kernelstate.pages[kernelstate.procs[pid].stack].owner == pid)))))

    # 3) have the correct type
    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        z3.Implies(
            is_status_live(kernelstate.procs[pid].state),
            z3.And(
                kernelstate.pages[kernelstate.procs[pid].page_table_root].type == dt.page_type.PAGE_TYPE_X86_PML4,
                kernelstate.pages[kernelstate.procs[pid].hvm].type == dt.page_type.PAGE_TYPE_PROC_DATA,
                kernelstate.pages[kernelstate.procs[pid].stack].type == dt.page_type.PAGE_TYPE_PROC_DATA)))))

    ##

    # Sleeping PROC's ipc_page is a frame owned by that pid
    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        z3.Implies(
            kernelstate.procs[pid].state == dt.proc_state.PROC_SLEEPING,
            z3.And(
                is_pn_valid(kernelstate.procs[pid].ipc_page),
                kernelstate.pages[kernelstate.procs[pid]
                    .ipc_page].type == dt.page_type.PAGE_TYPE_FRAME,
                kernelstate.pages[kernelstate.procs[pid].ipc_page].owner == pid)))))

    ## Non-zombie procs with use_io_bitmaps own their (valid) bitmap pages
    conj.append(z3.ForAll([pid],
        z3.Implies(
            z3.And(
                is_pid_valid(pid),
                kernelstate.procs[pid].use_io_bitmap,
                kernelstate.procs[pid].state != dt.proc_state.PROC_ZOMBIE),
            z3.And(
                is_pn_valid(kernelstate.procs[pid].io_bitmap_a),
                is_pn_valid(kernelstate.procs[pid].io_bitmap_b),
                kernelstate.pages[kernelstate.procs[pid].io_bitmap_a].owner == pid,
                kernelstate.pages[kernelstate.procs[pid].io_bitmap_b].owner == pid,
                kernelstate.pages[kernelstate.procs[pid].io_bitmap_a].type == dt.page_type.PAGE_TYPE_PROC_DATA,
                kernelstate.pages[kernelstate.procs[pid].io_bitmap_b].type == dt.page_type.PAGE_TYPE_PROC_DATA))))

    # page has an owner <=> page is not free
    conj.append(z3.ForAll([pn], z3.Implies(is_pn_valid(pn),
        is_pid_valid(kernelstate.pages[pn].owner) == (kernelstate.pages[pn].type != dt.page_type.PAGE_TYPE_FREE))))

    conj.append(z3.ForAll([pn], z3.Implies(is_pn_valid(pn),
        z3.Implies(kernelstate.pages[pn].type == dt.page_type.PAGE_TYPE_FREE,
            z3.Not(is_pid_valid(kernelstate.pages[pn].owner))))))

    # a sleeping proc's ipc_fd is either invalid or empty
    conj.append(z3.ForAll([pid], z3.Implies(z3.And(
        is_pid_valid(pid),
        kernelstate.procs[pid].state == dt.proc_state.PROC_SLEEPING),

        z3.Or(z3.Not(is_fd_valid(kernelstate.procs[pid].ipc_fd)),
              z3.Not(is_fn_valid(kernelstate.procs[pid].ofile(kernelstate.procs[pid].ipc_fd)))))))

    ##############
    # Unused procs's refcount is all zero
    # conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
    #     z3.Implies(kernelstate.procs[pid].state == dt.proc_state.PROC_UNUSED,
    #         z3.And(
    # kernelstate.procs[pid].nr_pages(dt.NPAGE - 1) == z3.BitVecVal(0, dt.size_t))))))
    # kernelstate.procs[pid].nr_children(dt.NPROC - 1) == z3.BitVecVal(0, dt.size_t),
    # kernelstate.procs[pid].nr_fds(dt.NOFILE - 1) == z3.BitVecVal(0, dt.size_t),
    # kernelstate.procs[pid].nr_devs(dt.NPCIDEV - 1) == z3.BitVecVal(0, dt.size_t))))))

    # # unused procs don't have a parent
    # conj.append(z3.ForAll([pid], z3.Implies(
    #     z3.And(
    #         is_pid_valid(pid),
    #         kernelstate.procs[pid].state == dt.proc_state.PROC_UNUSED),
    #     kernelstate.procs[pid].ppid == z3.BitVecVal(0, dt.pid_t))))

    # # unused procs don't have fds
    # conj.append(z3.ForAll([pid, fd], z3.Implies(
    #     z3.And(
    #         is_pid_valid(pid),
    #         kernelstate.procs[pid].state == dt.proc_state.PROC_UNUSED),
    #     z3.Not(is_fn_valid(kernelstate.procs[pid].ofile(fd))))))

    # unused fn has refcount == 0
    # conj.append(z3.ForAll([fn], z3.Implies(is_fn_valid(fn),
    #     z3.Implies(kernelstate.files[fn].type == dt.file_type.FD_NONE,
    #         kernelstate.files[fn].refcnt(
    #             z3.Concat(
    #                 z3.BitVecVal(dt.NPROC - 1, dt.pid_t),
    #                 z3.BitVecVal(dt.NOFILE - 1, dt.fd_t))) == z3.BitVecVal(0, dt.size_t)))))

    ##############

    # disjointed-ness of memory regions
    conj.append(z3.And(
        z3.Extract(63, 40, z3.UDiv(kernelstate.pages_ptr_to_int, util.i64(4096)) + dt.NPAGES_PAGES) == z3.BitVecVal(0, 24),
        z3.Extract(63, 40, z3.UDiv(kernelstate.proc_table_ptr_to_int, util.i64(4096)) + dt.NPAGES_PROC_TABLE) == z3.BitVecVal(0, 24),
        z3.Extract(63, 40, z3.UDiv(kernelstate.page_desc_table_ptr_to_int, util.i64(4096)) + dt.NPAGES_PAGE_DESC_TABLE) == z3.BitVecVal(0, 24),
        z3.Extract(63, 40, z3.UDiv(kernelstate.file_table_ptr_to_int, util.i64(4096)) + dt.NPAGES_FILE_TABLE) == z3.BitVecVal(0, 24),
        z3.Extract(63, 40, z3.UDiv(kernelstate.devices_ptr_to_int,util.i64(4096)) + dt.NPAGES_DEVICES) == z3.BitVecVal(0, 24),
        z3.Extract(63, 40, z3.UDiv(kernelstate.dmapages_ptr_to_int,util.i64(4096)) + dt.NDMAPAGE) == z3.BitVecVal(0, 24),

        z3.Extract(63, 40, z3.UDiv(kernelstate.pages_ptr_to_int, util.i64(4096))) == z3.BitVecVal(0, 24),
        z3.Extract(63, 40, z3.UDiv(kernelstate.proc_table_ptr_to_int, util.i64(4096))) == z3.BitVecVal(0, 24),
        z3.Extract(63, 40, z3.UDiv(kernelstate.page_desc_table_ptr_to_int, util.i64(4096))) == z3.BitVecVal(0, 24),
        z3.Extract(63, 40, z3.UDiv(kernelstate.file_table_ptr_to_int, util.i64(4096))) == z3.BitVecVal(0, 24),
        z3.Extract(63, 40, z3.UDiv(kernelstate.devices_ptr_to_int, util.i64(4096))) == z3.BitVecVal(0, 24),
        z3.Extract(63, 40, z3.UDiv(kernelstate.dmapages_ptr_to_int, util.i64(4096))) == z3.BitVecVal(0, 24),

        z3.ULT(z3.UDiv(kernelstate.pages_ptr_to_int, util.i64(4096)) + dt.NPAGES_PAGES, z3.UDiv(kernelstate.proc_table_ptr_to_int, util.i64(4096))),
        z3.ULT(z3.UDiv(kernelstate.proc_table_ptr_to_int, util.i64(4096)) + dt.NPAGES_PROC_TABLE, z3.UDiv(kernelstate.page_desc_table_ptr_to_int, util.i64(4096))),
        z3.ULT(z3.UDiv(kernelstate.page_desc_table_ptr_to_int, util.i64(4096)) + dt.NPAGES_PAGE_DESC_TABLE, z3.UDiv(kernelstate.file_table_ptr_to_int, util.i64(4096))),
        z3.ULT(z3.UDiv(kernelstate.file_table_ptr_to_int, util.i64(4096)) + dt.NPAGES_FILE_TABLE, z3.UDiv(kernelstate.devices_ptr_to_int, util.i64(4096))),
        z3.ULT(z3.UDiv(kernelstate.devices_ptr_to_int, util.i64(4096)) + dt.NPCIDEV, z3.UDiv(kernelstate.dmapages_ptr_to_int, util.i64(4096))),
        z3.ULT(z3.UDiv(kernelstate.dmapages_ptr_to_int, util.i64(4096)) + dt.NDMAPAGE, z3.UDiv(dt.PCI_START, util.i64(4096))),
    ))

    # Current is a valid pid
    conj.append(is_pid_valid(kernelstate.current))
    # Current is always running
    conj.append(kernelstate.procs[kernelstate.current].state == dt.proc_state.PROC_RUNNING),
    # A running proc must be current
    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        z3.Implies(kernelstate.procs[pid].state == dt.proc_state.PROC_RUNNING,
            pid == kernelstate.current))))

    return z3.And(*conj)
