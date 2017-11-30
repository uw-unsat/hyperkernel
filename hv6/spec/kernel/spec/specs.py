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
import hv6py.kernel.spec.datatypes as dt

from helpers import (
        is_dmapn_valid,
        is_fd_valid,
        is_fn_valid,
        is_intremap_valid,
        is_pcipn_valid,
        is_pid_valid,
        is_pn_valid,
)


def sys_set_runnable(old, pid):
    cond = z3.And(
        is_pid_valid(pid),
        old.procs[pid].ppid == old.current,
        old.procs[pid].state == dt.proc_state.PROC_EMBRYO)

    new = old.copy()
    new.procs[pid].state = dt.proc_state.PROC_RUNNABLE
    return cond, util.If(cond, new, old)


def sys_reclaim_page(old, pn):
    cond = z3.And(
        is_pn_valid(pn),
        old.pages[pn].type != dt.page_type.PAGE_TYPE_FREE,
        is_pid_valid(old.pages[pn].owner),
        old.procs[old.pages[pn].owner].state == dt.proc_state.PROC_ZOMBIE,
        old.procs[old.pages[pn].owner].nr_devs() == z3.BitVecVal(0, dt.size_t),
    )

    new = old.copy()

    new.procs[new.pages[pn].owner].nr_pages[pn] -= 1
    new.pages[pn].type = dt.page_type.PAGE_TYPE_FREE
    new.pages[pn].owner = z3.BitVecVal(0, dt.pid_t)

    return cond, util.If(cond, new, old)


def alloc_page_table(old, pid, frm, index, to, perm, from_type, to_type):
    cond = z3.And(
        # The to argument is a valid page and is marked as free
        is_pn_valid(to),
        old.pages[to].type == dt.page_type.PAGE_TYPE_FREE,

        # The pid is valid and is either current running process or child embryo
        is_pid_valid(pid),
        z3.Or(pid == old.current,
              z3.And(
                  old.procs[pid].ppid == old.current,
                  old.procs[pid].state == dt.proc_state.PROC_EMBRYO)),

        # The from parameter is valid and of type PML4 and owned by pid
        is_pn_valid(frm),
        old.pages[frm].owner == pid,
        old.pages[frm].type == from_type,

        # Index is a valid page index
        z3.ULT(index, 512),

        # perm has no unsafe bits on it and it is present
        perm & (dt.MAX_INT64 ^ dt.PTE_PERM_MASK) == 0,
        perm & dt.PTE_P != 0,

        # index does not have the P bit in PML4
        old.pages[frm].data(index) & dt.PTE_P == 0,
    )

    new = old.copy()

    new.pages[to].owner = pid
    new.pages[to].type = to_type

    new.pages[frm].data[index] = (
        (z3.UDiv(new.pages_ptr_to_int, util.i64(dt.PAGE_SIZE)) + to) << dt.PTE_PFN_SHIFT) | perm

    # Zero out the new page
    new.pages[to].data = util.i64(0)

    # Maintain the "shadow" pgtable
    new.pages[frm].pgtable_pn[index] = to
    new.pages[to].pgtable_reverse_pn = frm
    new.pages[to].pgtable_reverse_idx = index

    new.pages[frm].pgtable_perm[index] = perm
    new.pages[frm].pgtable_type[index] = dt.PGTYPE_PAGE

    new.pages[to].pgtable_pn = util.i64(0)
    new.pages[to].pgtable_perm = util.i64(0)
    new.pages[to].pgtable_type = dt.PGTYPE_NONE

    new.procs[pid].nr_pages[to] += 1

    new.flush_tlb(pid)

    return cond, util.If(cond, new, old)


def sys_alloc_pdpt(old, pid, frm, index, to, perm):
    return alloc_page_table(old, pid, frm, index, to, perm,
                            dt.page_type.PAGE_TYPE_X86_PML4, dt.page_type.PAGE_TYPE_X86_PDPT)


def sys_alloc_pd(old, pid, frm, index, to, perm):
    return alloc_page_table(old, pid, frm, index, to, perm,
                            dt.page_type.PAGE_TYPE_X86_PDPT, dt.page_type.PAGE_TYPE_X86_PD)


def sys_alloc_pt(old, pid, frm, index, to, perm):
    return alloc_page_table(old, pid, frm, index, to, perm,
                            dt.page_type.PAGE_TYPE_X86_PD, dt.page_type.PAGE_TYPE_X86_PT)


def sys_alloc_frame(old, pid, frm, index, to, perm):
    return alloc_page_table(old, pid, frm, index, to, perm,
                            dt.page_type.PAGE_TYPE_X86_PT, dt.page_type.PAGE_TYPE_FRAME)


def sys_copy_frame(old, frm, pid, to):
    cond = z3.And(
        # frm is a valid FRAME owned by current
        is_pn_valid(frm),
        old.pages[frm].type == dt.page_type.PAGE_TYPE_FRAME,
        old.pages[frm].owner == old.current,

        # to is a valid frame owned by pid
        is_pid_valid(pid),
        is_pn_valid(to),
        old.pages[to].type == dt.page_type.PAGE_TYPE_FRAME,
        old.pages[to].owner == pid,

        # the pid is either current or an embryo belonging to current
        z3.Or(pid == old.current,
              z3.And(
                  old.procs[pid].ppid == old.current,
                  old.procs[pid].state == dt.proc_state.PROC_EMBRYO)),
    )

    new = old.copy()

    # copy contents of page frm to page to
    new.pages.data = lambda pn, idx, oldfn: \
        util.If(pn == to,
                oldfn(frm, idx),
                oldfn(pn, idx))

    return cond, util.If(cond, new, old)


def sys_protect_frame(old, pt, index, frame, perm):
    cond = z3.And(
        is_pn_valid(pt),
        old.pages[pt].type == dt.page_type.PAGE_TYPE_X86_PT,
        old.pages[pt].owner == old.current,

        # Index is a valid page index
        z3.ULT(index, 512),

        is_pn_valid(frame),
        old.pages[frame].type == dt.page_type.PAGE_TYPE_FRAME,
        old.pages[frame].owner == old.current,

        # index must be preset
        old.pages[pt].data(index) & dt.PTE_P != 0,

        # the entry in the pt must be the frame
        z3.Extract(63, 40, z3.UDiv(old.pages_ptr_to_int,
                                   util.i64(dt.PAGE_SIZE)) + frame) == z3.BitVecVal(0, 24),
        z3.Extract(39, 0, z3.UDiv(old.pages_ptr_to_int, util.i64(
            dt.PAGE_SIZE)) + frame) == z3.Extract(51, 12, old.pages[pt].data(index)),

        # no unsafe bits in perm is set
        perm & (dt.MAX_INT64 ^ dt.PTE_PERM_MASK) == 0,

        # P bit is set in perm
        perm & dt.PTE_P != 0
    )

    new = old.copy()

    new.pages[pt].data[index] = (
        (z3.UDiv(new.pages_ptr_to_int, util.i64(dt.PAGE_SIZE)) + frame) << dt.PTE_PFN_SHIFT) | perm

    # The only thing that changed is the permission.
    new.pages[pt].pgtable_perm[index] = perm

    new.flush_tlb(old.current)

    return cond, util.If(cond, new, old)


def sys_clone(old, pid, pml4, stack, hvm):
    cond = z3.And(
        is_pid_valid(pid),
        old.procs[pid].state == dt.proc_state.PROC_UNUSED,

        is_pn_valid(pml4),
        old.pages[pml4].type == dt.page_type.PAGE_TYPE_FREE,

        is_pn_valid(stack),
        old.pages[stack].type == dt.page_type.PAGE_TYPE_FREE,

        is_pn_valid(hvm),
        old.pages[hvm].type == dt.page_type.PAGE_TYPE_FREE,

        z3.Distinct(pml4, stack, hvm),
    )
    new = old.copy()

    # Initialize the proc
    new.procs[pid].ppid = new.current
    new.procs[pid].state = dt.proc_state.PROC_EMBRYO
    new.procs[pid].killed = z3.BoolVal(False)
    new.procs[pid].ipc_from = z3.BitVecVal(0, dt.pid_t)
    new.procs[pid].ipc_val = z3.BitVecVal(0, dt.uint64_t)
    new.procs[pid].ipc_page = z3.BitVecVal(0, dt.pn_t)
    new.procs[pid].ipc_size = z3.BitVecVal(0, dt.size_t)
    new.procs[pid].ipc_fd = z3.BitVecVal(0, dt.fd_t)
    new.procs[pid].use_io_bitmap = z3.BoolVal(False)
    new.procs[pid].io_bitmap_a = z3.BitVecVal(0, dt.pn_t)
    new.procs[pid].io_bitmap_b = z3.BitVecVal(0, dt.pn_t)

    # all refcnts should be zero at this point (according to invariants):
    # no need to zero them
    # new.proc_nr_pages = 0
    # new.proc_nr_children = 0
    # new.procs.nr_fds = 0
    # new.proc_nr_devs = 0

    new.procs[pid].ofile = z3.BitVecVal(0, dt.fn_t)
    new.procs[pid].intr = z3.BitVecVal(0, 64)

    # Maintain the "shadow" pgtable
    new.pages[pml4].pgtable_pn = util.i64(0)
    new.pages[pml4].pgtable_perm = util.i64(0)
    new.pages[pml4].pgtable_type = dt.PGTYPE_NONE

    # Claim the root pml4, the stack and hvm pages
    # We need to do four things to claim a page.
    # 1) Change the type from free to something else
    # 2) change the owner
    # 3) zero the page contents
    # 4) bump the refcount for the owner
    new.pages[pml4].type = dt.page_type.PAGE_TYPE_X86_PML4
    new.pages[pml4].owner = pid
    new.pages[pml4].data = util.i64(0)
    new.procs[pid].nr_pages[pml4] += 1

    new.pages[stack].type = dt.page_type.PAGE_TYPE_PROC_DATA
    new.pages[stack].owner = pid
    new.pages[stack].data = util.i64(0)
    new.procs[pid].nr_pages[stack] += 1

    new.pages[hvm].type = dt.page_type.PAGE_TYPE_PROC_DATA
    new.pages[hvm].owner = pid
    new.pages[hvm].data = util.i64(0)
    new.procs[pid].nr_pages[hvm] += 1

    new.procs[pid].page_table_root = pml4
    new.procs[pid].stack = stack
    new.procs[pid].hvm = hvm

    new.procs[new.current].nr_children[pid] += 1

    # Copy parent's hvm to child's hvm
    new.pages.data = lambda pn, idx, oldfn: \
        util.If(pn == hvm,
                oldfn(new.procs[new.current].hvm, idx),
                oldfn(pn, idx))

    # Copy parent's stack to child's stack
    new.pages.data = lambda pn, idx, oldfn: \
        util.If(pn == stack,
                oldfn(new.procs[new.current].stack, idx),
                oldfn(pn, idx))

    return cond, util.If(cond, new, old)


clone_proc = sys_clone


def sys_set_proc_name(old, name0, name1):
    # We don't model proc names.
    # The syscall should not change the state.
    return z3.BoolVal(True), old


def sys_reap(old, pid):
    cond = z3.And(
        is_pid_valid(pid),
        # Only the owner can reap a child
        old.procs[pid].ppid == old.current,

        # The pid to reap is a zombie
        old.procs[pid].state == dt.proc_state.PROC_ZOMBIE,

        # The proc has no children/open fds/pages/devices/ports
        old.procs[pid].nr_devs() == z3.BitVecVal(0, dt.size_t),
        old.procs[pid].nr_children() == z3.BitVecVal(0, dt.size_t),
        old.procs[pid].nr_fds() == z3.BitVecVal(0, dt.size_t),
        old.procs[pid].nr_pages() == z3.BitVecVal(0, dt.size_t),
        old.procs[pid].nr_dmapages() == z3.BitVecVal(0, dt.size_t),
        old.procs[pid].nr_ports() == z3.BitVecVal(0, dt.size_t),
        old.procs[pid].nr_vectors() == z3.BitVecVal(0, dt.size_t),
        old.procs[pid].nr_intremaps() == z3.BitVecVal(0, dt.size_t),
    )

    new = old.copy()

    new.procs[old.current].nr_children[pid] -= 1

    new.procs[pid].state = dt.proc_state.PROC_UNUSED
    new.procs[pid].ppid = z3.BitVecVal(0, dt.pid_t)
    new.procs[pid].page_table_root = z3.BitVecVal(0, dt.pn_t)
    new.procs[pid].stack = z3.BitVecVal(0, dt.pn_t)
    new.procs[pid].killed = z3.BoolVal(False)
    new.procs[pid].hvm = z3.BitVecVal(0, dt.pn_t)
    new.procs[pid].use_io_bitmap = z3.BoolVal(False)
    new.procs[pid].io_bitmap_a = z3.BitVecVal(0, dt.pn_t)
    new.procs[pid].io_bitmap_b = z3.BitVecVal(0, dt.pn_t)

    return cond, util.If(cond, new, old)


def sys_map_proc(old, pid, frm, index, n, perm):
    cond = z3.And(
        z3.ULT(n, dt.NPAGES_PROC_TABLE),

        is_pid_valid(pid),

        # the pid is either current or an embryo belonging to current
        z3.Or(pid == old.current,
              z3.And(
                  old.procs[pid].ppid == old.current,
                  old.procs[pid].state == dt.proc_state.PROC_EMBRYO)),

        # frm is a valid pn of type PT whose owner is pid
        is_pn_valid(frm),
        old.pages[frm].type == dt.page_type.PAGE_TYPE_X86_PT,
        old.pages[frm].owner == pid,

        # Index is a valid page index
        z3.ULT(index, 512),

        # perm has no unsafe bits on it and it is present and non-writable
        perm & (dt.MAX_INT64 ^ dt.PTE_PERM_MASK) == 0,
        perm & dt.PTE_P != 0,
        perm & dt.PTE_W == 0,

        # index does not have the P bit in the from page
        old.pages[frm].data(index) & dt.PTE_P == 0,
    )

    new = old.copy()

    new.pages[frm].data[index] = (
        (z3.UDiv(new.proc_table_ptr_to_int, util.i64(dt.PAGE_SIZE)) + n) << dt.PTE_PFN_SHIFT) | perm

    # maintain the "shadow" pgtable
    new.pages[frm].pgtable_pn[index] = n
    new.pages[frm].pgtable_perm[index] = perm
    new.pages[frm].pgtable_type[index] = dt.PGTYPE_PROC

    new.flush_tlb(pid)

    return cond, util.If(cond, new, old)


def sys_map_pml4(old, pid, index, perm):

    cond = z3.And(
        is_pid_valid(pid),

        # the pid is either current or an embryo belonging to current
        z3.Or(pid == old.current,
              z3.And(
                  old.procs[pid].ppid == old.current,
                  old.procs[pid].state == dt.proc_state.PROC_EMBRYO)),

        # Index is a valid page index
        z3.ULT(index, 512),

        # perm has no unsafe bits on it and it is present and non-writable
        perm & (dt.MAX_INT64 ^ dt.PTE_PERM_MASK) == 0,
        perm & dt.PTE_P != 0,
        perm & dt.PTE_W == 0,

        # index does not have the P bit in the page table root at that index
        old.pages[old.procs[pid].page_table_root].data(
            index) & dt.PTE_P == 0,
    )

    new = old.copy()

    frm = old.procs[pid].page_table_root

    new.pages[frm].data[index] = (
        (z3.UDiv(new.pages_ptr_to_int, util.i64(dt.PAGE_SIZE)) + frm) << dt.PTE_PFN_SHIFT) | perm

    # maintain the "shadow" pgtable
    new.pages[frm].pgtable_pn[index] = frm
    new.pages[frm].pgtable_perm[index] = perm
    new.pages[frm].pgtable_type[index] = dt.PGTYPE_PAGE

    new.pages[frm].pgtable_reverse_pn = frm
    new.pages[frm].pgtable_reverse_idx = index

    new.flush_tlb(pid)

    return cond, util.If(cond, new, old)


def sys_map_page_desc(old, pid, frm, index, n, perm):
    cond = z3.And(
        z3.ULT(n, dt.NPAGES_PAGE_DESC_TABLE),

        is_pid_valid(pid),

        # the pid is either current or an embryo belonging to current
        z3.Or(pid == old.current,
              z3.And(
                  old.procs[pid].ppid == old.current,
                  old.procs[pid].state == dt.proc_state.PROC_EMBRYO)),

        # frm is a valid pn of type PT whose owner is pid
        is_pn_valid(frm),
        old.pages[frm].type == dt.page_type.PAGE_TYPE_X86_PT,
        old.pages[frm].owner == pid,

        # Index is a valid page index
        z3.ULT(index, 512),

        # perm has no unsafe bits on it and it is present and non-writable
        perm & (dt.MAX_INT64 ^ dt.PTE_PERM_MASK) == 0,
        perm & dt.PTE_P != 0,
        perm & dt.PTE_W == 0,

        # index does not have the P bit in the from page
        old.pages[frm].data(index) & dt.PTE_P == 0,
    )

    new = old.copy()

    new.pages[frm].data[index] = ((z3.UDiv(
        new.page_desc_table_ptr_to_int, util.i64(dt.PAGE_SIZE)) + n) << dt.PTE_PFN_SHIFT) | perm

    # maintain the "shadow" pgtable
    new.pages[frm].pgtable_pn[index] = n
    new.pages[frm].pgtable_perm[index] = perm
    new.pages[frm].pgtable_type[index] = dt.PGTYPE_PAGE_DESC

    new.flush_tlb(pid)

    return cond, util.If(cond, new, old)


def sys_map_dev(old, pid, frm, index, n, perm):
    cond = z3.And(
        z3.ULT(n, dt.NPAGES_DEVICES),

        is_pid_valid(pid),

        # the pid is either current or an embryo belonging to current
        z3.Or(pid == old.current,
              z3.And(
                  old.procs[pid].ppid == old.current,
                  old.procs[pid].state == dt.proc_state.PROC_EMBRYO)),

        # frm is a valid pn of type PT whose owner is pid
        is_pn_valid(frm),
        old.pages[frm].type == dt.page_type.PAGE_TYPE_X86_PT,
        old.pages[frm].owner == pid,

        # Index is a valid page index
        z3.ULT(index, 512),

        # perm has no unsafe bits on it and it is present and non-writable
        perm & (dt.MAX_INT64 ^ dt.PTE_PERM_MASK) == 0,
        perm & dt.PTE_P != 0,
        perm & dt.PTE_W == 0,

        # index does not have the P bit in the from page
        old.pages[frm].data(index) & dt.PTE_P == 0,
    )

    new = old.copy()

    new.pages[frm].data[index] = (
        (z3.UDiv(new.devices_ptr_to_int, util.i64(dt.PAGE_SIZE)) + n) << dt.PTE_PFN_SHIFT) | perm

    # maintain the "shadow" pgtable
    new.pages[frm].pgtable_pn[index] = n
    new.pages[frm].pgtable_perm[index] = perm
    new.pages[frm].pgtable_type[index] = dt.PGTYPE_DEVICES

    new.flush_tlb(pid)

    return cond, util.If(cond, new, old)


def sys_map_file(old, pid, frm, index, n, perm):
    cond = z3.And(
        z3.ULT(n, dt.NPAGES_FILE_TABLE),

        is_pid_valid(pid),

        # the pid is either current or an embryo belonging to current
        z3.Or(pid == old.current,
              z3.And(
                  old.procs[pid].ppid == old.current,
                  old.procs[pid].state == dt.proc_state.PROC_EMBRYO)),

        # frm is a valid pn of type PT whose owner is pid
        is_pn_valid(frm),
        old.pages[frm].type == dt.page_type.PAGE_TYPE_X86_PT,
        old.pages[frm].owner == pid,

        # Index is a valid page index
        z3.ULT(index, 512),

        # perm has no unsafe bits on it and it is present and non-writable
        perm & (dt.MAX_INT64 ^ dt.PTE_PERM_MASK) == 0,
        perm & dt.PTE_P != 0,
        perm & dt.PTE_W == 0,

        # index does not have the P bit in the from page
        old.pages[frm].data(index) & dt.PTE_P == 0,
    )

    new = old.copy()

    new.pages[frm].data[index] = (
        (z3.UDiv(new.file_table_ptr_to_int, util.i64(dt.PAGE_SIZE)) + n) << dt.PTE_PFN_SHIFT) | perm

    # maintain the "shadow" pgtable
    new.pages[frm].pgtable_pn[index] = n
    new.pages[frm].pgtable_perm[index] = perm
    new.pages[frm].pgtable_type[index] = dt.PGTYPE_FILE_TABLE

    new.flush_tlb(pid)

    return cond, util.If(cond, new, old)


def free_page_table_page(old, frm, index, to, from_type, to_type):
    cond = z3.And(
        # The frm pn has the correct type and owned by current
        is_pn_valid(frm),
        old.pages[frm].type == from_type,
        old.pages[frm].owner == old.current,

        # Index is a valid page index
        z3.ULT(index, 512),

        # The to pn has the correct type and owned by current
        is_pn_valid(to),
        old.pages[to].type == to_type,
        old.pages[to].owner == old.current,

        # index does have the P bit in the from page
        old.pages[frm].data(index) & dt.PTE_P != 0,

        # The current pgtable entry matches to...
        z3.Extract(63, 40, z3.UDiv(old.pages_ptr_to_int,
                                   util.i64(dt.PAGE_SIZE)) + to) == z3.BitVecVal(0, 24),
        z3.Extract(39, 0, z3.UDiv(old.pages_ptr_to_int, util.i64(
            dt.PAGE_SIZE)) + to) == z3.Extract(51, 12, old.pages[frm].data(index)),
    )

    new = old.copy()

    new.pages[frm].data[index] = util.i64(0)

    new.pages[to].owner = z3.BitVecVal(0, dt.pid_t)
    new.pages[to].type = dt.page_type.PAGE_TYPE_FREE

    new.procs[old.current].nr_pages[to] -= 1

    new.flush_tlb(old.current)

    return cond, util.If(cond, new, old)


def sys_free_pdpt(old, frm, index, to):
    return free_page_table_page(old, frm, index, to, dt.page_type.PAGE_TYPE_X86_PML4, dt.page_type.PAGE_TYPE_X86_PDPT)


def sys_free_pd(old, frm, index, to):
    return free_page_table_page(old, frm, index, to, dt.page_type.PAGE_TYPE_X86_PDPT, dt.page_type.PAGE_TYPE_X86_PD)


def sys_free_pt(old, frm, index, to):
    return free_page_table_page(old, frm, index, to, dt.page_type.PAGE_TYPE_X86_PD, dt.page_type.PAGE_TYPE_X86_PT)


def sys_free_frame(old, frm, index, to):
    return free_page_table_page(old, frm, index, to, dt.page_type.PAGE_TYPE_X86_PT, dt.page_type.PAGE_TYPE_FRAME)


def sys_switch(old, pid):
    cond = z3.And(
        is_pid_valid(pid),
        old.procs[pid].state == dt.proc_state.PROC_RUNNABLE,

        # This is implied by pid having state runnable,
        # current is always running
        old.current != pid,
    )

    new = old.copy()
    new.procs[old.current].state = util.If(
        old.procs[old.current].killed, dt.proc_state.PROC_ZOMBIE, dt.proc_state.PROC_RUNNABLE)
    new.procs[pid].state = dt.proc_state.PROC_RUNNING
    new.current = pid

    return cond, util.If(cond, new, old)


def sys_kill(old, pid):
    cond = z3.And(
        is_pid_valid(pid),
        old.procs[pid].state != dt.proc_state.PROC_UNUSED,
        old.procs[pid].state != dt.proc_state.PROC_ZOMBIE
    )

    new = old.copy()
    new.procs[pid].killed = z3.BoolVal(True)
    new.procs[pid].state = util.If(
        old.procs[pid].state != dt.proc_state.PROC_RUNNING, dt.proc_state.PROC_ZOMBIE, old.procs[pid].state)

    return cond, util.If(cond, new, old)


switch_proc = sys_switch


def sys_reparent(old, pid):
    cond = z3.And(
        is_pid_valid(pid),
        is_pid_valid(old.procs[pid].ppid),
        old.procs[old.procs[pid].ppid].state == dt.proc_state.PROC_ZOMBIE,

        z3.Or(
            old.procs[dt.INITPID].state == dt.proc_state.PROC_RUNNABLE,
            old.procs[dt.INITPID].state == dt.proc_state.PROC_RUNNING,
        ),
    )

    new = old.copy()

    new.procs[dt.INITPID].nr_children[pid] += 1
    new.procs[old.procs[pid].ppid].nr_children[pid] -= 1

    new.procs[pid].ppid = dt.INITPID

    return cond, util.If(cond, new, old)


def sys_create(old, fd, fn, type, value, omode):
    cond = z3.And(
        type != dt.file_type.FD_NONE,

        # fd is valid and empty
        is_fd_valid(fd),
        z3.Not(is_fn_valid(old.procs[old.current].ofile(fd))),

        # fn is valid and unused
        is_fn_valid(fn),
        old.files[fn].refcnt() == 0,
    )

    new = old.copy()

    new.files[fn].type = type
    new.files[fn].value = value
    new.files[fn].omode = omode

    new.files[fn].offset = z3.BitVecVal(0, dt.off_t)

    new.procs[old.current].ofile[fd] = fn

    new.procs[old.current].nr_fds[fd] += 1

    # bump file refcnt
    new.files[fn].refcnt[(old.current, fd)] += 1

    return cond, util.If(cond, new, old)


def sys_close(old, pid, fd):
    cond = z3.And(
        is_pid_valid(pid),
        is_fd_valid(fd),

        # pid is either current or a zombie
        z3.Or(
            pid == old.current,
            old.procs[pid].state == dt.proc_state.PROC_ZOMBIE),

        is_fn_valid(old.procs[pid].ofile(fd)),
    )
    new = old.copy()

    fn = new.procs[pid].ofile(fd)

    new.procs[pid].ofile[fd] = z3.BitVecVal(0, dt.fn_t)

    new.procs[pid].nr_fds[fd] -= 1

    # decrement file refcnt
    new.files[fn].refcnt[(pid, fd)] -= 1

    ref = new.files[fn].refcnt()

    # If the refcnt is zero, clear the file slot
    new2 = new.copy()
    new2.files[fn].type = dt.file_type.FD_NONE
    new2.files[fn].value = z3.BitVecVal(0, dt.uint64_t)
    new2.files[fn].offset = z3.BitVecVal(0, dt.off_t)
    new2.files[fn].omode = z3.BitVecVal(0, dt.uint64_t)

    return cond, util.If(cond, util.If(ref == 0, new2, new), old)


def sys_dup(old, oldfd, pid, newfd):
    cond = z3.And(
        is_pid_valid(pid),

        # the pid is either current or an embryo belonging to current
        z3.Or(pid == old.current,
              z3.And(
                  old.procs[pid].ppid == old.current,
                  old.procs[pid].state == dt.proc_state.PROC_EMBRYO)),

        is_fd_valid(oldfd),
        is_fn_valid(old.procs[old.current].ofile(oldfd)),

        is_fd_valid(newfd),
        z3.Not(is_fn_valid(old.procs[pid].ofile(newfd))),
    )

    new = old.copy()

    fn = new.procs[old.current].ofile(oldfd)

    new.procs[pid].ofile[newfd] = fn

    new.procs[pid].nr_fds[newfd] += 1

    # bump file refcnt
    new.files[fn].refcnt[(pid, newfd)] += 1

    return cond, util.If(cond, new, old)


def sys_dup2(old, oldfd, pid, newfd):
    cond = z3.And(
        is_pid_valid(pid),

        # the pid is either current or an embryo belonging to current
        z3.Or(pid == old.current,
              z3.And(
                  old.procs[pid].ppid == old.current,
                  old.procs[pid].state == dt.proc_state.PROC_EMBRYO)),

        is_fd_valid(oldfd),
        is_fn_valid(old.procs[old.current].ofile(oldfd)),

        is_fd_valid(newfd),
    )

    new1 = old.copy()

    newfn = new1.procs[pid].ofile(newfd)

    # If fn != 0

    new1.procs[pid].ofile[newfd] = z3.BitVecVal(0, dt.fn_t)

    new1.procs[pid].nr_fds[newfd] -= 1

    # decrement file refcnt
    new1.files[newfn].refcnt[(pid, newfd)] -= 1

    ref = new1.files[newfn].refcnt()

    # If the refcnt is zero, clear the file slot

    new1.files[newfn].type = util.If(ref == 0, dt.file_type.FD_NONE, new1.files[newfn].type)
    new1.files[newfn].value = util.If(ref == 0, z3.BitVecVal(0, dt.uint64_t), new1.files[newfn].value)
    new1.files[newfn].offset = util.If(ref == 0, z3.BitVecVal(0, dt.off_t), new1.files[newfn].offset)
    new1.files[newfn].omode = util.If(ref == 0, z3.BitVecVal(0, dt.uint64_t), new1.files[newfn].omode)

    new2 = util.If(is_fn_valid(old.procs[pid].ofile(newfd)), new1, old.copy())

    # un-conditional

    fn = new2.procs[old.current].ofile(oldfd)

    new2.procs[pid].ofile[newfd] = fn

    new2.procs[pid].nr_fds[newfd] += 1

    # bump file refcnt
    new2.files[fn].refcnt[(pid, newfd)] += 1

    # posix: if fds are the same, do nothing

    new3 = util.If(z3.And(old.current == pid, oldfd == newfd),
                   old.copy(), new2)

    return cond, util.If(cond, new3, old)


def sys_lseek(old, fd, offset):
    cond = z3.And(
        is_fd_valid(fd),
        is_fn_valid(old.procs[old.current].ofile(fd)),
        old.files[old.procs[old.current].ofile(fd)].type == dt.file_type.FD_INODE,
        offset >= 0,
    )

    new = old.copy()

    fn = old.procs[old.current].ofile(fd)
    new.files[fn].offset = offset

    return cond, util.If(cond, new, old)


def sys_map_pcipage(old, pt, index, pcipn, perm):
    cond = z3.And(
        # pt is a valid PT page
        is_pn_valid(pt),
        old.pages[pt].type == dt.page_type.PAGE_TYPE_X86_PT,
        old.pages[pt].owner == old.current,
        z3.ULT(index, 512),

        # pcipn is a valid pci page owned by current
        is_pcipn_valid(pcipn),
        old.pcipages[pcipn].valid,
        old.pci[old.pcipages[pcipn].owner].owner == old.current,

        # perm has no unsafe bits on it and it is present
        perm & (dt.MAX_INT64 ^ dt.PTE_PERM_MASK) == 0,
        perm & dt.PTE_P != 0,

        # slot should be empty
        old.pages[pt].data(index) & dt.PTE_P == 0,
    )

    new = old.copy()

    new.pages[pt].data[index] = ((z3.UDiv(
        dt.PCI_START, util.i64(dt.PAGE_SIZE)) + pcipn) << dt.PTE_PFN_SHIFT) | perm

    # maintain the "shadow" pgtable
    new.pages[pt].pgtable_pn[index] = pcipn
    new.pages[pt].pgtable_perm[index] = perm
    new.pages[pt].pgtable_type[index] = dt.PGTYPE_PCIPAGE

    new.flush_tlb(old.current)

    return cond, util.If(cond, new, old)


def sys_alloc_iommu_root(old, devid, pn):
    cond = z3.And(
        old.pci[devid].owner == 0,
        is_pn_valid(pn),
        old.pages[pn].type == dt.page_type.PAGE_TYPE_FREE,
    )

    new = old.copy()

    new.pci[devid].owner = old.current
    new.pci[devid].page_table_root = pn

    new.pages[pn].owner = old.current
    new.pages[pn].type = dt.page_type.PAGE_TYPE_IOMMU_PML4
    # bzero page
    new.pages[pn].data = util.i64(0)
    new.procs[old.current].nr_pages[pn] += 1

    new.procs[new.current].nr_devs[devid] += 1

    new.flush_iotlb()

    return cond, util.If(cond, new, old)


def alloc_iommu_page_table_page(old, frm, index, to, perm, from_type, to_type):
    cond = z3.And(
        # to page is valid and free
        is_pn_valid(to),
        old.pages[to].type == dt.page_type.PAGE_TYPE_FREE,

        # from page is a valid page with correct type
        is_pn_valid(frm),
        old.pages[frm].type == from_type,

        old.pages[frm].owner == old.current,

        # index is a valid page index
        z3.ULT(index, 512),

        # permission bits check
        perm & (dt.MAX_INT64 ^ (dt.DMAR_PTE_R | dt.DMAR_PTE_W)) == 0,

        old.pages[frm].data(index) == 0,
    )

    new = old.copy()

    new.pages[frm].data[index] = (new.pages_ptr_to_int + to * dt.PAGE_SIZE) | perm
    new.pages[frm].pgtable_pn[index] = to
    new.pages[frm].pgtable_perm[index] = perm

    new.pages[to].type = to_type
    new.pages[to].owner = old.current
    new.pages[to].data = util.i64(0)

    new.procs[old.current].nr_pages[to] += 1

    new.flush_iotlb()

    return cond, util.If(cond, new, old)


def sys_alloc_iommu_pdpt(old, frm, index, to, perm):
    return alloc_iommu_page_table_page(old, frm, index, to, perm,
                                       dt.page_type.PAGE_TYPE_IOMMU_PML4, dt.page_type.PAGE_TYPE_IOMMU_PDPT)


def sys_alloc_iommu_pd(old, frm, index, to, perm):
    return alloc_iommu_page_table_page(old, frm, index, to, perm,
                                       dt.page_type.PAGE_TYPE_IOMMU_PDPT, dt.page_type.PAGE_TYPE_IOMMU_PD)


def sys_alloc_iommu_pt(old, frm, index, to, perm):
    return alloc_iommu_page_table_page(old, frm, index, to, perm,
                                       dt.page_type.PAGE_TYPE_IOMMU_PD, dt.page_type.PAGE_TYPE_IOMMU_PT)


def sys_alloc_iommu_frame(old, frm, index, to, perm):
    cond = z3.And(
        # to page is valid and free
        is_dmapn_valid(to),
        old.dmapages[to].type == dt.page_type.PAGE_TYPE_FREE,

        # from page is a valid page with correct type
        is_pn_valid(frm),
        old.pages[frm].type == dt.page_type.PAGE_TYPE_IOMMU_PT,
        old.pages[frm].owner == old.current,

        # index is a valid page index
        z3.ULT(index, 512),

        # permission bits check
        perm & (dt.MAX_INT64 ^ (dt.DMAR_PTE_R | dt.DMAR_PTE_W)) == 0,

        old.pages[frm].data(index) == 0,
    )

    new = old.copy()

    new.pages[frm].data[index] = (new.dmapages_ptr_to_int + to * dt.PAGE_SIZE) | perm
    new.pages[frm].pgtable_pn[index] = to
    new.pages[frm].pgtable_perm[index] = perm

    new.dmapages[to].type = dt.page_type.PAGE_TYPE_IOMMU_FRAME
    new.dmapages[to].owner = new.current
    new.procs[new.current].nr_dmapages[to] += 1

    new.flush_iotlb()

    return cond, util.If(cond, new, old)


def sys_map_iommu_frame(old, pt, index, to, perm):
    cond = z3.And(
        # to is a valid IOMMU_FRAME owned by current
        is_dmapn_valid(to),
        old.dmapages[to].type == dt.page_type.PAGE_TYPE_IOMMU_FRAME,
        old.dmapages[to].owner == old.current,

        # pt is a valid X86_PT page owned by current
        is_pn_valid(pt),
        old.pages[pt].type == dt.page_type.PAGE_TYPE_X86_PT,
        old.pages[pt].owner == old.current,

        # Index valid
        z3.ULT(index, 512),

        # permissions contain no unsafe bits
        perm & (dt.MAX_INT64 ^ dt.PTE_PERM_MASK) == 0,
        perm & dt.PTE_P != 0,


        # index slot is unused in pt
        old.pages[pt].data(index) & dt.PTE_P == 0,
    )

    new = old.copy()

    new.pages[pt].data[index] = (
        (z3.UDiv(new.dmapages_ptr_to_int, util.i64(dt.PAGE_SIZE)) + to) << dt.PTE_PFN_SHIFT) | perm

    new.pages[pt].pgtable_pn[index] = to
    new.pages[pt].pgtable_perm[index] = perm
    new.pages[pt].pgtable_type[index] = dt.PGTYPE_IOMMU_FRAME

    new.flush_tlb(old.current)

    return cond, util.If(cond, new, old)


def sys_reclaim_iommu_frame(old, dmapn):
    cond = z3.And(
        is_dmapn_valid(dmapn),
        old.dmapages[dmapn].type != dt.page_type.PAGE_TYPE_FREE,
        is_pid_valid(old.dmapages[dmapn].owner),
        old.procs[old.dmapages[dmapn].owner].state == dt.proc_state.PROC_ZOMBIE,
        old.procs[old.dmapages[dmapn].owner].nr_devs() == z3.BitVecVal(0, dt.size_t),
    )

    new = old.copy()

    new.procs[new.dmapages[dmapn].owner].nr_dmapages[dmapn] -= 1
    new.dmapages[dmapn].type = dt.page_type.PAGE_TYPE_FREE
    new.dmapages[dmapn].owner = z3.BitVecVal(0, dt.pid_t)

    return cond, util.If(cond, new, old)


def sys_reclaim_iommu_root(old, devid):
    pid = old.pci[devid].owner
    cond = z3.And(
        is_pid_valid(pid),
        old.procs[pid].state == dt.proc_state.PROC_ZOMBIE,
        old.procs[pid].nr_intremaps() == 0,
    )

    new = old.copy()

    new.procs[pid].nr_devs[devid] -= 1
    # Clear the page_table_root
    new.pci[devid].page_table_root = z3.BitVecVal(-1, dt.pn_t)
    new.pci[devid].owner = z3.BitVecVal(0, dt.pid_t)

    new.flush_iotlb()

    return cond, util.If(cond, new, old)


def sys_send(old, pid, val, pn, size, fd):
    cond = z3.And(
        is_pid_valid(pid),
        old.procs[pid].state == dt.proc_state.PROC_SLEEPING,

        is_pn_valid(pn),
        old.pages[pn].owner == old.current,

        z3.ULE(size, dt.PAGE_SIZE),

        z3.Implies(is_fd_valid(fd),
                   is_fn_valid(old.procs[old.current].ofile(fd))),
    )

    new = old.copy()

    new.procs[pid].ipc_from = old.current
    new.procs[pid].ipc_val = val
    new.procs[pid].ipc_size = size

    # memcpy
    new.pages.data = lambda pn0, idx0, oldfn: \
        util.If(z3.And(pn0 == old.procs[pid].ipc_page, z3.ULT(idx0, size)),
                oldfn(pn, idx0),
                oldfn(pn0, idx0))

    ########
    new2 = new.copy()

    cond2 = z3.And(is_fd_valid(fd), is_fd_valid(new2.procs[pid].ipc_fd))

    fn = old.procs[old.current].ofile(fd)
    fd = old.procs[pid].ipc_fd

    new2.procs[pid].ofile[fd] = fn

    # bump proc nr_fds
    new2.procs[pid].nr_fds[fd] += 1

    # bump file refcnt
    new2.files[fn].refcnt[(pid, fd)] += 1

    new3 = util.If(cond2, new2, new)

    new3.procs[pid].state = dt.proc_state.PROC_RUNNING
    new3.procs[old.current].state = dt.proc_state.PROC_RUNNABLE
    new3.current = pid

    return cond, util.If(cond, new3, old)


send_proc = sys_send


def sys_recv(old, pid, pn, fd):
    cond = z3.And(
        is_pid_valid(pid),
        old.procs[pid].state == dt.proc_state.PROC_RUNNABLE,

        is_pn_valid(pn),
        old.pages[pn].owner == old.current,
        old.pages[pn].type == dt.page_type.PAGE_TYPE_FRAME,

        z3.Implies(is_fd_valid(fd),
                   z3.Not(is_fn_valid(old.procs[old.current].ofile(fd))))
    )

    new = old.copy()

    new.procs[old.current].ipc_from = z3.BitVecVal(0, dt.pid_t)
    new.procs[old.current].ipc_page = pn
    new.procs[old.current].ipc_size = z3.BitVecVal(0, dt.size_t)
    new.procs[old.current].ipc_fd = fd

    new.procs[old.current].state = dt.proc_state.PROC_SLEEPING
    new.procs[pid].state = dt.proc_state.PROC_RUNNING
    new.current = pid

    return cond, util.If(cond, new, old)


recv_proc = sys_recv


def send_recv(old, pid, val, inpn, size, infd, outpn, outfd):
    cond = z3.And(
        is_pid_valid(pid),

        old.procs[pid].state == dt.proc_state.PROC_SLEEPING,

        # inpn is a valid pn and belongs to current
        is_pn_valid(inpn),
        old.pages[inpn].owner == old.current,

        z3.ULE(size, dt.PAGE_SIZE),

        z3.Implies(is_fd_valid(infd),
                   is_fn_valid(old.procs[old.current].ofile(infd))),

        # outpn is a valid pn and belongs to current
        is_pn_valid(outpn),
        old.pages[outpn].owner == old.current,
        old.pages[outpn].type == dt.page_type.PAGE_TYPE_FRAME,

        z3.Implies(is_fd_valid(outfd),
                   z3.Not(is_fn_valid(old.procs[old.current].ofile(outfd)))),

        # if ipc from is set, it must be set to current
        z3.Implies(old.procs[pid].ipc_from != 0,
                   old.procs[pid].ipc_from == old.current)
    )

    new = old.copy()

    new.procs[old.current].ipc_page = outpn
    new.procs[old.current].ipc_fd = outfd

    new.procs[pid].ipc_from = old.current
    new.procs[pid].ipc_val = val

    # memcpy
    new.pages.data = lambda pn0, idx0, oldfn=new.pages.data: \
        util.If(z3.And(pn0 == old.procs[pid].ipc_page, z3.ULT(idx0, size)),
                oldfn(inpn, idx0),
                oldfn(pn0, idx0))

    new.procs[pid].ipc_size = size

    new2 = new.copy()

    cond2 = z3.And(is_fd_valid(infd), is_fd_valid(new2.procs[pid].ipc_fd))

    fn = old.procs[old.current].ofile(infd)
    fd = old.procs[pid].ipc_fd

    new2.procs[pid].ofile[fd] = fn

    # bump proc nr_fds
    new2.procs[pid].nr_fds[fd] += 1

    # bump file refcnt
    new2.files[fn].refcnt[(pid, fd)] += 1

    new3 = util.If(cond2, new2, new)

    new3.procs[old.current].state = dt.proc_state.PROC_SLEEPING
    new3.procs[pid].state = dt.proc_state.PROC_RUNNING

    return cond, util.If(cond, new3, old)


def sys_reply_wait(old, pid, val, inpn, size, infd, outpn):
    cond, new = send_recv(old, pid, val, inpn, size, infd,
                          outpn, z3.BitVecVal(-1, dt.fd_t))

    new.procs[old.current].ipc_from = z3.BitVecVal(0, dt.pid_t)
    new.current = pid

    return cond, util.If(cond, new, old)
reply_wait_proc = sys_reply_wait


def sys_call(old, pid, val, inpn, size, outpn, outfd):
    cond, new = send_recv(old, pid, val, inpn, size,
                          z3.BitVecVal(-1, dt.fd_t), outpn, outfd)

    new.procs[old.current].ipc_from = pid
    new.current = pid

    return cond, util.If(cond, new, old)
call_proc = sys_call


def sys_alloc_vector(old, vector):
    cond = z3.And(
        old.vectors[vector].owner == 0
    )

    new = old.copy()

    new.vectors[vector].owner = old.current
    new.procs[old.current].nr_vectors[vector] += 1

    return cond, util.If(cond, new, old)


def sys_reclaim_vector(old, vector):
    pid = old.vectors[vector].owner
    cond = z3.And(
        is_pid_valid(pid),
        old.procs[pid].state == dt.proc_state.PROC_ZOMBIE,
        old.procs[pid].nr_intremaps() == 0,
    )

    new = old.copy()

    new.vectors[vector].owner = z3.BitVecVal(0, dt.pid_t)
    new.procs[pid].nr_vectors[vector] -= 1

    return cond, util.If(cond, new, old)


def sys_alloc_intremap(old, index, devid, vector):
    cond = z3.And(
        # valid and free index
        is_intremap_valid(index),
        old.intremaps[index].state == dt.intremap_state.IR_FREE,

        # current owns this devid
        old.pci[devid].owner == old.current,

        # current owns this vector
        old.vectors[vector].owner == old.current,
    )

    new = old.copy()

    new.intremaps[index].state = dt.intremap_state.IR_ACTIVE
    new.intremaps[index].devid = devid
    new.intremaps[index].vector = vector

    new.procs[new.current].nr_intremaps[index] += 1

    return cond, util.If(cond, new, old)


def sys_reclaim_intremap(old, index):
    pid = old.pci[old.intremaps[index].devid].owner

    cond = z3.And(
        # active index
        is_intremap_valid(index),
        old.intremaps[index].state == dt.intremap_state.IR_ACTIVE,

        is_pid_valid(pid),
        old.procs[pid].state == dt.proc_state.PROC_ZOMBIE
    )

    new = old.copy()

    new.intremaps[index].state = dt.intremap_state.IR_FREE
    new.intremaps[index].devid = z3.BitVecVal(0, dt.devid_t)
    new.intremaps[index].vector = z3.BitVecVal(0, dt.uint8_t)

    new.procs[pid].nr_intremaps[index] -= 1

    return cond, util.If(cond, new, old)


def sys_ack_intr(old, vector):
    cond = z3.BoolVal(True)

    new = old.copy()

    vector = z3.ZeroExt(64 - vector.size(), vector)
    idx = z3.UDiv(vector, 64)
    mask = 1 << (vector % 64)

    new.procs[new.current].intr[idx] = new.procs[new.current].intr(idx) & ~mask

    return cond, new


def sys_alloc_io_bitmap(old, pn1, pn2, pn3):
    cond = z3.And(
        pn1 + 1 == pn2,
        pn2 + 1 == pn3,

        z3.Not(old.procs[old.current].use_io_bitmap),

        is_pn_valid(pn1),
        old.pages[pn1].type == dt.page_type.PAGE_TYPE_FREE,

        is_pn_valid(pn2),
        old.pages[pn2].type == dt.page_type.PAGE_TYPE_FREE,

        is_pn_valid(pn3),
        old.pages[pn3].type == dt.page_type.PAGE_TYPE_FREE,
    )

    new = old.copy()

    new.pages[pn1].owner = old.current
    new.pages[pn1].type = dt.page_type.PAGE_TYPE_PROC_DATA
    new.pages[pn1].data = util.i64(0xffffffffffffffff)
    new.procs[old.current].nr_pages[pn1] += 1

    new.pages[pn2].owner = old.current
    new.pages[pn2].type = dt.page_type.PAGE_TYPE_PROC_DATA
    new.pages[pn2].data = util.i64(0xffffffffffffffff)
    new.procs[old.current].nr_pages[pn2] += 1

    new.pages[pn3].owner = old.current
    new.pages[pn3].type = dt.page_type.PAGE_TYPE_PROC_DATA
    new.pages[pn3].data = util.i64(0xffffffffffffffff)
    new.procs[old.current].nr_pages[pn3] += 1

    new.procs[old.current].io_bitmap_a = pn1
    new.procs[old.current].io_bitmap_b = pn2
    new.procs[old.current].use_io_bitmap = z3.BoolVal(True)

    return cond, util.If(cond, new, old)


def sys_alloc_port(old, port):
    cond = z3.And(
        old.io[port].owner == 0,
        old.procs[old.current].use_io_bitmap,
    )

    new = old.copy()

    new.io[port].owner = old.current
    new.procs[old.current].nr_ports[port] += 1

    page = util.If(z3.ULT(port, 0x8000),
            new.procs[new.current].io_bitmap_a,
            new.procs[new.current].io_bitmap_b)

    port = z3.ZeroExt(64 - port.size(), util.If(z3.ULT(port, 0x8000), port, port - 0x8000))

    idx = z3.UDiv(port, 64)
    mask = 1 << (port % 64)

    new.pages[page].data[idx] = new.pages[page].data(idx) & ~mask

    return cond, util.If(cond, new, old)


def sys_reclaim_port(old, port):
    pid = old.io[port].owner
    cond = z3.And(
        is_pid_valid(pid),
        old.procs[pid].state == dt.proc_state.PROC_ZOMBIE
    )

    new = old.copy()

    new.procs[pid].nr_ports[port] -= 1
    new.io[port].owner = z3.BitVecVal(0, dt.pid_t)

    return cond, util.If(cond, new, old)


def extintr(old, vector):
    pid = old.vectors[vector].owner
    cond = is_pid_valid(pid)
    cond2 = z3.And(cond, old.procs[pid].state == dt.proc_state.PROC_SLEEPING)

    vector = z3.ZeroExt(64 - vector.size(), vector)
    idx = z3.UDiv(vector, 64)
    mask = 1 << (vector % 64)

    new = old.copy()
    new.procs[pid].intr[idx] = new.procs[pid].intr(idx) | mask

    new2 = new.copy()
    new2.procs[pid].state = dt.proc_state.PROC_RUNNABLE
    new2.procs[pid].ipc_from = z3.BitVecVal(0, dt.pid_t)
    new2.procs[pid].ipc_val = vector
    new2.procs[pid].ipc_size = z3.BitVecVal(0, dt.size_t)

    return cond, util.If(cond, util.If(cond2, new2, new), old)
