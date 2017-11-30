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
        get_sub_type,
        get_iommu_sub_type,
        is_dmapn_valid,
        is_fd_valid,
        is_fn_valid,
        is_intremap_valid,
        is_iommu_page_table_type,
        is_page_table_type,
        is_pid_valid,
        is_pn_valid,
        is_status_live,
        is_va_valid,
        page_walk,
        pgentry2pfn,
)


# process pid's nr_pages == the number of pages owned by pid
def spec_lemma_nr_pages_refcnt(kernelstate):
    conj = []

    pid = util.FreshBitVec('pid', dt.pid_t)

    # PROC_UNUSED state implies refcount is 0 (sys_clone needs this)
    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        z3.Implies(kernelstate.procs[pid].state == dt.proc_state.PROC_UNUSED,
            kernelstate.procs[pid].nr_pages() == z3.BitVecVal(0, dt.size_t)))))

    # Correctness definition for `permutation` based refcount
    kernelstate.procs.nr_pages.check(conj,
            is_owner_valid=is_pid_valid,
            is_owned_valid=is_pn_valid,
            max_refs=dt.NPAGE,
            ownerfn=lambda pn: kernelstate.pages[pn].owner)

    return z3.And(*conj)


def spec_lemma_nr_dmapages_refcnt(kernelstate):
    conj = []

    pid = util.FreshBitVec('pid', dt.pid_t)
    dmapn = util.FreshBitVec('dmapn', dt.dmapn_t)

    # General invariant -- a free dma page has no owner
    conj.append(z3.ForAll([dmapn], z3.Implies(is_dmapn_valid(dmapn),
        is_pid_valid(kernelstate.dmapages[dmapn].owner) ==
        (kernelstate.dmapages[dmapn].type != dt.page_type.PAGE_TYPE_FREE))))

    # PROC_UNUSED state implies refcount is 0 (sys_clone needs this)
    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        z3.Implies(kernelstate.procs[pid].state == dt.proc_state.PROC_UNUSED,
            kernelstate.procs[pid].nr_dmapages() == z3.BitVecVal(0, dt.size_t)))))

    # # Correctness definition for `permutation` based refcount
    kernelstate.procs.nr_dmapages.check(conj,
            is_owner_valid=is_pid_valid,
            is_owned_valid=is_dmapn_valid,
            max_refs=dt.NDMAPAGE,
            ownerfn=lambda dmapn: kernelstate.dmapages[dmapn].owner)

    return z3.And(*conj)


# process pid's nr_children == the number of processes with pid as parent (ppid)
def spec_lemma_nr_children_refcnt(kernelstate):
    conj = []

    pid = util.FreshBitVec('pid', dt.pid_t)

    # pid has a parent <=> pid is not PROC_UNUSED
    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        is_pid_valid(kernelstate.procs[pid].ppid) ==
        (kernelstate.procs[pid].state != dt.proc_state.PROC_UNUSED))))

    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        z3.Implies(kernelstate.procs[pid].state == dt.proc_state.PROC_UNUSED,
            z3.Not(is_pid_valid(kernelstate.procs[pid].ppid))))))

    # PROC_UNUSED state implies refcnt is 0
    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        z3.Implies(kernelstate.procs[pid].state == dt.proc_state.PROC_UNUSED,
            kernelstate.procs[pid].nr_children() == z3.BitVecVal(0, dt.size_t)))))

    # unused procs don't have a parent
    conj.append(z3.ForAll([pid], z3.Implies(
        z3.And(
            is_pid_valid(pid),
            kernelstate.procs[pid].state == dt.proc_state.PROC_UNUSED),
        kernelstate.procs[pid].ppid == z3.BitVecVal(0, dt.pid_t))))

    # Correctness definition for `permutation` based refcount
    kernelstate.procs.nr_children.check(conj,
            is_owner_valid=is_pid_valid,
            is_owned_valid=is_pid_valid,
            max_refs=dt.NPROC-1,
            ownerfn=lambda pid0: kernelstate.procs[pid0].ppid)

    return z3.And(*conj)


# process pid's nr_fds == the number of valid fds in its fd table
def spec_lemma_nr_fds_refcnt(kernelstate):
    conj = []

    pid = util.FreshBitVec('pid', dt.pid_t)
    fd = util.FreshBitVec('fd', dt.fd_t)

    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        z3.Implies(kernelstate.procs[pid].state == dt.proc_state.PROC_UNUSED,
            kernelstate.procs[pid].nr_fds() == z3.BitVecVal(0, dt.size_t)))))

    conj.append(z3.ForAll([pid, fd], z3.Implies(z3.And(is_pid_valid(pid), is_fd_valid(fd)),
        z3.Implies(kernelstate.procs[pid].state == dt.proc_state.PROC_UNUSED,
            z3.Not(is_fn_valid(kernelstate.procs[pid].ofile(fd)))))))

    conj.append(z3.ForAll([pid, fd], z3.Implies(
        z3.And(
            is_pid_valid(pid),
            is_fd_valid(fd),
            is_fn_valid(kernelstate.procs[pid].ofile(fd))),
            kernelstate.procs[pid].state != dt.proc_state.PROC_UNUSED)))

    kernelstate.procs.nr_fds.check(conj,
            is_owner_valid=is_pid_valid,
            is_owned_valid=is_fd_valid,
            max_refs=dt.NOFILE,
            ownedby=lambda pid, fd: is_fn_valid(kernelstate.procs[pid].ofile(fd)))

    return z3.And(*conj)


def spec_lemma_nr_devs_refcnt(kernelstate):
    conj = []

    pid = util.FreshBitVec('pid', dt.pid_t)
    devid = util.FreshBitVec('devid', dt.devid_t)

    # unused procs don't own any devices
    conj.append(z3.ForAll([devid], z3.Implies(
        is_pid_valid(kernelstate.pci[devid].owner),
        kernelstate.procs[kernelstate.pci[devid].owner].state != dt.proc_state.PROC_UNUSED)))

    conj.append(z3.ForAll([pid], z3.Implies(kernelstate.procs[pid].state == dt.proc_state.PROC_UNUSED,
            kernelstate.procs[pid].nr_devs() == z3.BitVecVal(0, dt.size_t))))

    # Correctness definition for `permutation` based refcount
    kernelstate.procs.nr_devs.check(conj,
            is_owner_valid=is_pid_valid,
            is_owned_valid=lambda n: z3.BoolVal(True),
            max_refs=2**dt.devid_t.size(),
            ownerfn=lambda devid0: kernelstate.pci[devid0].owner)

    return z3.And(*conj)


def spec_lemma_nr_ports_refcnt(kernelstate):
    conj = []

    pid = util.FreshBitVec('pid', dt.pid_t)
    port = util.FreshBitVec('port', dt.uint16_t)

    # unused procs don't own any ports
    conj.append(z3.ForAll([port], z3.Implies(
        is_pid_valid(kernelstate.io[port].owner),
        kernelstate.procs[kernelstate.io[port].owner].state != dt.proc_state.PROC_UNUSED)))

    conj.append(z3.ForAll([pid], z3.Implies(kernelstate.procs[pid].state == dt.proc_state.PROC_UNUSED,
            kernelstate.procs[pid].nr_ports() == z3.BitVecVal(0, dt.size_t))))

    # Correctness definition for `permutation` based refcount
    kernelstate.procs.nr_ports.check(conj,
            is_owner_valid=is_pid_valid,
            is_owned_valid=lambda n: z3.BoolVal(True),
            max_refs=2**dt.uint16_t.size(),
            ownerfn=lambda port0: kernelstate.io[port0].owner)

    return z3.And(*conj)


def spec_lemma_nr_vectors(kernelstate):
    conj = []

    kernelstate.procs.nr_vectors.check(conj,
            is_owner_valid=is_pid_valid,
            is_owned_valid=lambda n: z3.BoolVal(True),
            max_refs=2**dt.uint8_t.size(),
            ownerfn=lambda vector0: kernelstate.vectors[vector0].owner)

    return z3.And(*conj)


def spec_lemma_nr_intremaps(kernelstate):
    conj = []

    index = util.FreshBitVec('index', dt.size_t)

    # active intremaps have valid pid owners
    conj.append(z3.ForAll([index], z3.Implies(
        z3.And(
            is_intremap_valid(index),
            kernelstate.intremaps[index].state == dt.intremap_state.IR_ACTIVE),
        is_pid_valid(kernelstate.pci[kernelstate.intremaps[index].devid].owner))))

    # intremaps's vector and devid match
    conj.append(z3.ForAll([index], z3.Implies(
        z3.And(
            is_intremap_valid(index),
            kernelstate.intremaps[index].state == dt.intremap_state.IR_ACTIVE),
        kernelstate.pci[kernelstate.intremaps[index].devid].owner ==
        kernelstate.vectors[kernelstate.intremaps[index].vector].owner)))

    kernelstate.procs.nr_intremaps.check(conj,
            is_owner_valid=is_pid_valid,
            is_owned_valid=is_intremap_valid,
            max_refs=dt.NINTREMAP,
            ownerfn=lambda index0: \
                util.If(kernelstate.intremaps[index0].state == dt.intremap_state.IR_ACTIVE,
                    kernelstate.pci[kernelstate.intremaps[index0].devid].owner,
                    0))

    return z3.And(*conj)


# file f's refcnt == the number of (pid, fd) that points to f
def spec_lemma_files_refcnt(kernelstate, syscall=None):
    conj = []

    if syscall == 'clone_proc':
        conj.append(spec_lemma_nr_fds_refcnt(kernelstate))

    pid = util.FreshBitVec('pid', dt.pid_t)
    fd = util.FreshBitVec('fd', dt.fd_t)

    kernelstate.files.refcnt.check(conj,
            is_owner_valid=is_fn_valid,
            is_owned1_valid=is_pid_valid,
            is_owned2_valid=is_fd_valid,
            max_refs=(dt.NPROC - 1) * dt.NOFILE,
            ownerfn=lambda pidfn: \
                kernelstate.procs[pidfn[0]].ofile(pidfn[1]))

    return z3.And(*conj)


# memory isolation
def spec_corollary_pgwalk(kernelstate):
    pid = util.FreshBitVec('pid', dt.pid_t)
    va = dt.FreshVA()

    pml4 = kernelstate.procs[pid].page_table_root
    # Abstract model of a page_walk starting from some root
    page, writable, present = page_walk(kernelstate, pml4, *va)

    # If a four level page-walk from some pid returns a page,
    # that page must be exclusively owned by the pid.
    # furthermore, if the page is writable,
    # it has to be a frame.
    isolation = util.Implies(present,
            kernelstate.pages[page].owner == pid,
            z3.Implies(writable, kernelstate.pages[page].type == dt.page_type.PAGE_TYPE_FRAME))

    return z3.ForAll([pid] + va,
        z3.Implies(
            z3.And(
                is_pid_valid(pid),
                is_status_live(kernelstate.procs[pid].state),
                is_va_valid(va),
                ),
            isolation))


# IOMMU memory isolation
def spec_corollary_iommu_pgwalk(kernelstate):
    devid = util.FreshBitVec('devid', dt.devid_t)
    pid = kernelstate.pci[devid].owner
    va = dt.FreshVA()

    pml4 = kernelstate.pci[devid].page_table_root
    page, writable, present = page_walk(kernelstate, pml4, *va)

    isolation = util.Implies(present,
            kernelstate.dmapages[page].owner == pid,
            kernelstate.dmapages[page].type == dt.page_type.PAGE_TYPE_IOMMU_FRAME)

    return z3.ForAll([devid] + va,
        z3.Implies(
            z3.And(
                is_pn_valid(pml4),
                is_va_valid(va),
            ),
            isolation))


def spec_lemma_isolation(kernelstate):
    conj = []

    conj.append(spec_lemma_nr_pages_refcnt(kernelstate))

    pn = util.FreshBitVec('pn', dt.pn_t)
    idx = util.FreshBitVec('page_index', dt.size_t)

    conj.append(z3.ForAll([pn, idx], z3.Implies(
        z3.And(
            # Arguments are valid
            is_pn_valid(pn),
            z3.ULT(idx, 512),

            # This is a page table and the idx entry does have the P bit set
            is_page_table_type(kernelstate.pages[pn].type),
            (kernelstate.pages[pn].data(idx) & dt.PTE_P) != 0,

            # The owner of this page has a valid pid and is either EMBRYO, RUNNABLE or RUNNING
            is_status_live(
                kernelstate.procs[kernelstate.pages[pn].owner].state),
            is_pid_valid(kernelstate.pages[pn].owner),
        ),
        z3.And(
            z3.ULT(kernelstate.pages[pn].pgtable_type(idx), dt.PGTYPE_NONE),

            # The contents of the shadow pgatble correspond to the *actual*
            # contents of those pages according to our pn->pfn mapping fn.
            kernelstate.pages[pn].data(idx) == pgentry2pfn(kernelstate,
                                                           kernelstate.pages[pn].pgtable_pn(idx),
                                                           kernelstate.pages[pn].pgtable_perm(idx),
                                                           kernelstate.pages[pn].pgtable_type(idx)),

            z3.Extract(62, 12, kernelstate.pages[pn].pgtable_perm(idx)) == z3.BitVecVal(0, 51),

            # For the specification each entry in the pgtable has a type.
            # For each of those type, we must specify how it can appear in a
            # the page table.

            # If the entry is a page
            z3.Implies(
                kernelstate.pages[pn].pgtable_type(idx) == dt.PGTYPE_PAGE,

                z3.And(
                    # The entry must be a valid pn
                    is_pn_valid(kernelstate.pages[pn].pgtable_pn(idx)),

                    # The pn must be owned by the owner of the pgtable
                    kernelstate.pages[kernelstate.pages[pn].pgtable_pn(
                        idx)].owner == kernelstate.pages[pn].owner,

                    # Either the subtypes match (PML4 => PDPT, PDPT => PD, etc) and is a unique mapping.
                    # Or PML4 points to a *read_only* PML4 page.
                    z3.Or(
                        z3.And(
                            get_sub_type(kernelstate.pages[pn].type) ==
                                kernelstate.pages[kernelstate.pages[pn].pgtable_pn(idx)].type,
                            # The mapping from a pgtable <pn, idx> to a page is unique
                            kernelstate.pages[kernelstate.pages[pn].pgtable_pn(idx)].pgtable_reverse_pn == pn,
                            kernelstate.pages[kernelstate.pages[pn].pgtable_pn(idx)].pgtable_reverse_idx == idx,
                        ),
                        z3.And(
                            kernelstate.pages[pn].type == dt.page_type.PAGE_TYPE_X86_PML4,
                            kernelstate.pages[kernelstate.pages[pn].pgtable_pn(idx)].type == dt.page_type.PAGE_TYPE_X86_PML4,
                            kernelstate.pages[pn].pgtable_perm(idx) & dt.PTE_W == 0)))),

            # If the entry is a proc
            z3.Implies(
                kernelstate.pages[pn].pgtable_type(idx) == dt.PGTYPE_PROC,

                z3.And(
                    # This must be at the PT level in the pgtable
                    kernelstate.pages[pn].type == dt.page_type.PAGE_TYPE_X86_PT,

                    # There are 3 proc pages
                    z3.ULT(kernelstate.pages[pn].pgtable_pn(idx),
                           dt.NPAGES_PROC_TABLE),

                    # proc pages can not be mapped writable
                    kernelstate.pages[pn].pgtable_perm(idx) & dt.PTE_W == 0)),

            # If the entry is a page_desc
            z3.Implies(
                kernelstate.pages[pn].pgtable_type(idx) == dt.PGTYPE_PAGE_DESC,

                z3.And(
                    # This must be at the PT level in the pgtable
                    kernelstate.pages[pn].type == dt.page_type.PAGE_TYPE_X86_PT,

                    # There are 15 page desc pages
                    z3.ULT(kernelstate.pages[pn].pgtable_pn(idx),
                           dt.NPAGES_PAGE_DESC_TABLE),

                    # page desc pages can not be mapped writable
                    kernelstate.pages[pn].pgtable_perm(idx) & dt.PTE_W == 0)),

            # If the entry is file table
            z3.Implies(
                kernelstate.pages[pn].pgtable_type(idx) == dt.PGTYPE_FILE_TABLE,

                z3.And(
                    # This must be at the PT level in the pgtable
                    kernelstate.pages[pn].type == dt.page_type.PAGE_TYPE_X86_PT,

                    # There are 15 page desc pages
                    z3.ULT(kernelstate.pages[pn].pgtable_pn(idx),
                           dt.NPAGES_FILE_TABLE),

                    # file tables can not be mapped writable
                    kernelstate.pages[pn].pgtable_perm(idx) & dt.PTE_W == 0)),

            # If the entry is devices
            z3.Implies(
                kernelstate.pages[pn].pgtable_type(idx) == dt.PGTYPE_DEVICES,

                z3.And(
                    # This must be at the PT level in the pgtable
                    kernelstate.pages[pn].type == dt.page_type.PAGE_TYPE_X86_PT,

                    # There are 15 page desc pages
                    z3.ULT(kernelstate.pages[pn].pgtable_pn(idx),
                           dt.NPAGES_DEVICES),

                    # page desc pages can not be mapped writable
                    kernelstate.pages[pn].pgtable_perm(idx) & dt.PTE_W == 0)),

            # If the entry is an IOMMU_FRAME
            z3.Implies(
                    kernelstate.pages[pn].pgtable_type(idx) == dt.PGTYPE_IOMMU_FRAME,

                    z3.And(
                        # This must be at the PT level in the pgtable
                        kernelstate.pages[pn].type == dt.page_type.PAGE_TYPE_X86_PT,

                        # There are NDMAPAGES many dma pages that can be mapped
                        z3.ULT(kernelstate.pages[pn].pgtable_pn(idx), dt.NDMAPAGE),

                        # must be an IOMMU_FRAME
                        kernelstate.dmapages[kernelstate.pages[pn].pgtable_pn(idx)].type
                            == dt.page_type.PAGE_TYPE_IOMMU_FRAME,

                        # the dma page must belong to the owner of the pt page
                        kernelstate.dmapages[kernelstate.pages[pn].pgtable_pn(idx)].owner
                            == kernelstate.pages[pn].owner
                        )),

            # If the entry is a pci page
            z3.Implies(
                    kernelstate.pages[pn].pgtable_type(idx) == dt.PGTYPE_PCIPAGE,

                    z3.And(
                        # This must be at the PT level in the pgtable
                        kernelstate.pages[pn].type == dt.page_type.PAGE_TYPE_X86_PT,

                        # There are NPCIPAGE many pci pages that can be mapped
                        z3.ULT(kernelstate.pages[pn].pgtable_pn(idx), dt.NPCIPAGE),

                        # the pci page must belong to a device owned by the
                        # proc that owns the pgtable page
                        kernelstate.pci[
                                kernelstate.pcipages[
                                    kernelstate.pages[pn].pgtable_pn(idx)].owner].owner
                                == kernelstate.pages[pn].owner)),

            ))))

    return z3.And(*conj)


def spec_lemma_iommu_isolation(kernelstate):
    conj = []

    conj.append(spec_lemma_nr_pages_refcnt(kernelstate))
    conj.append(spec_lemma_nr_devs_refcnt(kernelstate))

    pn = util.FreshBitVec('pn', dt.pn_t)
    idx = util.FreshBitVec('page_index', dt.size_t)
    devid = util.FreshBitVec('devid', dt.devid_t)

    conj.append(z3.ForAll([devid], z3.Implies(
        is_pn_valid(kernelstate.pci[devid].page_table_root),
        z3.And(
            is_pid_valid(kernelstate.pci[devid].owner),
            kernelstate.pages[kernelstate.pci[devid].page_table_root].type == dt.page_type.PAGE_TYPE_IOMMU_PML4,
            kernelstate.pages[kernelstate.pci[devid].page_table_root].owner == kernelstate.pci[devid].owner
        )
    )))

    conj.append(z3.ForAll([pn, idx], z3.Implies(
        z3.And(
            is_pn_valid(pn),
            z3.ULT(idx, 512),

            is_iommu_page_table_type(kernelstate.pages[pn].type),
            dt.has_bit(kernelstate.pages[pn].data(idx), dt.PTE_P),

            is_pid_valid(kernelstate.pages[pn].owner),

            # If this proc has a device, nr_devs is non-zero.
            # Devices can write regardless of proc status.
            z3.Or(
                is_status_live(kernelstate.procs[kernelstate.pages[pn].owner].state),
                kernelstate.procs[kernelstate.pages[pn].owner].nr_devs() != 0),
        ),
        z3.And(
            # The iommu page table is highly-regular and there are basically
            # two cases.
            # The page table it self is made from pages in the `pages` array.
            # And the last level are all dmapages from the `dmapages` array.

            z3.Implies(kernelstate.pages[pn].type != dt.page_type.PAGE_TYPE_IOMMU_PT,
                z3.And(
                    kernelstate.pages[pn].data(idx) ==
                    (kernelstate.pages_ptr_to_int +
                        kernelstate.pages[pn].pgtable_pn(idx) * 4096) |
                    kernelstate.pages[pn].pgtable_perm(idx),

                    is_pn_valid(kernelstate.pages[pn].pgtable_pn(idx)),

                    get_iommu_sub_type(kernelstate.pages[pn].type) ==
                        kernelstate.pages[kernelstate.pages[pn].pgtable_pn(idx)].type,

                    kernelstate.pages[kernelstate.pages[pn].pgtable_pn(idx)].owner
                        == kernelstate.pages[pn].owner,
                )),

            z3.Implies(kernelstate.pages[pn].type == dt.page_type.PAGE_TYPE_IOMMU_PT,
                z3.And(
                    kernelstate.pages[pn].data(idx) ==
                    (kernelstate.dmapages_ptr_to_int +
                        kernelstate.pages[pn].pgtable_pn(idx) * 4096) |
                    kernelstate.pages[pn].pgtable_perm(idx),

                    is_dmapn_valid(kernelstate.pages[pn].pgtable_pn(idx)),

                    kernelstate.dmapages[kernelstate.pages[pn].pgtable_pn(idx)].type
                    == dt.page_type.PAGE_TYPE_IOMMU_FRAME,

                    kernelstate.dmapages[kernelstate.pages[pn].pgtable_pn(idx)].owner
                        == kernelstate.pages[pn].owner,
                )),

        ))))

    return z3.And(*conj)


# if any page-table page is modified, tlb is flushed
def spec_lemma_tlb_ok(kernelstate, oldstate=None):
    if kernelstate is oldstate or oldstate is None:
        return z3.BoolVal(True)

    pn = util.FreshBitVec('pn', dt.pn_t)
    idx = util.FreshBitVec('page_index', dt.size_t)

    return z3.ForAll([pn, idx], z3.Implies(
        z3.And(
            # Arguments are valid
            is_pn_valid(pn),
            z3.ULT(idx, 512),

            is_page_table_type(oldstate.pages[pn].type)),
        z3.And(
            z3.Implies(
                oldstate.pages[pn].data(idx) != kernelstate.pages[pn].data(idx),
                kernelstate.procs[oldstate.pages[pn].owner].tlbinv
        ))))


# if any IOMMU page-table page is modified, IOMMU is flushed
def spec_lemma_iommu_tlb_ok(kernelstate, oldstate=None):
    if kernelstate is oldstate or oldstate is None:
        return z3.BoolVal(True)

    pn = util.FreshBitVec('pn', dt.pn_t)
    idx = util.FreshBitVec('page_index', dt.size_t)

    return z3.ForAll([pn, idx], z3.Implies(
        z3.And(
            # Arguments are valid
            is_pn_valid(pn),
            z3.ULT(idx, 512),

            is_iommu_page_table_type(oldstate.pages[pn].type)),
        z3.And(
            z3.Implies(
                oldstate.pages[pn].data(idx) != kernelstate.pages[pn].data(idx),
                kernelstate.iotlbinv)
        )))
