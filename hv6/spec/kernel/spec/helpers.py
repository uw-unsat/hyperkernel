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


__all__ = ['is_pid_bounded', 'is_pid_valid', 'is_pn_valid', 'is_dmapn_valid',
           'is_fn_valid', 'is_fd_valid', 'is_pcipn_valid', 'is_page_table_type',
           'is_iommu_page_table_type', 'is_status_live', 'is_va_valid',
           'get_sub_type', 'get_iommu_sub_type', 'pn_has_owner_and_type',
           'pgentry2pfn', 'proc_field_equiv', 'page_walk']


def is_pid_bounded(pid):
    return z3.ULT(pid, dt.NPROC)


def is_pid_valid(pid):
    return z3.And(pid > 0, pid < dt.NPROC)


def is_pn_valid(pn):
    return z3.ULT(pn, dt.NPAGE)


def is_dmapn_valid(pn):
    return z3.ULT(pn, dt.NDMAPAGE)


def is_pcipn_valid(pci):
    return z3.ULT(pci, dt.NPCIPAGE)


def is_fn_valid(fn):
    return z3.And(z3.UGT(fn, 0), z3.ULT(fn, dt.NFILE))


def is_fd_valid(fd):
    return z3.And(fd >= 0, fd < dt.NOFILE)


def is_intremap_valid(index):
    return z3.ULT(index, dt.NINTREMAP)


def is_page_table_type(type):
    return util.In(type, [
        dt.page_type.PAGE_TYPE_X86_PML4,
        dt.page_type.PAGE_TYPE_X86_PDPT,
        dt.page_type.PAGE_TYPE_X86_PD,
        dt.page_type.PAGE_TYPE_X86_PT,
    ])


def is_iommu_page_table_type(type):
    return util.In(type, [
        dt.page_type.PAGE_TYPE_IOMMU_PML4,
        dt.page_type.PAGE_TYPE_IOMMU_PDPT,
        dt.page_type.PAGE_TYPE_IOMMU_PD,
        dt.page_type.PAGE_TYPE_IOMMU_PT,
    ])


def is_status_live(status):
    return util.In(status, [
        dt.proc_state.PROC_EMBRYO,
        dt.proc_state.PROC_RUNNABLE,
        dt.proc_state.PROC_RUNNING,
        dt.proc_state.PROC_SLEEPING,
    ])


def is_va_valid(va):
    return z3.And(*[z3.ULT(idx, 512) for idx in va])


def get_sub_type(type):
    return util.If(type == dt.page_type.PAGE_TYPE_X86_PML4, dt.page_type.PAGE_TYPE_X86_PDPT,
                 util.If(type == dt.page_type.PAGE_TYPE_X86_PDPT, dt.page_type.PAGE_TYPE_X86_PD,
                       util.If(type == dt.page_type.PAGE_TYPE_X86_PD, dt.page_type.PAGE_TYPE_X86_PT,
                             util.If(type == dt.page_type.PAGE_TYPE_X86_PT, dt.page_type.PAGE_TYPE_FRAME,
                                   util.FreshBitVec('invalid', dt.page_type.PAGE_TYPE_FRAME.size())))))


def get_iommu_sub_type(type):
    return util.If(type == dt.page_type.PAGE_TYPE_IOMMU_PML4, dt.page_type.PAGE_TYPE_IOMMU_PDPT,
                 util.If(type == dt.page_type.PAGE_TYPE_IOMMU_PDPT, dt.page_type.PAGE_TYPE_IOMMU_PD,
                       util.If(type == dt.page_type.PAGE_TYPE_IOMMU_PD, dt.page_type.PAGE_TYPE_IOMMU_PT,
                             util.If(type == dt.page_type.PAGE_TYPE_IOMMU_PT, dt.page_type.PAGE_TYPE_IOMMU_FRAME,
                                   util.FreshBitVec('invalid', dt.page_type.PAGE_TYPE_IOMMU_FRAME.size())))))


def pn_has_owner_and_type(ctx, pn, pid, type):
    return z3.And(is_pn_valid(pn),
                  util.global_field_element(
                      ctx, '@page_desc_table', 'pid', pn) == pid,
                  util.global_field_element(ctx, '@page_desc_table', 'type', pn) == type)


def pgentry2pfn(ks, off, perm, type):
    res = util.i64(0)
    res = util.If(type == dt.PGTYPE_PCIPAGE, util.i64(dt.PCI_START), res)
    res = util.If(type == dt.PGTYPE_IOMMU_FRAME, ks.dmapages_ptr_to_int, res)
    res = util.If(type == dt.PGTYPE_DEVICES, ks.devices_ptr_to_int, res)
    res = util.If(type == dt.PGTYPE_FILE_TABLE, ks.file_table_ptr_to_int, res)
    res = util.If(type == dt.PGTYPE_PAGE_DESC, ks.page_desc_table_ptr_to_int, res)
    res = util.If(type == dt.PGTYPE_PROC, ks.proc_table_ptr_to_int, res)
    res = util.If(type == dt.PGTYPE_PAGE, ks.pages_ptr_to_int, res)
    return ((z3.UDiv(res, util.i64(dt.PAGE_SIZE)) + off) << dt.PTE_PFN_SHIFT) | perm


def proc_field_equiv(conj, pid, ctx, kernelstate, field_name):
    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        util.global_field_element(ctx, '@proc_table', field_name, pid) ==
        getattr(kernelstate.procs[pid], field_name))))


def page_walk(state, pml4, idx1, idx2, idx3, idx4):
    pdpt = state.pages[pml4].pgtable_pn(idx1)
    pd = state.pages[pdpt].pgtable_pn(idx2)
    pt = state.pages[pd].pgtable_pn(idx3)
    frame = state.pages[pt].pgtable_pn(idx4)

    present = z3.And(
        # P bit is set on each level down.
        dt.has_bit(state.pages[pml4].data(idx1), dt.PTE_P),
        dt.has_bit(state.pages[pdpt].data(idx2), dt.PTE_P),
        dt.has_bit(state.pages[pd].data(idx3), dt.PTE_P),
        dt.has_bit(state.pages[pt].data(idx4), dt.PTE_P),
        # The last level is of type page
        state.pages[pt].pgtable_type(idx4) == dt.PGTYPE_PAGE)

    writable = z3.And(
        # W bit is set on each level down.
        dt.has_bit(state.pages[pml4].data(idx1), dt.PTE_W),
        dt.has_bit(state.pages[pdpt].data(idx2), dt.PTE_W),
        dt.has_bit(state.pages[pd].data(idx3), dt.PTE_W),
        dt.has_bit(state.pages[pt].data(idx4), dt.PTE_W),
        # The last level is of type page
        state.pages[pt].pgtable_type(idx4) == dt.PGTYPE_PAGE
    )

    return frame, writable, present
