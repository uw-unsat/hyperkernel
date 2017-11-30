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
import z3
from libirpy import util
import hv6py.kernel.spec.datatypes as dt

from invariants import impl_invariants
from helpers import (
        is_dmapn_valid,
        is_fd_valid,
        is_fn_valid,
        is_intremap_valid,
        is_pcipn_valid,
        is_pid_valid,
        is_pn_valid,
        proc_field_equiv,
)


__all__ = ['state_equiv']


"""
Defines when KernelState and irpy context state are equivalent
"""


def procs_equiv(conj, ctx, kernelstate):
    pid = util.FreshBitVec('pid', dt.pid_t)
    fd = util.FreshBitVec('fd', dt.fd_t)
    idx = util.FreshBitVec('vector_index', 64)

    proc_field_equiv(conj, pid, ctx, kernelstate, 'state')
    proc_field_equiv(conj, pid, ctx, kernelstate, 'ppid')

    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        (util.global_field_element(ctx, '@proc_table', 'killed', pid) == 0) ==
        z3.Not(kernelstate.procs[pid].killed))))

    proc_field_equiv(conj, pid, ctx, kernelstate, 'ipc_from')
    proc_field_equiv(conj, pid, ctx, kernelstate, 'ipc_val')
    proc_field_equiv(conj, pid, ctx, kernelstate, 'ipc_page')
    proc_field_equiv(conj, pid, ctx, kernelstate, 'ipc_size')
    proc_field_equiv(conj, pid, ctx, kernelstate, 'ipc_fd')

    conj.append(z3.ForAll([pid, fd], z3.Implies(
        z3.And(
            is_pid_valid(pid),
            is_fd_valid(fd)),
        util.global_field_element(ctx, '@proc_table', 'ofile', pid, z3.ZeroExt(32, fd)) ==
        kernelstate.procs[pid].ofile(fd))))

    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        util.global_field_element(ctx, '@proc_table', 'nr_children', pid) ==
        kernelstate.procs[pid].nr_children())))

    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        util.global_field_element(ctx, '@proc_table', 'nr_fds', pid) ==
        kernelstate.procs[pid].nr_fds())))

    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        util.global_field_element(ctx, '@proc_table', 'nr_pages', pid) ==
        kernelstate.procs[pid].nr_pages())))

    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        util.global_field_element(ctx, '@proc_table', 'nr_dmapages', pid) ==
        kernelstate.procs[pid].nr_dmapages())))

    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        util.global_field_element(ctx, '@proc_table', 'nr_devs', pid) ==
        kernelstate.procs[pid].nr_devs())))

    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        util.global_field_element(ctx, '@proc_table', 'nr_ports', pid) ==
        kernelstate.procs[pid].nr_ports())))

    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        util.global_field_element(ctx, '@proc_table', 'nr_vectors', pid) ==
        kernelstate.procs[pid].nr_vectors())))

    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        util.global_field_element(ctx, '@proc_table', 'nr_intremaps', pid) ==
        kernelstate.procs[pid].nr_intremaps())))

    proc_field_equiv(conj, pid, ctx, kernelstate, 'stack')
    proc_field_equiv(conj, pid, ctx, kernelstate, 'hvm')
    proc_field_equiv(conj, pid, ctx, kernelstate, 'page_table_root')

    conj.append(z3.ForAll([pid], z3.Implies(is_pid_valid(pid),
        (util.global_field_element(ctx, '@proc_table', 'use_io_bitmap', pid) == 0) ==
        z3.Not(kernelstate.procs[pid].use_io_bitmap))))

    proc_field_equiv(conj, pid, ctx, kernelstate, 'io_bitmap_a')
    proc_field_equiv(conj, pid, ctx, kernelstate, 'io_bitmap_b')

    conj.append(z3.ForAll([pid, idx], z3.Implies(
        z3.And(
            is_pid_valid(pid),
            z3.ULT(idx, 4)),
        util.global_field_element(ctx, '@proc_table', 'intr', pid, idx) ==
        kernelstate.procs[pid].intr(idx))))

    conj.append(z3.ForAll([pid],
        ctx.globals['#tlbinv'](pid) == kernelstate.procs[pid].tlbinv))

    conj.append(ctx.globals['#iotlbinv'] == kernelstate.iotlbinv)


def pages_equiv(conj, ctx, kernelstate):
    pn = util.FreshBitVec('pn', dt.pn_t)
    idx = util.FreshBitVec('page_index', 64)

    conj.append(z3.ForAll([pn, idx], z3.Implies(
        z3.And(
            is_pn_valid(pn),
            z3.ULT(idx, 512)),
        util.global_to_uf_dict(ctx, '@pages')[()](util.i64(0), pn, idx) ==
        kernelstate.pages[pn].data(idx))))

    conj.append(z3.ForAll([pn], z3.Implies(is_pn_valid(pn),
        util.global_field_element(ctx, '@page_desc_table', 'pid', pn) ==
        kernelstate.pages[pn].owner)))

    conj.append(z3.ForAll([pn], z3.Implies(is_pn_valid(pn),
        util.global_field_element(ctx, '@page_desc_table', 'type', pn) ==
        kernelstate.pages[pn].type)))


def dmapages_equiv(conj, ctx, kernelstate):
    dmapn = util.FreshBitVec('dmapn', dt.dmapn_t)

    conj.append(z3.ForAll([dmapn], z3.Implies(is_dmapn_valid(dmapn),
        util.global_field_element(ctx, '@dmapage_desc_table', 'type', dmapn) ==
        kernelstate.dmapages[dmapn].type)))

    conj.append(z3.ForAll([dmapn], z3.Implies(is_dmapn_valid(dmapn),
        util.global_field_element(ctx, '@dmapage_desc_table', 'pid', dmapn) ==
        kernelstate.dmapages[dmapn].owner)))


def files_equiv(conj, ctx, kernelstate):
    fn = util.FreshBitVec('fn', dt.fn_t)

    conj.append(z3.ForAll([fn], z3.Implies(is_fn_valid(fn),
        util.global_field_element(ctx, '@file_table', 'type', fn) ==
        kernelstate.files[fn].type)))

    conj.append(z3.ForAll([fn], z3.Implies(is_fn_valid(fn),
        util.global_field_element(ctx, '@file_table', 'refcnt', fn) ==
        kernelstate.files[fn].refcnt())))

    conj.append(z3.ForAll([fn], z3.Implies(is_fn_valid(fn),
        util.global_field_element(ctx, '@file_table', 'value', fn) ==
        kernelstate.files[fn].value)))

    conj.append(z3.ForAll([fn], z3.Implies(is_fn_valid(fn),
        util.global_field_element(ctx, '@file_table', 'omode', fn) ==
        kernelstate.files[fn].omode)))

    conj.append(z3.ForAll([fn], z3.Implies(is_fn_valid(fn),
        util.global_field_element(ctx, '@file_table', 'offset', fn) ==
        kernelstate.files[fn].offset)))


def pci_equiv(conj, ctx, kernelstate):
    devid = util.FreshBitVec('devid', dt.devid_t)

    conj.append(z3.ForAll([devid],
        util.global_to_uf_dict(ctx, '@pci_table')[()](util.i64(0), z3.ZeroExt(64 - devid.size(), devid)) ==
        kernelstate.pci[devid].owner))


def pcipages_equiv(conj, ctx, kernelstate):
    pcipn = util.FreshBitVec('pcipn', dt.pn_t)

    conj.append(z3.ForAll([pcipn], z3.Implies(is_pcipn_valid(pcipn),
        util.global_field_element(ctx, '@pcipages', 'devid', pcipn) ==
        kernelstate.pcipages[pcipn].owner)))

    conj.append(z3.ForAll([pcipn], z3.Implies(is_pcipn_valid(pcipn),
        (util.global_field_element(ctx, '@pcipages', 'valid', pcipn) != 0) ==
        kernelstate.pcipages[pcipn].valid)))


def vectors_equiv(conj, ctx, kernelstate):
    vector = util.FreshBitVec('vector', dt.uint8_t)

    conj.append(z3.ForAll([vector],
        util.global_to_uf_dict(ctx, '@vector_table')[()](util.i64(0),
            z3.ZeroExt(64 - vector.size(), vector)) == kernelstate.vectors[vector].owner))


def io_equiv(conj, ctx, kernelstate):
    port = util.FreshBitVec('port', dt.uint16_t)

    conj.append(z3.ForAll([port],
        util.global_to_uf_dict(ctx, '@io_table')[()](util.i64(0),
            z3.ZeroExt(64 - port.size(), port)) == kernelstate.io[port].owner))


def intremaps_equiv(conj, ctx, kernelstate):
    index = util.FreshBitVec('index', dt.size_t) # intremap index

    conj.append(z3.ForAll([index], z3.Implies(is_intremap_valid(index),
        util.global_field_element(ctx, '@intremap_table', 'state', index) ==
        kernelstate.intremaps[index].state)))

    conj.append(z3.ForAll([index], z3.Implies(is_intremap_valid(index),
        util.global_field_element(ctx, '@intremap_table', 'devid', index) ==
        kernelstate.intremaps[index].devid)))

    conj.append(z3.ForAll([index], z3.Implies(is_intremap_valid(index),
        util.global_field_element(ctx, '@intremap_table', 'vector', index) ==
        kernelstate.intremaps[index].vector)))


def state_equiv(ctx, kernelstate):
    conj = []

    module = sys.modules[__name__]
    for k in kernelstate._meta.keys():
        if not k in kernelstate._structs:
            continue
        getattr(module, k + '_equiv')(conj, ctx, kernelstate)

    conj.append(kernelstate.current == util.global_value(ctx, '@current'))

    conj.append(kernelstate.pages_ptr_to_int == util.global_ptr_to_int(ctx, '@pages'))
    conj.append(kernelstate.proc_table_ptr_to_int == util.global_ptr_to_int(ctx, '@proc_table'))
    conj.append(kernelstate.page_desc_table_ptr_to_int == util.global_ptr_to_int(ctx, '@page_desc_table'))
    conj.append(kernelstate.file_table_ptr_to_int == util.global_ptr_to_int(ctx, '@file_table'))
    conj.append(kernelstate.devices_ptr_to_int == util.global_ptr_to_int(ctx, '@devices'))
    conj.append(kernelstate.dmapages_ptr_to_int == util.global_ptr_to_int(ctx, '@dmapages'))

    conj.append(impl_invariants(ctx))

    return z3.And(*conj)
