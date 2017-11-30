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

import hv6py.kernel.spec.spec as kspec
import hv6py.kernel.spec.datatypes as kdt


def root(state, pid):
    return state.procs[pid].page_table_root


def pg_rw_pn(state, pn, idx):
    return z3.And(
            (state.pages[pn].data(idx) & kdt.PTE_P) != 0,
            (state.pages[pn].pgtable_perm(idx) & kdt.PTE_P) != z3.BitVecVal(0, kdt.size_t),
            (state.pages[pn].pgtable_perm(idx) & kdt.PTE_W) != z3.BitVecVal(0, kdt.size_t),
            state.pages[pn].pgtable_type(idx) == kdt.PGTYPE_PAGE)


def pgwalk_rw(state, pid, idx1, idx2, idx3, idx4):
    pml4 = root(state, pid)
    pdpt = state.pages[pml4].pgtable_pn(idx1)
    pd = state.pages[pdpt].pgtable_pn(idx2)
    pt = state.pages[pd].pgtable_pn(idx3)

    return z3.And(
            pg_rw_pn(state, pml4, idx1),
            pg_rw_pn(state, pdpt, idx2),
            pg_rw_pn(state, pd, idx3),
            pg_rw_pn(state, pt, idx4),
            )


def state_equiv(kernelstate, userstate):
    conj = []

    pid = util.FreshBitVec('pid.eq', kdt.pid_t)

    idx1 = util.FreshBitVec('idx1.eq', kdt.size_t)
    idx2 = util.FreshBitVec('idx2.eq', kdt.size_t)
    idx3 = util.FreshBitVec('idx', kdt.size_t)
    idx4 = util.FreshBitVec('idx', kdt.size_t)

    conj.append(z3.ForAll([pid, idx1, idx2, idx3, idx4],
        z3.Implies(
            z3.And(
                kspec.is_pid_valid(pid),
                kspec.is_status_live(kernelstate.procs[pid].state),

                z3.ULT(idx1, 512),
                z3.ULT(idx2, 512),
                z3.ULT(idx3, 512),
                z3.ULT(idx4, 512),
                ),
            z3.And(
                pgwalk_rw(kernelstate, pid,  idx1, idx2, idx3, idx4) ==
                userstate.writable(pid, idx1, idx2, idx3, idx4)
            ))))

    return z3.And(*conj)

