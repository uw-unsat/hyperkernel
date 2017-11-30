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

import unittest

import z3

from libirpy import solver
from libirpy import util

import hv6py.kernel.spec.spec as kspec
import hv6py.kernel.spec.datatypes as kdt

import datatypes as dt
import spec


# Solver = solver.Solver
Solver = z3.Solver


def mmap_spec(old, pid, va, _perm):
    new = old.copy()

    cond = util.FreshBool('cond')

    idx1, idx2, idx3, idx4 = va

    new.writable = lambda opid, oidx1, oidx2, oidx3, oidx4, oldfn: \
        util.If(z3.And(opid == pid, oidx1 == idx1, oidx2 == idx2, oidx3 == idx3, oidx4 == idx4),
                z3.BoolVal(True),
                oldfn(opid, oidx1, oidx2, oidx3, oidx4))

    return cond, util.If(cond, new, old)


def mmap_impl(old, current, va, perm):
    new = old

    idx1, idx2, idx3, idx4 = va

    # Pick a few pages -- we don't care how they are picked.
    pml4 = old.procs[current].page_table_root
    pdptpn = util.FreshBitVec('pdptpn', kdt.pn_t)
    pdpn = util.FreshBitVec('pdpn', kdt.pn_t)
    ptpn = util.FreshBitVec('ptpn', kdt.pn_t)
    framepn = util.FreshBitVec('framepn', kdt.pn_t)

    condpdpt, new = kspec.sys_alloc_pdpt(new,
            current,
            pml4,
            idx1,
            pdptpn,
            perm)

    condpdpt = z3.Or(
            condpdpt,
            z3.And(
                z3.ULT(idx1, 512),
                new.pages[pml4].pgtable_pn(idx1) == pdptpn,
                (new.pages[pml4].data(idx1) & kdt.PTE_P) != z3.BitVecVal(0, kdt.size_t),
                new.pages[pml4].pgtable_perm(idx1) == perm,
                # The above implies this
                # new.pages[pml4].data(idx1) == (((z3.UDiv(new.pages_ptr_to_int, util.i64(4096)) + pdptpn) << kdt.PTE_PFN_SHIFT) | perm),
            ))

    condpd, new = kspec.sys_alloc_pd(new,
            current,
            pdptpn,
            idx2,
            pdpn,
            perm)

    condpd = z3.Or(
            condpd,
            z3.And(
                z3.ULT(idx2, 512),
                new.pages[pdptpn].pgtable_pn(idx2) == pdpn,
                (new.pages[pdptpn].data(idx2) & kdt.PTE_P) != z3.BitVecVal(0, kdt.size_t),
                new.pages[pdptpn].pgtable_perm(idx2) == perm,
            ))

    condpt, new = kspec.sys_alloc_pt(new,
            current,
            pdpn,
            idx3,
            ptpn,
            perm)

    condpt = z3.Or(
            condpt,
            z3.And(
                z3.ULT(idx3, 512),
                new.pages[pdpn].pgtable_pn(idx3) == ptpn,
                (new.pages[pdpn].data(idx3) & kdt.PTE_P) != z3.BitVecVal(0, kdt.size_t),
                new.pages[pdpn].pgtable_perm(idx3) == perm,
            ))

    condframe, new = kspec.sys_alloc_frame(new,
            current,
            ptpn,
            idx4,
            framepn,
            perm)

    cond = z3.And(condpdpt, condpd, condpt, condframe)

    return cond, util.If(cond, new, old)


class UserSpec(unittest.TestCase):
    def setUp(self):
        self.solver = Solver()

    def _prove(self, cond):
        # self.solver = Solver()
        self.solver.push()
        self.solver.add(z3.Not(cond))
        res = self.solver.check()
        assert res != z3.unknown
        if res != z3.unsat:
            model = self.solver.model()
            print cond
            print model
            self.solver.pop()
            self.assertEquals(model, [])
        self.solver.pop()

    def _solve(self, cond):
        self.solver = Solver()
        self.solver.push()
        self.solver.add(cond)
        res = self.solver.check()
        assert res != z3.unknown
        if res == z3.unsat:
            self.solver.pop()
            assert False

        model = self.solver.model()
        print cond
        print model
        self.solver.pop()


    def test_mmap_writable(self):
        kstate = kdt.KernelState()
        ustate = dt.UserState()

        self.solver.add(spec.state_equiv(kstate, ustate))
        self.solver.add(kspec.spec_invariants(kstate))
        self.solver.add(kspec.spec_lemma_isolation(kstate))

        current = kstate.current

        idx1 = util.FreshBitVec('idx1', kdt.size_t)
        idx2 = util.FreshBitVec('idx2', kdt.size_t)
        idx3 = util.FreshBitVec('idx3', kdt.size_t)
        idx4 = util.FreshBitVec('idx4', kdt.size_t)

        kcond, nkstate = mmap_impl(kstate, current, (idx1, idx2, idx3, idx4), kdt.PTE_P | kdt.PTE_W)
        ucond, nustate = mmap_spec(ustate, current, (idx1, idx2, idx3, idx4), kdt.PTE_P | kdt.PTE_W)

        self._prove(z3.Implies(z3.And(kcond == ucond), spec.state_equiv(nkstate, nustate)))


if __name__ == "__main__":
    unittest.main()
