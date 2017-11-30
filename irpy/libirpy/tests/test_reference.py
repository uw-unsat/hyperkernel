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
import util
import datatypes as dt
import itypes as it
from ctx import newctx


class TestReference(unittest.TestCase):
    def setUp(self):
        self._ctx = newctx()

    def assertIsZ3(self, v):
        self.assertTrue(hasattr(v, 'sexpr'))

    def assertIsNotZ3(self, v):
        self.assertFalse(hasattr(v, 'sexpr'))

    def assertIsConcrete(self, v):
        self.assertTrue(hasattr(v, 'as_long'))

    def assertIsSymbolic(self, v):
        self.assertFalse(hasattr(v, 'as_long'))

    def type(self, t):
        return it.parse_type(self._ctx, t)

    def test_pointer_to_int(self):
        ctx = newctx()
        p = dt.fresh_ptr(ctx, util.fresh_name(
            'p'), it.PointerType(it.IntType(64)))
        print ctx['references'][p._ref._name]
        p.write(ctx, util.i64(4))
        self.assertEquals(4, p.read(ctx).as_long())

    def test_struct_of_ints(self):
        ctx = newctx()
        point = it.StructType('Point', [it.IntType(64), it.IntType(64)])
        q = dt.fresh_ptr(ctx, util.fresh_name('q'), it.PointerType(point))
        print ctx['references'][q._ref._name]
        x = util.FreshBitVec('x', 64)
        q.getelementptr(ctx, util.i64(0), util.i64(0)).write(ctx, x)
        s = z3.Solver()
        s.add(z3.Not(x == q.getelementptr(ctx, util.i64(0), util.i64(0)).read(ctx)))
        self.assertEquals(s.check(), z3.unsat)

    def test_struct_of_structs_of_ints(self):
        ctx = newctx()
        point = it.StructType('Point', [it.IntType(64), it.IntType(64)])
        metapoint = it.StructType('metapoint', [point, point])
        r = dt.fresh_ptr(ctx, util.fresh_name('r'), it.PointerType(metapoint))
        print ctx['references'][r._ref._name]
        x = util.FreshBitVec('x', 64)
        q = r.getelementptr(ctx, util.i64(0), util.i64(1))
        q.getelementptr(ctx, util.i64(0), util.i64(0)).write(ctx, x)
        s = z3.Solver()
        s.add(z3.Not(x == q.getelementptr(ctx, util.i64(0), util.i64(0)).read(ctx)))
        self.assertEquals(s.check(), z3.unsat)

    def test_read_read_same(self):
        # "Helgi's problem"
        ctx = newctx()
        p = dt.fresh_ptr(ctx, util.fresh_name(
            'p'), it.PointerType(it.IntType(64)))
        self.assertEquals(p.getelementptr(ctx, util.i64(0)).read(
            ctx), p.getelementptr(ctx, util.i64(0)).read(ctx))

    def test_array_of_stucts(self):
        ctx = newctx()
        points = it.ArrayType(10, it.StructType(
            'Point', [it.IntType(64), it.IntType(64)]))
        p = dt.fresh_ptr(ctx, util.fresh_name('p'), points)
        y = util.FreshBitVec('y', 64)
        x = util.FreshBitVec('x', 64)
        # x and y are within bounds
        ctx['solver'].add(z3.ULT(x, 10))
        ctx['solver'].add(z3.ULT(y, 10))
        p.getelementptr(ctx, x, util.i64(0)).write(ctx, x)
        s = z3.Solver()
        s.add(z3.Not(z3.Implies(x == y, p.getelementptr(
            ctx, y, util.i64(0)).read(ctx) == y)))
        self.assertEquals(s.check(), z3.unsat)

    def test_array_bounds(self):
        ctx = newctx()
        points = it.ArrayType(10, it.IntType(64))
        p = dt.fresh_ptr(ctx, util.fresh_name('p'), points)
        p = p.getelementptr(ctx, 50)
        with self.assertRaises(IndexError):
            p.write(ctx, util.i64(10))

    def test_pointer_ite(self):
        ctx = newctx()
        p1 = dt.fresh_ptr(ctx, util.fresh_name(
            'p'), it.PointerType(it.IntType(64)))
        p2 = dt.fresh_ptr(ctx, util.fresh_name(
            'p'), it.PointerType(it.IntType(64)))
        cond = z3.Bool('cond')
        p3 = util.If(cond, p1, p2)
        p3.write(ctx, util.i64(4))
        s = z3.Solver()
        s.add(z3.Not(z3.Implies(cond, p1.read(ctx) == util.i64(4))))
        self.assertEquals(s.check(), z3.unsat)

        s = z3.Solver()
        s.add(z3.Not(z3.Implies(z3.Not(cond), p2.read(ctx) == util.i64(4))))
        self.assertEquals(s.check(), z3.unsat)

    def test_pointer_pointer(self):
        ctx = newctx()
        p1 = dt.fresh_ptr(ctx, util.fresh_name(
            'p'), it.PointerType(it.PointerType(it.IntType(64))))
        p2 = dt.fresh_ptr(ctx, util.fresh_name(
            'p'), it.PointerType(it.IntType(64)))
        p1.write(ctx, p2)
        p2.write(ctx, util.i64(10))
        self.assertEquals(p2.read(ctx).as_long(),
                          p1.read(ctx).read(ctx).as_long())

    def test_pointer_pointer_pointer(self):
        ctx = newctx()
        a = dt.fresh_ptr(ctx, util.fresh_name(
            'a'), it.PointerType(it.PointerType(it.IntType(64))))
        b = dt.fresh_ptr(ctx, util.fresh_name(
            'b'), it.PointerType(it.IntType(64)))
        c = dt.fresh_ptr(ctx, util.fresh_name(
            'c'), it.PointerType(it.IntType(64)))
        cond = z3.Bool('cond')
        p = util.If(cond, b, c)
        a.write(ctx, p)

        print a.read(ctx).read(ctx)
