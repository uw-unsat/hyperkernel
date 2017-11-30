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

import util
import ctx as context

import z3


class TestContext(unittest.TestCase):
    def prove(self, stmt):
        s = z3.Solver()
        s.add(z3.Not(stmt))
        if s.check() != z3.unsat:
            self.assertEquals(s.model(), [])

    def test_push_pop(self):
        ctx = context.newctx()

        x = util.FreshBitVec('x', 32)
        cond = util.FreshBool('cond')

        ctx.globals['%4'] = x

        ctx.push(cond)
        ctx.globals['%4'] += 1
        b1 = ctx.pop()

        ctx.push(z3.Not(cond))
        ctx.globals['%4'] += 2
        b2 = ctx.pop()

        ctx.merge(cond, b1, b2)

        self.prove(z3.Implies(cond, ctx.globals['%4'] == x + 1))
        self.prove(z3.Implies(z3.Not(cond), ctx.globals['%4'] == x + 2))

    def test_nested_push_pop(self):
        ctx = context.newctx()

        x = util.FreshBitVec('x', 32)

        ctx.globals['%4'] = x

        ctx.push()

        ctx.push()
        ctx.globals['%4'] += 1
        self.prove(ctx.globals['%4'] == x + 1)
        b11 = ctx.pop()

        self.prove(ctx.globals['%4'] == x)

        ctx.push()
        ctx.globals['%4'] += 2
        self.prove(ctx.globals['%4'] == x + 2)
        b12 = ctx.pop()

        cond1 = util.FreshBool('cond')
        ctx.merge(cond1, b11, b12)

        self.prove(z3.Implies(cond1, ctx.globals['%4'] == x + 1))
        self.prove(z3.Implies(z3.Not(cond1), ctx.globals['%4'] == x + 2))

        b1 = ctx.pop()

        ctx.push()
        ctx.globals['%4'] += 10
        b2 = ctx.pop()

        cond2 = util.FreshBool('cond')
        ctx.merge(cond2, b1, b2)

        self.prove(z3.Implies(z3.And(cond1, cond2),
                              ctx.globals['%4'] == x + 1))
        self.prove(z3.Implies(z3.And(z3.Not(cond1), cond2),
                              ctx.globals['%4'] == x + 2))
        self.prove(z3.Implies(z3.And(cond1, z3.Not(cond2)),
                              ctx.globals['%4'] == x + 10))
        self.prove(z3.Implies(z3.And(z3.Not(cond1), z3.Not(cond2)),
                              ctx.globals['%4'] == x + 10))

    def _inc(self, ctx):
        ctx.globals['%4'] += 1

    def test_more_nest(self):
        ctx = context.newctx()
        x = util.FreshBitVec('x', 32)
        ctx.globals['%4'] = x

        ctx.push()
        self._inc(ctx)
        self.prove(ctx.globals['%4'] == x + 1)
        ctx.pop()

        ctx.push()
        self._inc(ctx)
        self.prove(ctx.globals['%4'] == x + 1)
        ctx.push()
        self._inc(ctx)
        self.prove(ctx.globals['%4'] == x + 2)
        ctx.push()
        self._inc(ctx)
        self.prove(ctx.globals['%4'] == x + 3)
        ctx.pop()
        self.prove(ctx.globals['%4'] == x + 2)
        ctx.pop()
        self.prove(ctx.globals['%4'] == x + 1)
        ctx.pop()

        self.prove(ctx.globals['%4'] == x)

    def test_nested_restore(self):
        ctx = context.newctx()

        x = util.FreshBitVec('x', 32)

        ctx.globals['%4'] = x

        ctx.push()
        ctx.globals['%4'] += 1
        b1 = ctx.pop()

        self.prove(ctx.globals['%4'] == x)
        self.prove(b1.globals['%4'] == x + 1)

        ctx.restore(b1)

        self.prove(ctx.globals['%4'] == x + 1)

    def test_pcond(self):
        ctx = context.newctx()

        x = util.FreshBitVec('x', 32)
        cond = util.FreshBool('cond')

        ctx.globals['%4'] = x

        ctx.push(cond)
        ctx.globals['%4'] += 1
        print 'cond', ctx.path_condition
        b1 = ctx.pop()

        ctx.push(z3.Not(cond))
        ctx.globals['%4'] += 1
        print 'ncond', ctx.path_condition
        b2 = ctx.pop()

        print 'cond', b1.path_condition
        print 'ncond', b2.path_condition
        print [], ctx.path_condition
        ctx.restore(b1)
        print [], ctx.path_condition

    def _nest(self, ctx, depth):
        assert util.path_condition_implies(ctx, z3.And(*ctx.path_condition))
        assert not util.path_condition_implies(
            ctx, z3.Not(z3.And(*ctx.path_condition)))

        if depth == 0:
            return
        cond = util.FreshBool('cond')
        ctx.push(cond)
        ctx.globals['%4'] += 1
        self._nest(ctx, depth - 1)
        assert util.path_condition_implies(ctx, cond)
        ctx.pop()
        assert not util.path_condition_implies(ctx, cond)
        ctx.push(z3.Not(cond))
        self._nest(ctx, depth - 1)
        assert util.path_condition_implies(ctx, z3.Not(cond))
        ctx.pop()
        assert not util.path_condition_implies(ctx, z3.Not(cond))
        self._nest(ctx, depth - 1)

    def test_nest(self):
        ctx = context.newctx()
        x = util.FreshBitVec('x', 32)
        ctx.globals['%4'] = x
        self._nest(ctx, 5)

    def test_merge1(self):
        ctx = context.newctx()
        x = util.FreshBitVec('x', 32)
        ctx.globals['%4'] = x

        cond = util.FreshBool('cond')

        ctx.push(cond)
        ctx.globals['%4'] += 1
        g1 = ctx.pop()

        ctx.push(z3.Not(cond))
        ctx.globals['%4'] += 1
        g2 = ctx.pop()

        assert not util.path_condition_implies(g1, cond)
        assert not util.path_condition_implies(g2, z3.Not(cond))

        assert not util.path_condition_implies(ctx, cond)
        assert not util.path_condition_implies(ctx, z3.Not(cond))

        ctx.restore(g1)

        assert not util.path_condition_implies(ctx, cond)
        assert not util.path_condition_implies(ctx, z3.Not(cond))

    def test_merge2(self):
        ctx = context.newctx()
        x = util.FreshBitVec('x', 32)
        ctx.globals['%4'] = x

        cond = util.FreshBool('cond')

        ctx.push(cond)
        ctx.globals['%4'] += 1
        g1 = ctx.pop()

        ctx.push(z3.Not(cond))
        ctx.globals['%4'] += 1
        g2 = ctx.pop()

        assert not util.path_condition_implies(g1, cond)
        assert not util.path_condition_implies(g2, z3.Not(cond))

        assert not util.path_condition_implies(ctx, cond)
        assert not util.path_condition_implies(ctx, z3.Not(cond))

        ctx.restore(g2)

        assert not util.path_condition_implies(ctx, cond)
        assert not util.path_condition_implies(ctx, z3.Not(cond))

    def test_merge3(self):
        ctx = context.newctx()
        x = util.FreshBitVec('x', 32)
        ctx.globals['%4'] = x

        cond = util.FreshBool('cond')

        ctx.push(cond)
        ctx.globals['%4'] += 1
        g1 = ctx.pop()

        ctx.push(z3.Not(cond))
        ctx.globals['%4'] += 1
        g2 = ctx.pop()

        assert not util.path_condition_implies(g1, cond)
        assert not util.path_condition_implies(g2, z3.Not(cond))

        assert not util.path_condition_implies(ctx, cond)
        assert not util.path_condition_implies(ctx, z3.Not(cond))

        ctx.merge(cond, g1, g2)

        assert not util.path_condition_implies(ctx, cond)
        assert not util.path_condition_implies(ctx, z3.Not(cond))
