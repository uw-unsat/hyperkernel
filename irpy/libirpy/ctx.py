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

import copy
import util
import z3eval
import z3
#from z3 import Solver
from solver import Solver


_solver = Solver()
_path_condition = []
_snapshots = []


class Context(object):
    def __init__(self, **kwargs):
        self.globals = kwargs.get('globals', {})
        self.locals = kwargs.get('locals', [])
        self.stacktrace = kwargs.get('stacktrace', [])
        self.metadata = kwargs.get('metadata', {})
        self.references = kwargs.get('references', {})

        self.ptr_to_int = kwargs.get('ptr_to_int', {})

        self.types = kwargs.get('types', {})

        self.side_conditions = kwargs.get('side_conditions', {})

        self.eval = kwargs.get('eval')

        self.depth = kwargs.get('depth', 0)
        self.prune_depth = kwargs.get('prune_depth', 0)

        self.accessed = kwargs.get('accessed', set())

    def __repr__(self):
        return repr(self.__dict__)

    def __getitem__(self, key):
        return getattr(self, key)

    def __setitem__(self, key, value):
        return setattr(self, key, value)

    def add_assumption(self, assumption):
        self.solver.add(assumption)
        self.path_condition.append(assumption)

    def populate_globals(self, module):
        for k in dir(module):
            if k.startswith('func_'):
                gkey = '@' + k[len('func_'):]
                self.globals[gkey] = getattr(module, k)

    @property
    def stack(self):
        return self.locals[-1]

    @property
    def solver(self):
        return _solver

    @solver.setter
    def solver(self, s):
        global _solver
        _solver = s

    @property
    def path_condition(self):
        return _path_condition

    @property
    def _snapshots(self):
        return _snapshots

    def snapshot(self):
        return copy.deepcopy(self)

    def restore(self, c):
        self.globals = c.globals
        self.locals = c.locals
        self.references = c.references
        self.accessed = c.accessed

    def push(self, path_condition=z3.BoolVal(True)):
        c = self.snapshot()
        self._snapshots.append(c)

        self.solver.push()
        self.solver.add(path_condition)
        self.path_condition.append(path_condition)
        self.depth += 1

    def pop(self):
        self.depth -= 1
        self.path_condition.pop()
        self.solver.pop()

        ret = self.snapshot()

        c = self._snapshots.pop()
        self.restore(c)

        return ret

    def merge(self, cond, c1, c2):
        self.globals = util.merge(cond, c1.globals, c2.globals)
        self.locals = util.merge(cond, c1.locals, c2.locals)
        self.references = util.merge(cond, c1.references, c2.references)
        self.accessed = c1.accessed.union(c2.accessed)

        assert self.path_condition == c1.path_condition
        assert self.path_condition == c2.path_condition

        assert self.side_conditions == c1.side_conditions
        assert self.side_conditions == c2.side_conditions

    def call(self, fn, *args):
        try:
            self.locals.append({})
            self.stacktrace.append({})
            return self.globals[fn](self, *args)
        finally:
            self.stacktrace.pop()
            self.locals.pop()


def newctx():
    solver = Solver()
    solver.set(AUTO_CONFIG=False)

    return Context(
        globals={},
        solver=solver,
        eval=z3eval.Z3IRPyEval(),
        prune_depth=5,
        accessed=set(),
    )


def initctx(ctx, module):
    module._init_metadata(ctx)
    module._init_types(ctx)
    module._init_globals(ctx)
    ctx.populate_globals(module)
