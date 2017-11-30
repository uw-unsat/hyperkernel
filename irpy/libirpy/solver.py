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

import subprocess
import os

import util
import z3
import solver_utils as sutils


CURRENT = os.path.dirname(os.path.realpath(__file__))
Z3_SERVER_FILE = os.path.join(CURRENT, "server.py")


def to_smt2(term):
    s = z3.Solver()
    s.add(term)
    return s.to_smt2()


class ModelProxy(object):
    def __init__(self, model_str, solver):
        self._model = model_str
        self._solver = solver

    def __str__(self):
        return self._model

    def __repr__(self):
        return self._model

    def evaluate(self, term):
        term = term.sexpr()
        return self._solver._call('model_evaluate', term)

    def eval(self, term):
        return self.evaluate(term)


class Solver(object):
    def __init__(self):
        self._proc = subprocess.Popen(['python2', Z3_SERVER_FILE],
                                      stdout=subprocess.PIPE,
                                      stdin=subprocess.PIPE,
                                      # stderr=subprocess.PIPE
                                      )

    def _write(self, command):
        sutils.write_cmd(self._proc.stdin, command)

    def __del__(self):
        try:
            self._proc.kill()
        except:
            pass

    def _call(self, name, *args, **kwargs):
        self._write({'name': name, 'args': args, 'kwargs': kwargs})
        res = self._read()
        if 'return' in res:
            return res['return']
        if 'exc' in res:
            raise RuntimeError(res['exc'])

    def _read(self, **kwargs):
        return sutils.read_cmd(self._proc.stdout)

    def add(self, term):
        term = to_smt2(term)
        return self._call('add', term)

    def set(self, *args, **kwargs):
        return self._call('set', *args, **kwargs)

    def check(self):
        vals = {'sat': z3.sat, 'unsat': z3.unsat, 'unknown': z3.unknown}
        return vals.get(self._call('check'))

    def model(self):
        return ModelProxy(self._call('model'), self)

    def push(self):
        return self._call('push')

    def pop(self):
        return self._call('pop')
