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
import util
import z3

from solver_utils import write_cmd, read_cmd


class Server(object):
    def __init__(self):
        self._s = z3.Solver()

    def _write(self, command):
        return write_cmd(sys.stdout, command)

    def _read(self):
        return read_cmd(sys.stdin)

    def run(self):
        while True:
            self.handle_cmd()

    def handle_cmd(self):
        cmd = self._read()
        if not cmd:
            sys.exit(0)
        try:
            res = {'return': getattr(self, cmd['name'])(*cmd['args'], **cmd['kwargs'])}
        except Exception, e:
            res = {'exc': repr(e)}
        self._write(res)

    def add(self, term):
        self._s.add(z3.parse_smt2_string(term))

    def set(self, **kwargs):
        self._s.set(**{str(k): v for k, v in kwargs.items()})

    def check(self):
        return str(self._s.check())

    def push(self):
        return str(self._s.push())

    def pop(self):
        return str(self._s.pop())

    def model(self):
        return str(self._s.model())

    def model_evaluate(self, term):
        model = self._s.model()

        for t in model.decls():
            if str(t) == term:
                term = t()
                break
        return str(self._s.model().evaluate(term))


if __name__ == '__main__':
    Server().run()
