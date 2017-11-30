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

import itypes as it


class TestReference(unittest.TestCase):
    def test_type_parsing(self):
        ctx = {}
        ctx['types'] = {}

        it.declare_struct_type(ctx, 'struct.trap_regs', 'i64', 'i64', 'i64', 'i64', 'i64',
                               'i64', 'i64', 'i64', 'i64', 'i64', 'i64', 'i64', 'i64', 'i64', 'i64', '[8 x i8]',)
        it.declare_struct_type(ctx, 'struct.proc', 'i32', 'i64', 'i64',
                               '[16 x i64]', 'i64', '%struct.trap_regs = type { i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, [8 x i8] }', 'i64', '[8 x i8]',)

        self.assertEquals(it.parse_type(ctx, 'i64***'),
                          it.PointerType(it.PointerType(it.PointerType(it.IntType(64)))))
        it.parse_type(ctx, 'i64***')
        it.parse_type(ctx, '[0 x i8]')
        it.parse_type(ctx, '[0 x i8]*')
        it.parse_type(ctx, '[3 x [4 x i32]]')
        it.parse_type(ctx, '[3 x [4 x i32]]')
        it.parse_type(ctx, '[3 x [4 x i32]]')
        it.parse_type(ctx, '%mytype = type { %struct.trap_regs*, i32 }')
