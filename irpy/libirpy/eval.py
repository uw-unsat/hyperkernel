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

class BaseIRPyEvaluator(object):
    #############################
    # Binary Ops
    #############################
    def add(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def sub(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def mul(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def udiv(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def sdiv(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def urem(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def srem(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    #############################
    # Logical Ops
    #############################
    def shl(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def lshr(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def ashr(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def and_(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def or_(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def xor(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    #############################
    # Memory Ops
    #############################
    def alloca(self, ctx, return_type, size, size_type):
        raise NotImplementedError()

    def load(self, ctx, return_type, target, target_type):
        raise NotImplementedError()

    def store(self, ctx, return_type, target, target_type, dest, dest_type):
        raise NotImplementedError()

    def get_element_ptr(*args):
        raise NotImplementedError()
    getelementptr = get_element_ptr

    #############################
    # Cast Ops
    #############################
    def trunc(self, ctx, return_type, a, atype):
        raise NotImplementedError()

    def zext(self, ctx, return_type, a, atype):
        raise NotImplementedError()

    def sext(self, ctx, return_type, a, atype):
        raise NotImplementedError()

    def ptr_to_int(*args):
        raise NotImplementedError()
    ptrtoint = ptr_to_int

    def int_to_ptr(*args):
        raise NotImplementedError()
    inttoptr = int_to_ptr

    def bitcast(self, ctx, return_type, value, value_type):
        raise NotImplementedError()

    #############################
    # Other Ops
    #############################
    def constant_int(self, ctx, value, size):
        raise NotImplementedError()

    def constant_data_array(self, ctx, value, size):
        raise NotImplementedError()

    def constant_array(self, ctx, value, size):
        raise NotImplementedError()

    def constant_aggregate_zero(self, ctx, type, value):
        raise NotImplementedError()

    def constant_pointer_null(self, ctx, type):
        raise NotImplementedError()

    def declare_global_variable(self, ctx, name, global_type, value=None, value_type=None):
        if value_type is None:
            value_type = global_type.deref()
        raise NotImplementedError()

    def declare_global_constant(self, ctx, name, global_type, value=None, value_type=None):
        if value_type is None:
            value_type = global_type.deref()
        raise NotImplementedError()

    def call(self, ctx, return_type, *args):
        raise NotImplementedError()

    def select(self, ctx, return_type, cond, cond_type, trueval, trueval_type, falseval, falseval_type):
        raise NotImplementedError()

    def branch(self, ctx, cond, cond_type, iftrue, iffalse):
        raise NotImplementedError()

    def switch(self, ctx, value, value_type, default_case, *cases):
        raise NotImplementedError()

    def global_value(self, ctx, return_type, name):
        raise NotImplementedError()

    def asm(self, ctx, inline_assembly):
        raise NotImplementedError()

    def debug_loc(self, debug):
        pass

    #############################
    # Predicates
    #############################
    def eq(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def ne(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def ugt(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def uge(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def ult(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def ule(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def sgt(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def sge(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def slt(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()

    def sle(self, ctx, return_type, a, atype, b, btype):
        raise NotImplementedError()
