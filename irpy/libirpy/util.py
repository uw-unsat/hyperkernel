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

import types
import sys
import os
import z3

import itypes


if False:
    # A hook swhich spawns an ipdb debugger if an uncaught exception is thrown
    from IPython.core import ultratb
    sys.excepthook = ultratb.FormattedTB(
        mode='Verbose', color_scheme='Linux', call_pdb=1)


# Stupid z3 thing. Z3 requires z3.init to be called with it's library path.
# If it hasn't, it'll throw some exceptions.
Z3_LIBRARY_PATH = os.environ.get('Z3_LIBRARY_PATH')
if Z3_LIBRARY_PATH:
    z3.init(Z3_LIBRARY_PATH)


sys.setrecursionlimit(9999)


def nop(*args, **kwargs):
    pass


setattr(z3.AstRef, '__del__', nop)


# Patch z3 objects with some useful methods
def _is_poison(self):
    """A z3 term is poison if it's name starts with poison, or any of its
    subterms are poison."""
    if self.children():
        for c in self.children():
            if c.is_poison():
                return True
        return False
    else:
        return self.sexpr().startswith('poison.')


setattr(z3.BitVecRef, "type", lambda self: itypes.IntType(self.size()))
setattr(z3.BoolRef, "type", lambda self: itypes.IntType(1))
setattr(z3.BoolRef, "size", lambda self: 1)
setattr(z3.BitVecRef, "is_poison", _is_poison)
setattr(z3.BoolRef, "is_poison", _is_poison)

# Add copy support. Since z3 objects are immutable, copy / deepcopy can just
# return the original object.
setattr(z3.BitVecRef, '__copy__', lambda self: self)
setattr(z3.BitVecRef, '__deepcopy__', lambda self, memo: self)
setattr(z3.BoolRef, '__copy__', lambda self: self)
setattr(z3.BoolRef, '__deepcopy__', lambda self, memo: self)
setattr(z3.FuncDeclRef, '__copy__', lambda self: self)
setattr(z3.FuncDeclRef, '__deepcopy__', lambda self, memo: self)


def _solver_copy(self, memo=None):
    s = z3.Solver()
    s.add(z3.parse_smt2_string(self.to_smt2()))
    return s


# In case of emergencies
# Should probably not be used
def enable_solver_copy():
    setattr(z3.Solver, '__copy__', _solver_copy)
    setattr(z3.Solver, '__deepcopy__', _solver_copy)


def definitely_equal(a, b):
    """
    A conservative equals function. Must return a Python boolean.
    Returns True only if we can definitely determine that a and b are equal.

    A value of False only means they are potentially not equal.
    """
    if type(a) != type(b):
        return False
    container_types = [dict, list, tuple]
    if type(a) in container_types or type(b) in container_types:
        return a is b
    if a is b:
        return True
    if hasattr(a, 'sexpr'):
        if z3.is_func_decl(a) or z3.is_func_decl(b):
            return False
        return z3.is_true(simplify(a == b))
    return a == b


def is_true(cond):
    """Same as z3.is_true but supports python booleans"""
    if hasattr(cond, 'sexpr'):
        return z3.is_true(simplify(cond))
    assert isinstance(cond, bool)
    return cond


def is_false(cond):
    """Same as z3.is_false but supports python booleans"""
    if hasattr(cond, 'sexpr'):
        return z3.is_false(simplify(cond))
    assert isinstance(cond, bool)
    return not cond


def path_condition_implies(ctx, cond, print_model=False):
    """
    Check if current path condition implies some other condition
    """
    solver = ctx['solver']
    solver.push()
    solver.add(z3.Not(cond))
    res = solver.check()
    solver.pop()
    if res == z3.unsat:
        return True
    else:
        if print_model:
            print solver.model()
            print_stacktrace(ctx)
        return False


def If(cond, a, b):
    """
    Conceptually computes ite(cond, a, b) but try to simplify out the ite if
    possible and supports more than just plain z3 datatypes.
    """

    if not z3.is_expr(cond):
        raise ValueError("util.If: Expected cond to be a z3 expression, got {!r}".format(cond))

    cond = simplify(cond)
    if is_true(cond):
        return a
    if is_false(cond):
        return b

    if hasattr(a, 'size') and hasattr(b, 'size'):
        assert a.size() == b.size(
        ), "Can not ite types of different size {} v. {}".format(a.size(), b.size())

    if definitely_equal(a, b):
        return a

    if hasattr(a, 'ite'):
        assert type(a) == type(b), "{} v {}".format(type(a), type(b))
        return a.ite(b, cond)

    is_z3_func = z3.is_func_decl(a) or z3.is_func_decl(b)
    is_py_func = isinstance(a, types.FunctionType) or isinstance(b, types.FunctionType)

    if is_z3_func or is_py_func:
        if not isinstance(a, types.FunctionType) and not isinstance(a, z3.FuncDeclRef):
            a = (lambda outer: lambda *args, **kwargs: outer)(a)
        if not isinstance(b, types.FunctionType) and not isinstance(b, z3.FuncDeclRef):
            b = (lambda outer: lambda *args, **kwargs: outer)(b)
        return lambda *args, **kwargs: If(cond, a(*args, **kwargs), b(*args, **kwargs))

    if isinstance(a, dict) and isinstance(b, dict):
        # For simplicity, only ite dicts with exactly the same keys
        # and only if their values can be ite'd
        assert set(a.keys()) == set(b.keys()), 'Can not ite different dicts {} v. {}'.format(a.keys(), b.keys())
        c = {}
        for k in a.keys():
            c[k] = If(cond, a[k], b[k])
        return c

    if isinstance(a, list):
        a = tuple(a)
    if isinstance(b, list):
        b = tuple(b)

    if isinstance(a, tuple) and isinstance(b, tuple):
        # For simplicity, only ite tuples of same length
        # and only if their values can be ite'd
        assert len(a) == len(b), 'Can not ite tuples of different length {} v. {}'.format(len(a), len(b))
        return tuple([If(cond, ela, elb) for ela, elb in zip(a, b)])

    if not hasattr(a, 'sexpr'):
        raise ValueError("Can not ite object of type {!r}".format(type(a)))

    return z3.If(cond, a, b)


def Implies(a, b, *c):
    if c:
        return z3.Implies(a, z3.And(b, *c))
    else:
        return z3.Implies(a, b)


def partial_eval(ctx, term):
    """Partial eval `term` using path condition from the context"""
    if not hasattr(term, 'decl'):
        return term

    decl = term.decl()

    if str(decl) == 'If':
        cond, a, b = term.children()
        if path_condition_implies(ctx, cond):
            return partial_eval(ctx, a)
        if path_condition_implies(ctx, z3.Not(cond)):
            return partial_eval(ctx, b)
        return If(cond, partial_eval(ctx, a), partial_eval(ctx, b))
    else:
        return decl(*map(lambda subterm: partial_eval(ctx, subterm), term.children()))


def merge(cond, p1, p2):
    """
    Merge p1 and p2 according to cond
    """
    if isinstance(p1, dict):
        assert type(p1) == type(p2), 'Can not merge different types'
        keys = set(p1.keys() + p2.keys())
        out = {}
        for k in keys:
            a = p1.get(k)
            b = p2.get(k)
            if a is None or b is None:
                out[k] = a if b is None else b
                continue
            out[k] = merge(cond, a, b)
        return out

    if isinstance(p1, list):
        assert type(p1) == type(p2), 'Can not merge different types'
        assert len(p1) == len(p2), "Can not merge lists of different lengths"
        out = []
        for a, b in zip(p1, p2):
            out.append(merge(cond, a, b))
        return out

    return If(cond, p1, p2)


def parse_constant_array(values):
    if values[0] == '[':
        assert values[-1] == ']'
        return [int(v.split()[1]) for v in values[1:-1].split(', ')]
    if values[0] == 'c':
        assert values[1] == '"'
        assert values[-1] == '"'
        return map(ord, values[2:-2])


def parse_debug_info(dbg):
    dbg = map(lambda s: s.strip(' ]'), dbg.split('@[ '))
    dbg = map(lambda s: s.split(':', 3), dbg)
    return dbg[0][0], dbg[0][1], dbg[0][2], dbg[1:]


def parse_metadata(meta):
    if meta.startswith('distinct '):
        meta = meta[9:]
    assert meta.startswith("!")
    meta = meta[1:]

    if meta.startswith("{"):
        return list(meta.strip('{}').split(', '))

    name, rest = meta.split('(', 1)

    assert rest[-1] == ')'
    rest = rest[:-1]
    params = rest.split(', ')

    params_dict = {}
    for param in params:
        pname, value = param.split(': ', 1)
        if value.startswith('"'):
            value = value[1:-1]
        else:
            try:
                value = int(value)
            except:
                pass
        params_dict[pname] = value

    return (name, params_dict)


def fresh_name(name):
    if not hasattr(fresh_name, "idx"):
        fresh_name.idx = {}
    n = fresh_name.idx.get(name, 0)
    fresh_name.idx[name] = n + 1
    return name + "." + str(n)


def FreshFunction(name, *args, **kwargs):
    return z3.Function(fresh_name(name), *args, **kwargs)


def FreshBitVec(name, *args, **kwargs):
    return z3.BitVec(fresh_name(name), *args, **kwargs)


def FreshBool(name, *args, **kwargs):
    return z3.Bool(fresh_name(name), *args, **kwargs)


def FreshConst(name, *args, **kwargs):
    return z3.Const(fresh_name(name), *args, **kwargs)


def In(val, lst):
    assert len(lst) > 0, "List must be non-empty"
    return z3.Or(*[val == a for a in lst])


def symbolic_idx(array, idx):
    # TODO: out of bounds?
    v = array[-1]
    for i in range(len(array) - 1, -1, -1):
        v = If(idx == i, array[i], v)
    return v


def partial_update(fn, match_args, value):
    def inner(*args):
        cond = z3.And(*[a == b for a, b in zip(match_args, args)])
        return If(cond, value, fn(*args))
    return inner


def simplify(expression):
    args = {'algebraic_number_evaluator': False,
            'arith_lhs': False,
            'bit2bool': False,
            'blast_distinct': False,
            'blast_distinct_threshold': False,
            'blast_eq_value': False,
            'bv_extract_prop': False,
            'bv_ineq_consistency_test_max': False,
            'bv_ite2id': False,
            'bv_le_extra': False,
            'bv_not_simpl': False,
            'bv_sort_ac': False,
            'bv_trailing': False,
            'bv_urem_simpl': False,
            'bvnot2arith': False,
            'cache_all': False,
            'elim_and': False,
            'elim_rem': False,
            'elim_sign_ext': False,
            'elim_to_real': False,
            'eq2ineq': False,
            'expand_power': False,
            'expand_select_store': False,
            'expand_store_eq': False,
            'expand_tan': False,
            'flat': False,
            'gcd_rounding': False,
            'hi_div0': False,
            'hoist_cmul': False,
            'hoist_mul': False,
            'ite_extra_rules': False,
            'local_ctx': False,
            'local_ctx_limit': False,
            'max_degree': False,
            'max_memory': False,
            'max_steps': False,
            'mul2concat': False,
            'mul_to_power': False,
            'pull_cheap_ite': False,
            'push_ite_arith': False,
            'push_ite_bv': False,
            'push_to_real': False,
            'som': False,
            'som_blowup': False,
            'sort_store': False,
            'sort_sums': False,
            'split_concat_eq': False,
            'udiv2mul': False}
    return z3.simplify(expression, **args)


def global_ptr_to_int(ctx, name):
    pointer = ctx.globals[name]
    return ctx.ptr_to_int[pointer._ref._name]


def global_to_uf_dict(ctx, name, field_name=None):
    pointer = ctx.globals[name]
    return ctx['references'][pointer._ref._name]


def global_to_uf_field(ctx, name, *field_names):
    field_names = list(field_names)
    pointer = ctx.globals[name]
    types = pointer.type().deref(True)._field_names
    fields = []
    while field_names:
        field_name = field_names.pop(0)
        idx = [fn.keys()[0] for fn in types].index(field_name)
        types = types[idx][field_name]
        fields.append(idx)
    return global_to_uf_dict(ctx, name)[tuple(fields)]


def global_field_element(ctx, name, field_name, *elems):
    if not isinstance(field_name, list):
        field_name = [field_name]
    return global_to_uf_field(ctx, name, *field_name)(i64(0), *elems)


def global_value(ctx, name):
    return global_to_uf_dict(ctx, name)[()](i64(0))


def i64(val):
    return z3.BitVecVal(val, 64)


def i32(val):
    return z3.BitVecVal(val, 32)


def i16(val):
    return z3.BitVecVal(val, 16)


def _py2expr(a, ctx=None):
    if isinstance(a, bool):
        return z3.BoolVal(a, ctx)
    if isinstance(a, int):
        return z3.IntVal(a, ctx)
    if isinstance(a, float):
        return z3.RealVal(a, ctx)


def _coerce_expr_merge(s, a):
    if z3.is_expr(a):
        s1 = a.sort()
        if s is None:
            return s1
        if s1.eq(s):
            return s
        elif s.subsort(s1):
            return s1
        elif s1.subsort(s):
            return s
    else:
        return s


def _coerce_exprs(a, b, ctx=None):
    if not z3.is_expr(a) and not z3.is_expr(b):
        a = _py2expr(a, ctx)
        b = _py2expr(b, ctx)
    s = None
    s = _coerce_expr_merge(s, a)
    s = _coerce_expr_merge(s, b)
    a = s.cast(a)
    b = s.cast(b)
    return (a, b)


# From https://stackoverflow.com/questions/22568867/z3-bitvector-overflow-checking-from-python
def bvadd_no_overflow(a, b, signed):
    if a.size() != b.size():
        raise Exception(
            'Sizes do not match for overfow check: {} != {}'.format(a.size(), b.size()))
    assert a.ctx_ref() == b.ctx_ref()
    a, b = _coerce_exprs(a, b)
    return z3.BoolRef(z3.Z3_mk_bvadd_no_overflow(a.ctx_ref(), a.as_ast(), b.as_ast(), signed))


def bvmul_no_overflow(a, b, signed):
    if a.size() != b.size():
        raise Exception(
            'Sizes do not match for overfow check: {} != {}'.format(a.size(), b.size()))
    assert a.ctx_ref() == b.ctx_ref()
    a, b = _coerce_exprs(a, b)
    return z3.BoolRef(z3.Z3_mk_bvmul_no_overflow(a.ctx_ref(), a.as_ast(), b.as_ast(), signed))


def unsigned_saturating_add(a, b):
    overflow = z3.Not(bvadd_no_overflow(a, b, signed=False))
    n = a.size()
    return If(overflow,
              z3.BitVecVal(2 ** n, n) - 1,
              a + b)


def as_long(i):
    if hasattr(i, 'sexpr'):
        i = simplify(i)
        assert hasattr(i, 'as_long'), "Z3 object must be a concrete integer"
        return i.as_long()
    if isinstance(i, int):
        return i
    assert False, "Don't know how to convert {!r} to long".format(i)


def print_stacktrace(ctx,  stacktrace=None):
    def get(k):
        return frame[k] if k in frame else '?'

    if stacktrace is None:
        stacktrace = ctx['stacktrace']

    for frame in stacktrace:
        inlined = map(lambda ns: ':'.join(ns), get('inlined'))
        inlined = ' @[ '.join(inlined) + ' ] ' * len(inlined)
        print "  In function {}:{}:{}:{} {}{}".format(get('file'),
                                                      get('function'), get('line'), get('column'), '@[ ' if inlined else "", inlined)


def as_bool(v):
    if z3.is_bool(v):
        return v
    assert v.size() == 1
    return If(v == z3.BitVecVal(1, 1), z3.BoolVal(True), z3.BoolVal(False))


class NoReturn(BaseException):
    pass
