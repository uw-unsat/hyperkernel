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

import util
import z3
import copy


class Reference(object):
    def __init__(self, name, itype):
        self._type = itype
        self._name = name

    def __eq__(self, other):
        return self._type == other._type and self._name == other._name

    def build_field_tuple_and_path(self, ctx, path):
        typ = self._type
        fields = []
        newpath = []
        while len(path) > 0:
            if typ.is_int():
                assert False, "Can't have base type if there is more left in path"
            elif typ.is_array() or typ.is_pointer():
                if typ.is_array():
                    if not util.path_condition_implies(ctx, z3.ULT(path[0],
                        typ.length()), print_model=True):
                        util.print_stacktrace(ctx)
                        raise IndexError(
                            "Can not prove index %s is within array bounds %s"
                            % (path[0], typ.length()))

                if typ.is_pointer():
                    if not util.path_condition_implies(ctx, path[0] == 0):
                        util.print_stacktrace(ctx)
                        raise RuntimeError("Pointer arithmetic not supported")

                typ = typ.deref()
                newpath.append(path[0])
            elif typ.is_struct():
                field = util.simplify(path[0]).as_long()
                fields.append(field)
                typ = typ.field(field)
            else:
                assert False, "Unhandled case"
            path = path[1:]
        return tuple(fields), newpath

    def read(self, ctx, path):
        fields_tup, path = self.build_field_tuple_and_path(ctx, path)
        ctx['accessed'].add(self._name)
        return ctx['references'][self._name][fields_tup](*path)

    def write(self, ctx, path, value):
        fields_tup, path = self.build_field_tuple_and_path(ctx, path)
        oldf = ctx['references'][self._name][fields_tup]
        newf = util.partial_update(oldf, path, value)
        ctx['accessed'].add(self._name)
        ctx['references'][self._name][fields_tup] = newf


class BitcastPointer(object):
    def __init__(self, ptr, type, geps=None):
        assert isinstance(ptr, Pointer)
        self._ptr = ptr
        self._type = type
        if geps is None:
            geps = []
        self._geps = geps

    def __repr__(self):
        return "BitcastPointer<{!r} - {!r}>".format(self._ptr, self._type)

    def __eq__(self, other):
        return (self._type == other._type and self._ptr == other._ptr
                and self._geps == other._geps)

    def type(self):
        return self._type

    def getelementptr(self, ctx, *idxs, **kwargs):
        type = kwargs.pop('type', self._type)
        assert type == self._type
        assert kwargs == {}, "Unexpected argument {}".format(kwargs)
        assert len(idxs) > 0, "Can not have empty gep"
        geps = self._geps[:]
        geps.append((idxs, self._type))
        return BitcastPointer(self._ptr, type, geps=geps)

    def canonical_path(self):
        if not self._geps:
            return self._ptr.canonical_path()
        else:
            raise NotImplementedError("Can not canonicalize gep'd bitcast ptr")

    def read(self, ctx):
        raise NotImplementedError()

    def write(self, ctx, value):
        raise NotImplementedError()


class Pointer(object):
    def __init__(self, ref, geps=None, type=None):
        assert ref is None or isinstance(
            ref, Reference), "Pointer must point to a reference or None"
        if geps is None:
            geps = []
        self._geps = geps
        self._ref = ref
        self._type = type

    def __repr__(self):
        return "Pointer<{!r} - {!r}>".format(self._ref, self._type)

    def __eq__(self, other):
        return (self._geps == other._geps and self._ref == other._ref
                and self.type() == other.type())

    def type(self):
        return self._type

    def ite(self, other, cond):
        p1 = copy.deepcopy(self)
        p2 = copy.deepcopy(other)
        assert p1.type() == p2.type()

        def inner_write(self, ctx, value):
            p1.write(ctx, util.If(cond, value, p1.read(ctx)))
            p2.write(ctx, util.If(z3.Not(cond), value, p2.read(ctx)))

        def inner_read(self, ctx):
            return util.If(cond, p1.read(ctx), p2.read(ctx))

        def inner_getelementptr(self, ctx):
            assert False, "GEP on ite pointer"
        p = Pointer(None, type=p1.type())
        p.write = type(Pointer.write)(inner_write, p, Pointer)
        p.read = type(Pointer.read)(inner_read, p, Pointer)
        p.getelementptr = type(Pointer.getelementptr)(
            inner_getelementptr, p, Pointer)
        return p

    def bitcast(self, typ):
        return BitcastPointer(self, typ)

    # Just apppend the gep
    def getelementptr(self, ctx, *idxs, **kwargs):
        type = kwargs.pop('type', self._type)
        assert kwargs == {}, "Unexpected argument {}".format(kwargs)
        assert len(idxs) > 0, "Cannot have empty gep"
        geps = self._geps[:]
        geps.append(idxs)
        return Pointer(self._ref, geps, type=type)

    def canonical_path(self):
        path = [util.i64(0)]
        for gep in self._geps:
            assert len(gep) > 0, "Cannot have empty gep"
            if hasattr(gep[0], 'sexpr') and gep[0].size() != 64:
                path[-1] = path[-1] + z3.BitVecVal(util.as_long(gep[0]), 64)
            else:
                path[-1] = path[-1] + gep[0]
            path += gep[1:]
        return map(util.simplify, path)

    def read(self, ctx):
        return self._ref.read(ctx, self.canonical_path())

    def write(self, ctx, value):
        return self._ref.write(ctx, self.canonical_path(), value)


def init_ref(ctx, ref):
    d = {}

    def _fresh_ref(typ, tup, depth, name=None):
        if typ.is_pointer() and depth != 0:
            d[tup] = None
        if typ.is_int() or (typ.is_pointer() and depth != 0):
            args = [z3.BitVecSort(64)] * depth + [z3.BitVecSort(typ.size())]
            if name is None:
                name = ref._name
            else:
                name = ref._name + "->" + name
            d[tup] = z3.Function(util.fresh_name(name), *args)
        elif typ.is_struct():
            for i in range(len(typ.fields())):
                _fresh_ref(typ.field(i), tup + (i,), depth, typ.field_name(i))
        elif typ.is_array() or typ.is_pointer():
            _fresh_ref(typ.deref(), tup, depth + 1)
        else:
            assert False, "unhandled case"
    _fresh_ref(ref._type, (), 0)
    assert ref._name not in ctx.references, "Overwriting a reference, this is probably a bug"
    ctx['references'][ref._name] = d


def fresh_ptr(ctx, name, type):
    ref = Reference(name, type)
    init_ref(ctx, ref)
    return Pointer(ref, type=type)
