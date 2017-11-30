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


POINTER_SIZE = 64


class Type(object):
    def size(self):
        raise NotImplementedError()

    def is_pointer(self):
        return False

    def is_ref(self):
        return False

    def is_value(self):
        raise NotImplementedError()

    def is_composite(self):
        raise NotImplementedError()

    def is_array(self):
        return False

    def is_function(self):
        return False

    def is_struct(self):
        return False

    def is_int(self):
        return False

    def is_mutable(self):
        raise NotImplementedError()

    def is_immutable(self):
        return not self.is_mutable()

    def __eq__(self, other):
        if self.__class__ != other.__class__:
            return False
        return self._eq(other)


class ValueType(Type):
    def is_pointer(self):
        return False

    def is_value(self):
        return True

    def is_mutable(self):
        return False

    def is_composite(self):
        return False

    def deref(self, star=False):
        if star:
            return self
        raise ValueError("Can not dereference a value type")


class CompositeValueType(ValueType):
    def is_composite(self):
        return True


class VoidType(ValueType):
    def __repr__(self):
        return "<VoidType>"

    def size(self):
        return 0

    def _eq(self, other):
        return True


class VarArgType(ValueType):
    def __repr__(self):
        return "<VarArgType>"

    def size(self):
        return 0

    def _eq(self, other):
        return True


class IntType(ValueType):
    def __init__(self, bitwidth):
        self.bitwidth = bitwidth

    def __repr__(self):
        return "<IntType {}>".format(self.size())

    def size(self):
        return self.bitwidth

    def is_int(self):
        return True

    def _eq(self, other):
        return self.size() == other.size()


class StructType(CompositeValueType):
    def __init__(self, name, fields, field_names=None, size=None):
        self._name = name
        self._fields = tuple(fields)
        self._field_names = field_names
        self._size = size

    def size(self):
        if self._size:
            return self._size
        else:
            return sum([s.size() for s in self._fields])

    def fields(self):
        return self._fields

    def field(self, i):
        return self._fields[i]

    def field_name(self, i):
        if self._field_names is None:
            return None
        if len(self._field_names) < i:
            return None
        assert len(self._field_names[i]) == 1
        name = self._field_names[i].keys()[0]
        return self._name + '::' + name

    def field_names(self):
        return map(lambda x: x.keys()[0], self._field_names)

    def is_struct(self):
        return True

    def _eq(self, other):
        return self._name == other._name

    def is_composite(self):
        return True

    def __repr__(self):
        return "<StructType %{} {}>".format(self._name, self._fields)


class ArrayType(CompositeValueType):
    def __init__(self, size, of_type):
        self._size = size
        self._type = of_type

    def __repr__(self):
        return "<ArrayType [{} x {!r}]>".format(self._size, self._type)

    def is_array(self):
        return True

    def is_ref(self):
        return True

    def deref(self, star=False):
        inner = self._type
        if star and inner.is_ref():
            return inner.deref(True)
        return self._type

    def _eq(self, other):
        return self._size == other._size and self._type == other._type

    def is_composite(self):
        return True

    def length(self):
        return self._size

    def size(self):
        return self._size * self._type.size()


class FunctionType(CompositeValueType):
    def __init__(self, return_type, arguments):
        self._return_type = return_type
        self._arguments = tuple(arguments)

    def _eq(self, other):
        return self._return_type == other._return_type and self._arguments == other._arguments

    def is_function(self):
        return True

    def return_type(self):
        return self._return_type

    def __repr__(self):
        return "<FunctionType {!r} {!r}]>".format(self._return_type, self._arguments)


class PointerType(Type):
    def __init__(self, deref):
        assert isinstance(deref, Type), 'Argument must be a type'
        self._deref = deref

    def __repr__(self):
        return "<PointerType {!r}>".format(self.deref())

    def _eq(self, other):
        return self.deref() == other.deref()

    def is_composite(self):
        return False

    def is_ref(self):
        return True

    def deref(self, star=False):
        inner = self._deref
        if star and inner.is_ref():
            return inner.deref(True)
        return self._deref

    def size(self):
        return POINTER_SIZE

    def is_pointer(self):
        return True

    def is_value(self):
        return False

    def is_mutable(self):
        return True


def parse_type(ctx, typ):
    assert len(typ) > 0, 'Type string must have length > 0'
    if typ[-1] == '*':
        return PointerType(parse_type(ctx, typ[:-1]))

    if typ == 'void':
        return VoidType()
    if typ == '...':
        return VarArgType()
    if ' ' in typ and '(' in typ and ')' in typ:
        ret, args = typ.split(' (', 1)
        assert args[-1] == ')'
        args = args[:-1]
        if not args.strip():
            args = []
        else:
            args = [parse_type(ctx, t) for t in args.split(', ')]

        return FunctionType(parse_type(ctx, ret), args)
    if typ[0] == '[':
        assert typ[-1] == ']', 'Invalid array type'
        typ = typ[1:-1]
        size, subtyp = typ.split(' x ', 1)
        size = int(size)
        return ArrayType(size, parse_type(ctx, subtyp))
    if typ[0] == 'i':
        bitwidth = int(typ.lstrip('i'))
        return IntType(bitwidth)
    if typ[0] == '%':
        if ' = type ' in typ:
            name, fields = typ.split(' = ', 1)
            assert name[0] == '%'
            name = name[1:]
            assert fields.startswith('type {')
            assert fields[-1] == '}'
            fields = fields[7:-1].strip()
            fields = fields.split(', ')
            fields = [parse_type(ctx, field) for field in fields]
            return StructType(name, fields)
        return ctx['types'][typ]
    raise ValueError("Could not parse type: {!r}".format(typ))


def _get_struct_meta(ctx, struct_name):
    for k, v in ctx.metadata.items():
        if isinstance(v, tuple):
            if v[0] == 'DICompositeType' and v[1].get('name') == struct_name[7:]:
                return v[1]


def _get_struct_fields(ctx, struct_meta):
    field_names = []
    elements = ctx.metadata.get(struct_meta.get('elements'))
    for element in elements:
        field_name = ctx.metadata.get(element)
        fname = field_name[1].get('name')
        key = tuple()
        if 'baseType' in field_name[1]:
            inner = ctx.metadata.get(field_name[1]['baseType'])
            if inner[0] == 'DICompositeType' and inner[1].get('tag') == 'DW_TAG_structure_type':
                key = _get_struct_fields(ctx, inner[1])
        field_names.append({fname: key})
    return field_names


def declare_struct_type(ctx, name, *fields):
    struct_meta = _get_struct_meta(ctx, name)
    if struct_meta:
        field_names = _get_struct_fields(ctx, struct_meta)
        struct_size = struct_meta.get('size')
    else:
        field_names = None
        struct_size = None

    fields = [parse_type(ctx, field) for field in fields]
    s = StructType(name, fields, field_names=field_names, size=struct_size)
    ctx['types']['%' + name] = s
    return s


def construct_type(ctx, value):
    if hasattr(value, 'sexpr'):
        return IntType(value.size())
    if hasattr(value, 'type'):
        return value.type()
    raise RuntimeError(
        "Don't know how to construct type from value: {!r}".format(value))


def has_type(ctx, value, typ):
    v = construct_type(ctx, value) == typ
    if not v:
        print construct_type(ctx, value), typ
    return v


def integer_size(typ):
    assert isinstance(
        typ, IntType), "Expecting an integer, got {!r}".format(typ)
    return typ.size()


def array_bounds(array_type):
    assert array_type.is_array()
    bounds = []
    while array_type.is_array():
        bounds.append(array_type.length())
        array_type = array_type.deref()

    return bounds[::-1]
