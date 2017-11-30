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

import collections
import copy
import z3
import types

import libirpy.util as util


_order = 0


class Accessor(object):
    def __init__(self, field, instance, imap):
        self._field = field
        self._instance = instance
        self._imap = imap

    def __repr__(self):
        return "Partial application of {!r}{!r}".format(self._instance._fields[self._field], tuple(self._instance._path))

    def __call__(self, *args):
        instance = self._instance
        for i in args:
            instance = instance[i]
        return self._imap(instance)

    def __getattr__(self, attr):
        val = getattr(self._imap, attr)
        if isinstance(val, types.MethodType):
            return lambda *args, **kwargs: val(self._instance, *args, **kwargs)
        else:
            return val

    def __getitem__(self, arg):
        return Accessor(self._field, self._instance[arg], self._imap)

    def __setitem__(self, arg, value):
        return setattr(self._instance[arg], self._field, value)

    def __iadd__(self, value):
        return self._imap.__iadd__(self._instance, value)

    def __sub__(self, value):
        return self._imap.__isub__(self._instance, value)


class AbstractMap(object):
    def __init__(self, *types):
        global _order
        self._order = _order
        _order += 1

        self._name = None
        self._arity = len(types) - 1
        self._types = types

    def get_arity(self):
        return self._arity

    def get_types(self):
        return self._types

    def invariants(self):
        return []

    def initial(self, instance):
        pass

    def _init(self, obj, name, prefix=None):
        if prefix:
            self._prefix = prefix + '_'
        else:
            self._prefix = ''

        self._name = name
        obj._fields[self._name] = self.new()

    def __get__(self, instance, owner=None):
        f = instance._fields[self._name]

        if len(instance._path) < self.get_arity():
            return Accessor(self._name, instance, self)
        elif self._arity == len(instance._path):
            return self.get(f, instance._path)
        else:
            raise TypeError('Too many arguments to function: expected arguments: {!r}'.format(self._types))

    def __call__(self, instance):
        return self.__get__(instance)

    def __set__(self, instance, value):
        assert len(instance._path) <= self.get_arity()
        instance._fields[self._name] = self.set(instance._fields[self._name], instance._path, value)

    def __iadd__(self, instance, value):
        return self.iadd(instance._fields[self._name], instance._path, value)

    def __isub__(self, instance, value):
        return self.isub(instance._fields[self._name], instance._path, value)

    def new(self):
        raise NotImplementedError()

    def get(self):
        raise NotImplementedError()

    def iadd(self):
        raise NotImplementedError()

    def isub(self):
        raise NotImplementedError()


class StructMeta(type):
    def __new__(cls, name, parents, dct):
        meta = collections.OrderedDict()
        for k, v in sorted(dct.items(), key=lambda v: getattr(v[1], '_order', float('inf'))):
            if hasattr(v, '_init'):
                meta[k] = v
            if getattr(v, '__metaclass__', None) == cls:
                meta[k] = v.__class__
                del dct[k]
        dct['_meta'] = meta
        return super(StructMeta, cls).__new__(cls, name, parents, dct)


class Struct(object):
    __frozen = False
    __metaclass__ = StructMeta

    def __init__(self):
        global _order
        self._order = _order
        _order += 1

    def copy(self):
        return copy.deepcopy(self)

    def _init(self, parent, name):
        self._fields = {}
        self._structs = collections.OrderedDict()
        self._path = []

        for k, v in self._meta.items():
            if isinstance(v, type):
                self._structs[k] = v()
                self._structs[k]._init(self, k)
            else:
                v._init(self, k, prefix=name)

        for k, v in self._structs.items():
            v = copy.copy(v)
            self._structs[k] = v
            v._init(self, k)
        self.__frozen = True

    def __getattribute__(self, arg):
        if arg.startswith('_'):
            return super(Struct, self).__getattribute__(arg)

        if arg not in self._meta:
            return super(Struct, self).__getattribute__(arg)

        if arg in self._structs:
            return self._structs[arg]
        else:
            return super(Struct, self).__getattribute__(arg)

    def __setattr__(self, attribute, value):
        if self.__frozen and not attribute in self.__dict__ and not attribute in self._meta:
            raise AttributeError("No such attribute: '{}'".format(attribute))
        return super(Struct, self).__setattr__(attribute, value)

    def __getitem__(self, value):
        # shallow copy of self
        other = copy.copy(self)
        # deep copy of the path
        other._path = copy.deepcopy(self._path)
        other._path.append(value)
        return other

    def invariants(self, conj=None):
        if conj is None:
            conj = []
        for k, v in self._meta.items():
            if k in self._structs:
                v = self._structs[k]
            for c in v.invariants():
                conj.append(c)
        return conj

    def initial(self):
        kp = self.copy()
        for k, v in kp._meta.items():
            if k in kp._structs:
                kp._structs[k] = kp._structs[k].initial()
            else:
                v.initial(kp)
        return kp

    def ite(self, other, cond):
        assert self.__class__ == other.__class__
        new = copy.copy(self)
        new._fields = util.If(cond, self._fields, other._fields)
        new._structs = util.If(cond, self._structs, other._structs)
        return new


class BaseStruct(Struct):
    def __init__(self):
        self._init(None, None)


class Map(AbstractMap):
    def new(self):
        if self.get_arity() == 0:
            types = self.get_types()
            assert len(types) == 1
            typ = types[0]
            if typ == z3.BoolSort():
                value = util.FreshBool(self._prefix + self._name)
            else:
                value = util.FreshBitVec(self._prefix + self._name, typ)
        else:
            value = util.FreshFunction(self._prefix + self._name, *self.get_types())
        return value

    def get(self, fn, args):
        if args:
            return fn(*args)
        else:
            return fn

    def set(self, old, args, value):
        # "raw" assignment of a lambda without any accessor arguments
        if isinstance(value, types.FunctionType):
            assert not args
            return lambda *args: value(*args, oldfn=old)
        elif self.get_arity() == 0:
            # assignment to a value
            return value
        else:
            # assignment with value with partial arguments
            return util.partial_update(old, args, value)


class Refcnt(Map):
    """Refcount based on permuting the set of `owned` objects"""
    def __init__(self, *args, **kwargs):
        self._initial_offset = kwargs.pop('initial_offset', 0)
        super(Refcnt, self).__init__(*args, **kwargs)

    def __call__(self, instance, owner=None):
        f = instance._fields[self._name]
        assert len(instance._path) == 1
        return self.get(f, instance._path)

    def new(self):
        assert self.get_arity() == 2
        owner, owned, size = self.get_types()
        ref = util.FreshFunction(self._prefix + self._name, owner, size)
        perm = util.FreshFunction(self._prefix + self._name, owner, size, owned)
        perm_inv = util.FreshFunction(self._prefix + self._name, owner, owned, size)
        return (ref, perm, perm_inv)

    def check(self, instance, conj, is_owner_valid, is_owned_valid, max_refs, ownerfn=None, ownedby=None):
        """Emit correctness definitions for this refcnt"""

        assert ownerfn != None or ownedby != None
        assert not (ownerfn and ownedby)

        if ownerfn:
            ownedby = lambda arg1, arg2: ownerfn(arg2) == arg1

        fn = instance._fields[self._name]
        owner = util.FreshBitVec('owner', self.get_types()[0])
        owned = util.FreshBitVec('owned', self.get_types()[1])
        idx = util.FreshBitVec('idx', self.get_types()[2])

        ref, perm, perm_inv = fn

        # 1) a valid input implies a valid owned output
        conj.append(z3.ForAll([owner, owned], z3.Implies(is_owner_valid(owner),
            z3.Implies(is_owned_valid(owned),
                z3.ULT(perm_inv(owner, owned), max_refs)
        ))))

        # 2) The function is a bijection
        conj.append(z3.ForAll([owner, owned, idx],
            z3.Implies(z3.And(
                is_owner_valid(owner),
                is_owned_valid(owned),
                z3.ULT(idx, max_refs)),
            z3.And(
                perm_inv(owner, perm(owner, idx)) == idx,
                perm(owner, perm_inv(owner, owned)) == owned,
        ))))

        # 3) if 'owner' owns 'owned', then f(owned) < ref, otherwise f(owned) >= ref
        conj.append(z3.ForAll([owner, owned], z3.Implies(
            z3.And(
                is_owner_valid(owner),
                is_owned_valid(owned),
            ),
            z3.And(
                z3.Implies(ownedby(owner, owned),
                    z3.ULT(perm_inv(owner, owned), ref(owner))),
                z3.Implies(z3.Not(ownedby(owner, owned)),
                    z3.UGE(perm_inv(owner, owned), ref(owner)))
            ))))

        # Checks that the refcnt don't overflows, that if its
        # value is 0 that the owner owns nothing and if its value is max_refs that
        # process owns all the resources.

        # refcount is in the range 0 <= r <= max_refs
        conj.append(z3.ForAll([owner],
            z3.Implies(is_owner_valid(owner), z3.ULE(ref(owner), max_refs))))

        # if refcount is 0, then you own no pages
        conj.append(z3.ForAll([owner, owned], z3.Implies(
            z3.And(
                is_owner_valid(owner),
                is_owned_valid(owned),
                ref(owner) == z3.BitVecVal(0, self.get_types()[-1]),
            ),
            z3.Not(ownedby(owner, owned)),
        )))

        # if refcount is max_refs, then that owner owns all the resources
        conj.append(z3.ForAll([owner, owned], z3.Implies(
            z3.And(
                is_owner_valid(owner),
                is_owned_valid(owned),
                ref(owner) == max_refs
            ),
            ownedby(owner, owned),
        )))


    def set(self, old, args, value):
        assert isinstance(value, tuple)
        assert all(map(lambda v: isinstance(v, types.FunctionType), value))
        return value

    def get(self, fn, args):
        return fn[0](*args)

    def iadd(self, old, args, value):
        assert len(args) == 2
        assert value == 1
        ref, perm, perm_inv = old

        refval = ref(args[0])
        owned = perm(args[0], refval)
        idx = perm_inv(args[0], args[1])

        ref = util.partial_update(ref, (args[0],), refval + 1)

        # We are modeling the ownership with three functions,
        # 1) a refcount number: the number of objects owned by `owner`
        # 2) a function with the property that the first `refval` objects owned by `owner`
        # 3) a function that is the inverse of 2)

        # For example, consider 5 'ownable' objects in the system,
        # Where `owner` has 2 objects: 3 and 2. The state might look like:
        #--------------------------
        # 3 | 2 | 1 | 4 | 5
        #--------------------------
        #         ^
        #       refval
        # Now, iadd is incrementing the refcnt by allocating args[2]
        # To do this we have to swap the current position of args[2] with the
        # Slot at refval.

        # For example, if args[1] is 5, we update the state by swapping the `1`
        # at index refval with the index of args[1].
        #--------------------------
        # 3 | 2 | 5 | 4 | 1
        #--------------------------
        #             ^
        #           refval

        # Write the new value (args[1]) into position refval and maintain the
        # inverse function
        perm = util.partial_update(perm, (args[0], refval), args[1])
        perm_inv = util.partial_update(perm_inv, (args[0], args[1]), refval)

        # Write the previous value of refval to the previous location of args[1]
        perm = util.partial_update(perm, (args[0], idx), owned)
        perm_inv = util.partial_update(perm_inv, (args[0], owned), idx)

        return (ref, perm, perm_inv)

    def initial(self, instance):
        def trim(var):
            if var.size() == self.get_types()[1].size():
                return var
            return z3.Extract(self.get_types()[1].size() - 1, 0, var)
        def extend(var):
            if var.size() < self.get_types()[-1].size():
                v = z3.ZeroExt(self.get_types()[2].size() - var.size(), var)
                return v
            return var

        ref = instance._fields[self._name][0]
        perm = lambda pid, idx: trim(idx + self._initial_offset)
        perm_inv = lambda pid, child: extend(child - self._initial_offset)
        instance._fields[self._name] = (ref, perm, perm_inv)

    def isub(self, old, args, value):
        assert len(args) == 2
        assert value == 1
        ref, perm, perm_inv = old

        ref = util.partial_update(ref, (args[0],), ref(args[0]) - 1)

        refval = ref(args[0])
        owned = perm(args[0], refval)
        idx = perm_inv(args[0], args[1])

        perm = util.partial_update(perm, (args[0], refval), args[1])
        perm_inv = util.partial_update(perm_inv, (args[0], args[1]), refval)

        perm = util.partial_update(perm, (args[0], idx), owned)
        perm_inv = util.partial_update(perm_inv, (args[0], owned), idx)

        return (ref, perm, perm_inv)


class Refcnt2(Map):
    """Refcount based on permuting the set of `owned` objects"""
    def __call__(self, instance, owner=None):
        f = instance._fields[self._name]
        assert len(instance._path) == 1
        return self.get(f, instance._path)

    def new(self):
        assert self.get_arity() == 2
        owner, owned, size = self.get_types()
        ref = util.FreshFunction(self._prefix + self._name, owner, size)
        perm1 = util.FreshFunction(self._prefix + self._name, owner, size, owned[0])
        perm2 = util.FreshFunction(self._prefix + self._name, owner, size, owned[1])
        perm_inv = util.FreshFunction(self._prefix + self._name, owner, owned[0], owned[1], size)
        return (ref, perm1, perm2, perm_inv)

    def check(self, instance, conj, is_owner_valid, is_owned1_valid, is_owned2_valid, max_refs, ownerfn=None, ownedby=None):
        """Emit correctness definitions for this refcnt"""

        is_owned_valid = lambda a, b: z3.And(is_owned1_valid(a), is_owned2_valid(b))

        assert ownerfn != None or ownedby != None
        assert not (ownerfn and ownedby)

        if ownerfn:
            ownedby = lambda arg1, arg2: ownerfn(arg2) == arg1

        fn = instance._fields[self._name]
        owner = util.FreshBitVec('owner', self.get_types()[0])
        owned1 = util.FreshBitVec('owned1', self.get_types()[1][0])
        owned2 = util.FreshBitVec('owned2', self.get_types()[1][1])
        idx = util.FreshBitVec('idx', self.get_types()[2])

        ref, perm1, perm2, perm_inv = fn

        # 1) a valid input implies a valid owned output
        conj.append(z3.ForAll([owner, owned1, owned2], z3.Implies(
            z3.And(
                is_owner_valid(owner),
                is_owned_valid(owned1, owned2)),
            z3.ULT(perm_inv(owner, owned1, owned2), max_refs)
        )))

        conj.append(z3.ForAll([owner, idx], z3.Implies(
            z3.And(
                is_owner_valid(owner),
                z3.ULT(idx, max_refs)),
            z3.And(
                is_owned1_valid(perm1(owner, idx)),
                is_owned2_valid(perm2(owner, idx))))))

        # 2) The function function is a bijection
        conj.append(z3.ForAll([owner, owned1, owned2, idx],
            z3.Implies(z3.And(
                is_owner_valid(owner),
                is_owned_valid(owned1, owned2),
                z3.ULT(idx, max_refs)),
            z3.And(
                perm_inv(owner, perm1(owner, idx), perm2(owner, idx)) == idx,
                perm1(owner, perm_inv(owner, owned1, owned2)) == owned1,
                perm2(owner, perm_inv(owner, owned1, owned2)) == owned2,
        ))))

        # 3) if 'owner' owns 'owned', then f(owned) < ref, otherwise w(owned) >= ref
        conj.append(z3.ForAll([owner, owned1, owned2], z3.Implies(
            z3.And(
                is_owner_valid(owner),
                is_owned_valid(owned1, owned2),
            ),
            z3.And(
                z3.Implies(ownedby(owner, (owned1, owned2)),
                    z3.ULT(perm_inv(owner, owned1, owned2), ref(owner))),
                z3.Implies(z3.Not(ownedby(owner, (owned1, owned2))),
                    z3.UGE(perm_inv(owner, owned1, owned2), ref(owner)))
            ))))

        # Checks that the refcnt don't overflows, that if its
        # value is 0 that the owner owns nothing and if its value is max_refs that
        # process owns all the resources.

        # refcount is in the range 0 <= r <= max_refs
        conj.append(z3.ForAll([owner],
            z3.Implies(is_owner_valid(owner), z3.ULE(ref(owner), max_refs))))

        # if refcount is 0, then you own no pages
        conj.append(z3.ForAll([owner, owned1, owned2], z3.Implies(
            z3.And(
                is_owner_valid(owner),
                is_owned_valid(owned1, owned2),
                ref(owner) == z3.BitVecVal(0, self.get_types()[-1]),
            ),
            z3.Not(ownedby(owner, (owned1, owned2))),
        )))

        # if refcount is max_refs, then that owner owns all the resources
        conj.append(z3.ForAll([owner, owned1, owned2], z3.Implies(
            z3.And(
                is_owner_valid(owner),
                is_owned_valid(owned1, owned2),
                ref(owner) == max_refs
            ),
            ownedby(owner, (owned1, owned2)),
        )))

    def initial(self, instance):
        def trim(var, type):
            if var.size() == type.size():
                return var
            return z3.Extract(type.size() - 1, 0, var)
        def extend(var):
            if var.size() < self.get_types()[-1].size():
                v = z3.ZeroExt(self.get_types()[2].size() - var.size(), var)
                return v
            return var

        ref = instance._fields[self._name][0]
        perm1 = lambda fn, idx: trim(z3.UDiv(idx, 16) + 1 , type=self.get_types()[1][0])
        perm2 = lambda fn, idx: trim(z3.URem(idx, 16), type=self.get_types()[1][1])
        perm_inv = lambda fn, owned1, owned2: extend(owned1 - 1) * 16 + extend(owned2 % 16)
        instance._fields[self._name] = (ref, perm1, perm2, perm_inv)

    def set(self, old, args, value):
        assert isinstance(value, tuple)
        assert all(map(lambda v: isinstance(v, types.FunctionType), value))
        return value

    def get(self, fn, args):
        return fn[0](*args)

    def iadd(self, old, args, value):
        assert len(args) == 2
        assert value == 1
        ref, perm1, perm2, perm_inv = old

        refval = ref(args[0])
        owned_x = perm1(args[0], refval)
        owned_y = perm2(args[0], refval)
        idx = perm_inv(args[0], *args[1])

        ref = util.partial_update(ref, (args[0],), refval + 1)

        # We are modeling the ownership with three functions,
        # 1) a refcount number: the number of objects owned by `owner`
        # 2) a function with the property that the first `refval` objects owned by `owner`
        # 3) a function that is the inverse of 2)

        # For example, consider 5 'ownable' objects in the system,
        # Where `owner` has 2 objects: 3 and 2. The state might look like:
        #--------------------------
        # 3 | 2 | 1 | 4 | 5
        #--------------------------
        #         ^
        #       refval
        # Now, iadd is incrementing the refcnt by allocating args[2]
        # To do this we have to swap the current position of args[2] with the
        # Slot at refval.

        # For example, if args[1] is 5, we update the state by swapping the `1`
        # at index refval with the index of args[1].
        #--------------------------
        # 3 | 2 | 5 | 4 | 1
        #--------------------------
        #             ^
        #           refval

        # Write the new value (args[1]) into position refval and maintain the
        # inverse function
        perm1 = util.partial_update(perm1, (args[0], refval), args[1][0])
        perm2 = util.partial_update(perm2, (args[0], refval), args[1][1])
        perm_inv = util.partial_update(perm_inv, (args[0], args[1][0], args[1][1]), refval)

        # Write the previous value of refval to the previous location of args[1]
        perm1 = util.partial_update(perm1, (args[0], idx), owned_x)
        perm2 = util.partial_update(perm2, (args[0], idx), owned_y)
        perm_inv = util.partial_update(perm_inv, (args[0], owned_x, owned_y), idx)

        return (ref, perm1, perm2, perm_inv)

    def isub(self, old, args, value):
        assert len(args) == 2
        assert value == 1
        ref, perm1, perm2, perm_inv = old

        ref = util.partial_update(ref, (args[0],), ref(args[0]) - 1)

        refval = ref(args[0])
        owned_x = perm1(args[0], refval)
        owned_y = perm2(args[0], refval)
        idx = perm_inv(args[0], *args[1])

        perm1 = util.partial_update(perm1, (args[0], refval), args[1][0])
        perm2 = util.partial_update(perm2, (args[0], refval), args[1][1])
        perm_inv = util.partial_update(perm_inv, (args[0], args[1][0], args[1][1]), refval)

        perm1 = util.partial_update(perm1, (args[0], idx), owned_x)
        perm2 = util.partial_update(perm2, (args[0], idx), owned_y)
        perm_inv = util.partial_update(perm_inv, (args[0], owned_x, owned_y), idx)

        return (ref, perm1, perm2, perm_inv)
