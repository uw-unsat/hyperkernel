#!/usr/bin/env python

import fileinput

count = 0
print('#include <symtable.h>')
print('')
print('const struct symbol ksymtable[] = {')
for line in fileinput.input():
    e = line.strip().split()
    if len(e) == 2:
        # weak symbols
        addr = 0
        typ, name = e
    else:
        assert len(e) == 3
        addr, typ, name = e
    count += 1
    print('\t{{ 0x{}, \'{}\', "{}" }},'.format(addr, typ, name))
print('};')
print('')
print('const uint64_t ksymtable_count = {};'.format(count))
