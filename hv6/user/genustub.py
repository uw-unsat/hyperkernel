#!/usr/bin/env python

import fileinput

for line in fileinput.input():
    e = line.strip().split()
    assert len(e) == 3
    addr, typ, name = e
    if typ != 'T':
        continue
    if name in ['_start', 'main']:
        continue
    print('.global\t{}'.format(name))
    print('{}:'.format(name))
    print('\tmovq\t$0x{}, %rax'.format(addr))
    print('\tjmpq\t*%rax')
    print('')
