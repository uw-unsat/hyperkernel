#!/usr/bin/env python2
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

#
# Expects input in the format yielded by
# objdump --no-show-raw-insn -d
#

import re
import sys
import stackcheck_config as config


def die(mesg):
    print '\033[91m' + 'stackcheck.py failed: {}'.format(mesg) + '\033[0m'
    exit(1)


if len(sys.argv) < 2:
    f = sys.stdin
else:
    f = open(sys.argv[1], 'r')

func_re = re.compile('[0-9a-f]{16} <([^>]*)>:')
instr_re = re.compile('  [0-9a-f]*:\t([a-zA-Z]+\s+.*)')
blank_re = re.compile('\s*')

call_re = re.compile('callq?\s+[0-9a-f]+ <([^+>]+).*')
subrsp_re = re.compile('sub\s+\$(0x[0-9a-f]+),%[re]sp')
addrsp_re = re.compile('add\s+\$(0x[0-9a-f]+),%[re]sp')
push_re = re.compile('push.*')

current_symbol = None
callgraph = {}
local_stackusage = {}

for line in f:

    # Is this a new symbol?
    match = func_re.match(line)
    if match:
        current_symbol = match.group(1)
        callgraph[current_symbol] = []
        local_stackusage[current_symbol] = 0L
        continue

    match = instr_re.match(line)
    if match:
        if current_symbol is None:
            die('Found instruction before first symbol')
        instr = match.group(1)
        match = call_re.match(instr)
        if match:
            if match.group(1) == current_symbol:
                # Recursion, just set usage to be "very large"
                local_stackusage[current_symbol] = 9999999999999L
            elif match.group(1) != 'panic':
                callgraph[current_symbol].append(match.group(1))
            continue

        # sub %rsp
        match = subrsp_re.match(instr)
        if match:
            operand = long(match.group(1), 16)
            if operand <= (2L ** 63) - 1:
                local_stackusage[current_symbol] += operand
            continue

        # add %rsp
        match = addrsp_re.match(instr)
        if match:
            operand = long(match.group(1), 16)
            if operand >= (2L ** 63) - 1:
                operand = (2L ** 64) - operand
                local_stackusage[current_symbol] += operand
            continue

        # pushes
        match = push_re.match(instr)
        if match:
            local_stackusage[current_symbol] += 8
            continue

        # some other instruction
        continue

    if blank_re.match(line):
        continue

    die('Unable to parse line:'.format(line))

f.close()

# Compute stack usage

stackusage = {}


def get_usage(symbol):
    if symbol in stackusage:
        return stackusage[symbol]
    usage = local_stackusage[symbol]
    usage += max(map(lambda child: get_usage(child) +
                     8, callgraph[symbol]) or [0])
    stackusage[symbol] = usage
    return usage


for s in local_stackusage:
    if any(map(lambda f: f(s), config.check)):
        if get_usage(s) > config.maxusage:
            print '{} - {} bytes - ERROR!'.format(s, get_usage(s))
            die('{} uses more than {} bytes of stack :('.format(s, config.maxusage))
        else:
            print '{} - {} bytes - OK'.format(s, get_usage(s))

print 'All checked functions use less than {} bytes of stack :)'.format(config.maxusage)
exit(0)
