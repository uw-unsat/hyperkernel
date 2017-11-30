#!/usr/bin/env python2
# Expects input in the format yielded by
# nm --numeric-sort --print-size

import sys

def main():
    addr = 1024 * 1024
    for line in sys.stdin:
        line = line.strip().split()
        if len(line) != 4:
            continue
        start = int(line[0], 16)
        end = start + int(line[1], 16)
        print("%016x-%016x: %s" % (start, end - 1, line[-1]))
        # check no overlap
        assert addr <= start
        addr = end

if __name__ == "__main__":
    main()
