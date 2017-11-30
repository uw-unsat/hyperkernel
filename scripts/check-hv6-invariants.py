#!/usr/bin/env python2
import os
import sys
import subprocess
import time

q = subprocess.Popen('make hv6-qemu', stdout=subprocess.PIPE, shell=True)

time.sleep(10)

q.terminate()

os.popen('killall qemu-system-x86_64')

buf = q.stdout.read(2 ** 20)

print buf

if 'checking invariants done' in buf:
    sys.exit(0)
else:
    sys.exit(1)
