#!/usr/bin/env bash

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

read -p 'Install Prefix> ' BOCHS_PREFIX
./configure --enable-disasm --enable-x86-64 --enable-all-optimizations --enable-gdb-stub --enable-fpu --enable-cdrom --enable-plugins --enable-pci --enable-alignment-check --enable-debugger-gui --enable-iodebug --enable-logging --enable-cpu-level=6 --with-term --with-sdl2 --with-nogui --enable-svm --enable-avx --enable-evex --enable-vmx=2 --disable-show-ips --prefix="${BOCHS_PREFIX}"

