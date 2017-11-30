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

import libirpy.util as util

import datatypes as dt


def _sys_alloc():
    pid = util.FreshBitVec('pid', dt.pid_t)
    frm = util.FreshBitVec('from', dt.pn_t)
    index = util.FreshBitVec('index', dt.size_t)
    to = util.FreshBitVec('to', dt.pn_t)
    perm = util.FreshBitVec('perm', dt.pte_t)
    return (pid, frm, index, to, perm)


def _sys_alloc_iommu():
    frm = util.FreshBitVec('from', dt.pn_t)
    index = util.FreshBitVec('index', dt.size_t)
    to = util.FreshBitVec('to', dt.pn_t)
    perm = util.FreshBitVec('perm', dt.dmar_pte_t)
    return (frm, index, to, perm)


def _sys_free():
    frm = util.FreshBitVec('from', dt.pn_t)
    index = util.FreshBitVec('index', dt.size_t)
    to = util.FreshBitVec('to', dt.pn_t)
    return (frm, index, to)


def _sys_map():
    pid = util.FreshBitVec('pid', dt.pid_t)
    frm = util.FreshBitVec('from', dt.pn_t)
    index = util.FreshBitVec('index', dt.size_t)
    n = util.FreshBitVec('n', dt.size_t)
    perm = util.FreshBitVec('perm', dt.pte_t)
    return (pid, frm, index, n, perm)


class SyscallSpec(object):
    def sys_nop(self):
        return ()

    def sys_map_pml4(self):
        pid = util.FreshBitVec('pid', dt.pid_t)
        index = util.FreshBitVec('index', dt.size_t)
        perm = util.FreshBitVec('perm', dt.pte_t)
        return (pid, index, perm)

    def sys_map_page_desc(self):
        return _sys_map()

    def sys_map_proc(self):
        return _sys_map()

    def sys_map_dev(self):
        return _sys_map()

    def sys_map_pcipage(self):
        pt = util.FreshBitVec('pt', dt.pn_t)
        index = util.FreshBitVec('index', dt.size_t)
        pcipn = util.FreshBitVec('pcipn', dt.pn_t)
        perm = util.FreshBitVec('perm', dt.pte_t)
        return (pt, index, pcipn, perm)

    def sys_map_file(self):
        return _sys_map()

    def sys_map_inode(self):
        return _sys_map()

    def sys_map_bitmap(self):
        return _sys_map()

    def sys_alloc_pdpt(self):
        return _sys_alloc()

    def sys_alloc_pd(self):
        return _sys_alloc()

    def sys_alloc_pt(self):
        return _sys_alloc()

    def sys_alloc_frame(self):
        return _sys_alloc()

    def sys_copy_frame(self):
        frm = util.FreshBitVec('from', dt.pn_t)
        pid = util.FreshBitVec('pid', dt.pid_t)
        to = util.FreshBitVec('to', dt.pn_t)
        return (frm, pid, to)

    def sys_protect_frame(self):
        pt = util.FreshBitVec('pt', dt.pn_t)
        index = util.FreshBitVec('index', dt.size_t)
        frame = util.FreshBitVec('frame', dt.pn_t)
        perm = util.FreshBitVec('perm', dt.pte_t)
        return (pt, index, frame, perm)

    def sys_free_pdpt(self):
        return _sys_free()

    def sys_free_pd(self):
        return _sys_free()

    def sys_free_pt(self):
        return _sys_free()

    def sys_free_frame(self):
        return _sys_free()

    def sys_reclaim_page(self):
        pn = util.FreshBitVec('pn', dt.pn_t)
        return (pn,)

    def sys_reclaim_iommu_frame(self):
        dmapn = util.FreshBitVec('dmapn', dt.dmapn_t)
        return (dmapn,)

    def sys_reclaim_iommu_root(self):
        devid = util.FreshBitVec('devid', dt.devid_t)
        return (devid,)

    def sys_clone(self):
        pid = util.FreshBitVec('pid', dt.pid_t)
        pml4 = util.FreshBitVec('pml4', dt.pn_t)
        stack = util.FreshBitVec('stack', dt.pn_t)
        hvm = util.FreshBitVec('hvm', dt.pn_t)
        return (pid, pml4, stack, hvm)
    clone_proc = sys_clone

    def sys_set_proc_name(self):
        name0 = util.FreshBitVec('name0', dt.uint64_t)
        name1 = util.FreshBitVec('name1', dt.uint64_t)
        return (name0, name1)

    def sys_set_runnable(self):
        pid = util.FreshBitVec('pid', dt.pid_t)
        return (pid,)

    def sys_switch(self):
        pid = util.FreshBitVec('pid', dt.pid_t)
        return (pid,)
    switch_proc = sys_switch

    def sys_kill(self):
        pid = util.FreshBitVec('pid', dt.pid_t)
        return (pid,)

    def sys_reap(self):
        pid = util.FreshBitVec('pid', dt.pid_t)
        return (pid,)

    def sys_reparent(self):
        pid = util.FreshBitVec('pid', dt.pid_t)
        return (pid,)

    # ipc syscalls

    def sys_send(self):
        pid = util.FreshBitVec('pid', dt.pid_t)
        val = util.FreshBitVec('val', dt.uint64_t)
        pn = util.FreshBitVec('pn', dt.pn_t)
        size = util.FreshBitVec('size', dt.size_t)
        fd = util.FreshBitVec('fd', dt.fd_t)
        return (pid, val, pn, size, fd)
    send_proc = sys_send

    def sys_recv(self):
        pid = util.FreshBitVec('pid', dt.pid_t)
        pn = util.FreshBitVec('pn', dt.pn_t)
        fd = util.FreshBitVec('fd', dt.fd_t)
        return (pid, pn, fd)
    recv_proc = sys_recv

    def sys_reply_wait(self):
        pid = util.FreshBitVec('pid', dt.pid_t)
        val = util.FreshBitVec('val', dt.uint64_t)
        inpn = util.FreshBitVec('inpn', dt.pn_t)
        size = util.FreshBitVec('size', dt.size_t)
        infd = util.FreshBitVec('infd', dt.fd_t)
        outpn = util.FreshBitVec('outpn', dt.pn_t)
        return (pid, val, inpn, size, infd, outpn)
    reply_wait_proc = sys_reply_wait

    def sys_call(self):
        pid = util.FreshBitVec('pid', dt.pid_t)
        val = util.FreshBitVec('val', dt.uint64_t)
        inpn = util.FreshBitVec('inpn', dt.pn_t)
        size = util.FreshBitVec('size', dt.size_t)
        outpn = util.FreshBitVec('outpn', dt.pn_t)
        outfd = util.FreshBitVec('outfd', dt.fd_t)
        return (pid, val, inpn, size, outpn, outfd)
    call_proc = sys_call

    # fd syscalls

    def sys_create(self):
        fd = util.FreshBitVec('fd', dt.fd_t)
        fn = util.FreshBitVec('fn', dt.fn_t)
        type = util.FreshBitVec('type', dt.uint64_t)
        value = util.FreshBitVec('value', dt.uint64_t)
        omode = util.FreshBitVec('omode', dt.uint64_t)
        return (fd, fn, type, value, omode)

    def sys_close(self):
        pid = util.FreshBitVec('pid', dt.pid_t)
        fd = util.FreshBitVec('fd', dt.fd_t)
        return (pid, fd)

    def sys_dup(self):
        oldfd = util.FreshBitVec('oldfd', dt.fd_t)
        pid = util.FreshBitVec('pid', dt.pid_t)
        newfd = util.FreshBitVec('newfd', dt.fd_t)
        return (oldfd, pid, newfd)

    def sys_dup2(self):
        oldfd = util.FreshBitVec('oldfd', dt.fd_t)
        pid = util.FreshBitVec('pid', dt.pid_t)
        newfd = util.FreshBitVec('newfd', dt.fd_t)
        return (oldfd, pid, newfd)

    def sys_lseek(self):
        fd = util.FreshBitVec('fd', dt.fd_t)
        offset = util.FreshBitVec('offset', dt.off_t)
        return (fd, offset)

    # iommu syscalls

    def sys_alloc_iommu_root(self):
        devid = util.FreshBitVec('devid', dt.devid_t)
        pn = util.FreshBitVec('pn', dt.pn_t)
        return (devid, pn)

    def sys_alloc_iommu_pdpt(self):
        return _sys_alloc_iommu()

    def sys_alloc_iommu_pd(self):
        return _sys_alloc_iommu()

    def sys_alloc_iommu_pt(self):
        return _sys_alloc_iommu()

    def sys_alloc_iommu_frame(self):
        return _sys_alloc_iommu()

    def sys_map_iommu_frame(self):
        pt = util.FreshBitVec('pt', dt.pn_t)
        index = util.FreshBitVec('index', dt.size_t)
        to = util.FreshBitVec('to', dt.dmapn_t)
        perm = util.FreshBitVec('perm', dt.pte_t)
        return (pt, index, to, perm)

    def sys_alloc_vector(self):
        return (util.FreshBitVec('vector', dt.uint8_t),)

    def sys_reclaim_vector(self):
        return (util.FreshBitVec('vector', dt.uint8_t),)

    def sys_alloc_intremap(self):
        index = util.FreshBitVec('index', dt.size_t)
        devid = util.FreshBitVec('devid', dt.devid_t)
        vector = util.FreshBitVec('vector', dt.uint8_t)
        return (index, devid, vector)

    def sys_reclaim_intremap(self):
        index = util.FreshBitVec('index', dt.size_t)
        return (index,)

    def sys_ack_intr(self):
        return (util.FreshBitVec('vector', dt.uint8_t),)

    def sys_alloc_io_bitmap(self):
        pn1 = util.FreshBitVec('pn', dt.pn_t)
        pn2 = util.FreshBitVec('pn', dt.pn_t)
        pn3 = util.FreshBitVec('pn', dt.pn_t)
        return (pn1, pn2, pn3)

    def sys_alloc_port(self):
        port = util.FreshBitVec('port', dt.uint16_t)
        return (port,)

    def sys_reclaim_port(self):
        port = util.FreshBitVec('port', dt.uint16_t)
        return (port,)

    def extintr(self):
        vector = util.FreshBitVec('vector', dt.uint8_t)
        return (vector,)

    # sys_mmap
    # sys_munmap


def get_syscall_args(name):
    s = SyscallSpec()
    if not hasattr(s, name):
        raise NotImplementedError()
    return getattr(SyscallSpec(), name)()
