#include "types.h"
#include "proc.h"

#define ASSERT(test) assert(test, # test)

/*  These will be overridden in python */
bool __attribute__((noinline)) implies(bool a, bool b)
{
    return !a || b;
}
bool __attribute__((noinline)) and2(bool a, bool b)
{
    return a && b;
}

bool __attribute__((noinline)) and3(bool a, bool b, bool c)
{
    return a && b && c;
}

bool __attribute__((noinline)) and4(bool a, bool b, bool c, bool d)
{
    return a && b && c && d;
}

bool __attribute__((noinline)) and5(bool a, bool b, bool c, bool d, bool e)
{
    return a && b && c && d && e;
}

bool __attribute__((noinline)) and6(bool a, bool b, bool c, bool d, bool e, bool f)
{
    return a && b && c && d && e && f;
}

bool __attribute__((noinline)) and7(bool a, bool b, bool c, bool d, bool e, bool f, bool g)
{
    return a && b && c && d && e && f && g;
}

bool __attribute__((noinline)) and8(bool a, bool b, bool c, bool d, bool e, bool f, bool g, bool h)
{
    return a && b && c && d && e && f && g && h;
}

bool __attribute__((noinline)) and9(bool a, bool b, bool c, bool d, bool e, bool f, bool g, bool h, bool i)
{
    return a && b && c && d && e && f && g && h && i;
}

bool __attribute__((noinline)) or2(bool a, bool b)
{
    return a || b;
}

bool __attribute__((noinline)) or3(bool a, bool b, bool c)
{
    return a || b || c;
}

bool __attribute__((noinline)) or4(bool a, bool b, bool c, bool d)
{
    return a || b || c || d;
}

static struct proc *_get_proc(pid_t pid)
{
    return &proc_table[pid];
}

static inline struct page_desc *_get_page_desc(pn_t pn)
{
    return &page_desc_table[pn];
}

static bool __attribute__((noinline)) _is_pid_valid(pid_t pid)
{
    return and2(pid > 0, pid < NPROC);
}

static bool __attribute__((noinline)) _is_pid_bounded(pid_t pid)
{
    return (uint64_t)pid < NPROC;
}

static inline bool _is_pn_valid(pn_t pn)
{
    return pn < NPAGE;
}

static inline bool _is_fn_valid(fn_t fn)
{
    return and2(fn > 0, fn < NFILE);
}

static inline bool _is_fd_valid(int fd)
{
    return and2(fd >= 0, fd < NOFILE);
}

static inline bool _is_page_pid(pn_t pn, pid_t pid)
{
    return _get_page_desc(pn)->pid == pid;
}

static inline bool _is_page_type(pn_t pn, enum page_type type)
{
    return _get_page_desc(pn)->type == type;
}

static inline bool _is_proc_state(pid_t pid, enum proc_state state)
{
    return _get_proc(pid)->state == state;
}

static inline fn_t _get_fd(pid_t pid, int fd)
{
    return _get_proc(pid)->ofile[fd];
}

// invariants

bool inv_current_valid(void)
{
    return _is_pid_valid(current);
}

bool inv_current_running(void)
{
    return _is_proc_state(current, PROC_RUNNING);
}

bool inv_proc_pns_valid(pid_t pid)
{
    return and3(_is_pn_valid(_get_proc(pid)->page_table_root), _is_pn_valid(_get_proc(pid)->hvm),
                _is_pn_valid(_get_proc(pid)->stack));
}

bool inv_proc_owns_pns(pid_t pid)
{
    return implies(
        or4(_is_proc_state(pid, PROC_EMBRYO), _is_proc_state(pid, PROC_RUNNING),
            _is_proc_state(pid, PROC_RUNNABLE), _is_proc_state(pid, PROC_SLEEPING)),
        and3(and3(_is_pn_valid(_get_proc(pid)->page_table_root),
                  _is_page_pid(_get_proc(pid)->page_table_root, pid),
                  _is_page_type(_get_proc(pid)->page_table_root, PAGE_TYPE_X86_PML4)),
             and3(_is_pn_valid(_get_proc(pid)->hvm), _is_page_pid(_get_proc(pid)->hvm, pid),
                  _is_page_type(_get_proc(pid)->hvm, PAGE_TYPE_PROC_DATA)),
             and3(_is_pn_valid(_get_proc(pid)->stack), _is_page_pid(_get_proc(pid)->stack, pid),
                  _is_page_type(_get_proc(pid)->stack, PAGE_TYPE_PROC_DATA))));
}

bool inv_sleeping_proc_owns_ipc(pid_t pid)
{
    return implies(is_pid_valid(pid),
                   implies(_is_proc_state(pid, PROC_SLEEPING),
                           and3(_is_pn_valid(_get_proc(pid)->ipc_page),
                                _is_page_pid(_get_proc(pid)->ipc_page, pid),
                                _is_page_type(_get_proc(pid)->ipc_page, PAGE_TYPE_FRAME))));
}

bool inv_sleeping_proc_ipc_fd_valid_empty(pid_t pid)
{
    return implies(is_pid_valid(pid), implies(and2(_is_proc_state(pid, PROC_SLEEPING),
                                                   _is_fd_valid(_get_proc(pid)->ipc_fd)),
                                              _get_fd(pid, _get_proc(pid)->ipc_fd) == 0));
}

bool inv_proc_fds_valid(pid_t pid, int fd)
{
    return implies(and2(_is_pid_valid(pid), _is_fd_valid(fd)),
                   or2(_get_fd(pid, fd) == 0, _is_fn_valid(_get_fd(pid, fd))));
}

bool inv_proc_unused_refs(pid_t pid)
{
    return implies(and2(_is_pid_valid(pid), is_proc_state(pid, PROC_UNUSED)),
                   and8(_get_proc(pid)->nr_children == 0,
                        _get_proc(pid)->nr_fds == 0,
                        _get_proc(pid)->nr_pages == 0,
                        _get_proc(pid)->nr_dmapages == 0,
                        _get_proc(pid)->nr_devs == 0,
                        _get_proc(pid)->nr_ports == 0,
                        _get_proc(pid)->nr_vectors == 0,
                        _get_proc(pid)->nr_intremaps == 0));
}

bool inv_io_bitmap(pid_t pid)
{
    return implies(_is_pid_valid(pid),
            implies(and2(_get_proc(pid)->use_io_bitmap, _get_proc(pid)->state != PROC_ZOMBIE),
                and6(is_pn_valid(_get_proc(pid)->io_bitmap_a),
                     is_pn_valid(_get_proc(pid)->io_bitmap_b),
                    _is_page_pid(_get_proc(pid)->io_bitmap_a, pid),
                    _is_page_pid(_get_proc(pid)->io_bitmap_b, pid),
                    _is_page_type(_get_proc(pid)->io_bitmap_a, PAGE_TYPE_PROC_DATA),
                    _is_page_type(_get_proc(pid)->io_bitmap_b, PAGE_TYPE_PROC_DATA))));

}

bool inv_page_owner(pn_t pn)
{
    return implies(_is_pn_valid(pn), _is_pid_valid(_get_page_desc(pn)->pid) ==
                                         (_get_page_desc(pn)->type != PAGE_TYPE_FREE));
}

bool inv_proc_freelist_valid(pn_t pid)
{
    return implies(_is_pid_bounded(pid),
            and2(_is_pid_bounded(_get_proc(pid)->ready.prev),
                 _is_pid_bounded(_get_proc(pid)->ready.next)));
}

bool inv_page_freelist_valid(pn_t pn)
{
    return implies(_is_pn_valid(pn),
            and2(_is_pn_valid(_get_page_desc(pn)->link.prev),
                 _is_pn_valid(_get_page_desc(pn)->link.next)));
}

void check_invariants(void)
{
    pid_t pid;
    pn_t pn;
    int fd;

    pr_info("checking invariants\n");
    ASSERT(inv_current_valid());
    ASSERT(inv_current_running());

    for (pid = 0; pid < NPROC; pid++) {
        ASSERT(inv_proc_pns_valid(pid));
        ASSERT(inv_proc_owns_pns(pid));
        ASSERT(inv_proc_unused_refs(pid));
        ASSERT(inv_io_bitmap(pid));
        ASSERT(inv_proc_freelist_valid(pid));
        ASSERT(inv_sleeping_proc_owns_ipc(pid));
        ASSERT(inv_sleeping_proc_ipc_fd_valid_empty(pid));
        for (fd = 0; fd < NOFILE; fd++) {
            ASSERT(inv_proc_fds_valid(pid, fd));
        }
    }

    for (pn = 0; pn < NPAGE; pn++) {
        ASSERT(inv_page_owner(pn));
        ASSERT(inv_page_freelist_valid(pn));
    }

    pr_info("checking invariants done\n");
}
