#pragma once

#include "types.h"

extern struct file file_table[NFILE];

int sys_create(int fd, fn_t fn, uint64_t type, uint64_t value, uint64_t mode);
int sys_close(pid_t pid, int fd);
int sys_dup(int oldfd, pid_t pid, int newfd);
int sys_dup2(int oldfd, pid_t pid, int newfd);
int sys_lseek(int fd, off_t offset);

static inline struct file *get_file(fn_t fn)
{
    assert(is_fn_valid(fn), "fn must be valid");
    return &file_table[fn];
}

static inline bool is_file_type(fn_t fn, enum file_type type)
{
    return is_fn_valid(fn) && get_file(fn)->type == type;
}
