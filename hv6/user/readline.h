#pragma once

char *readline(const char *prompt);
void add_history(const char *);
void reset_history(void);
int bind_key(int key, int (*function)(int key, int cur, char **buf));
