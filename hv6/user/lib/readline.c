#include "user.h"
#include "fs.h"

#define ASCII_MAX 255

typedef bool (*rl_handler2)(int, void *);

struct history {
    char *line;
    int len;
    struct history *next;
    struct history *prev;
};

struct rl_state {
    char *buf;
    int buflen;
    int bufidx;
    int curidx;
    bool *(*transitions)(int, void *);
    struct history *history;
};

static struct history *history_head;

typedef bool (*rl_handler)(int, struct rl_state *);

bool rl_etx(int key, struct rl_state *s);
bool rl_eot(int key, struct rl_state *s);

bool rl_emit_char(int key, struct rl_state *s);
bool rl_drop1(int key, struct rl_state *s);
bool rl_drop_word(int key, struct rl_state *s);
bool rl_drop_all(int key, struct rl_state *s);
bool rl_delete(int key, struct rl_state *s);
bool rl_newline(int key, struct rl_state *s);
bool rl_completion(int key, struct rl_state *s);

bool rl_history_prev(int key, struct rl_state *s);
bool rl_history_next(int key, struct rl_state *s);

bool rl_line_left(int key, struct rl_state *s);
bool rl_line_right(int key, struct rl_state *s);

bool rl_nop(int key, struct rl_state *s);

bool rl_transition_normal(int key, struct rl_state *s);
bool rl_transition_escape(int key, struct rl_state *s);
bool rl_transition_control(int key, struct rl_state *s);

rl_handler key_binds_normal[ASCII_MAX] = {
        [0 ... ASCII_MAX - 1] = rl_emit_char,
        [3] = rl_etx,
        [4] = rl_eot,
        [23] = rl_drop_word,
        ['\e'] = rl_transition_escape,
        ['\t'] = rl_completion,
        ['\b'] = rl_drop1,
        ['\x7f'] = rl_drop1,
        ['\n'] = rl_newline,
        ['\r'] = rl_newline,
};

rl_handler key_binds_escape[ASCII_MAX] = {
        [0 ... ASCII_MAX - 1] = rl_nop, ['\e'] = rl_nop, ['['] = rl_transition_control,
};

rl_handler key_binds_control[ASCII_MAX] = {
        [0 ... ASCII_MAX - 1] = rl_transition_normal,
        ['A'] = rl_history_next,
        ['B'] = rl_history_prev,
        ['D'] = rl_line_left,
        ['C'] = rl_line_right,
        ['3'] = rl_nop,
        ['~'] = rl_delete,
};

void rl_reserve(struct rl_state *s, int buflen)
{
    while (s->buflen - s->bufidx < buflen) {
        s->buflen *= 2;
        s->buf = realloc(s->buf, s->buflen);
    }
}

void rl_transition(struct rl_state *s, void *binds)
{
    s->transitions = binds;
}

void rl_emit(struct rl_state *s, char *buf, int buflen)
{
    rl_reserve(s, buflen + 1);
    if (s->curidx < s->bufidx) {
        memmove(s->buf + s->curidx + buflen, s->buf + s->curidx, s->bufidx - s->curidx);
    }
    memcpy(s->buf + s->curidx, buf, buflen);

    s->bufidx += buflen;
    s->curidx += buflen;
}

bool rl_history_prev(int key, struct rl_state *s)
{
    rl_transition(s, (void *)key_binds_normal);
    rl_drop_all(key, s);
    if (s->history != NULL) {
        s->history = s->history->prev;
    }
    if (s->history != NULL) {
        rl_emit(s, s->history->line, s->history->len);
    }
    return true;
}

bool rl_line_left(int key, struct rl_state *s)
{
    rl_transition(s, (void *)key_binds_normal);
    if (s->curidx > 0) {
        s->curidx--;
    }
    return true;
}

bool rl_line_right(int key, struct rl_state *s)
{
    rl_transition(s, (void *)key_binds_normal);
    if (s->curidx < s->bufidx) {
        s->curidx++;
    }
    return true;
}

bool rl_history_next(int key, struct rl_state *s)
{
    rl_transition(s, (void *)key_binds_normal);
    rl_drop_all(key, s);
    if (s->history == NULL) {
        s->history = history_head;
    } else {
        if (s->history->next != NULL)
            s->history = s->history->next;
    }

    if (s->history != NULL) {
        rl_emit(s, s->history->line, s->history->len);
    }
    return true;
}

bool rl_nop(int key, struct rl_state *s)
{
    return true;
}

bool rl_eot(int key, struct rl_state *s)
{
    s->bufidx = 0;
    s->curidx = 0;
    return false;
}

bool rl_etx(int key, struct rl_state *s)
{
    s->bufidx = 0;
    s->curidx = 0;
    rl_emit(s, "\n", 1);
    return false;
}

bool rl_completion(int key, struct rl_state *s)
{
    int fd;
    struct dirent de;

    if (s->bufidx == 0) {
        return true;
    }

    if ((fd = open(".", 0)) < 0) {
        printf(2, "readline: cannot open .\n");
        return false;
    }

    char *p;
    if ((p = strchr(s->buf, ' ')) != NULL)
        p++;
    else
        p = s->buf;

    while (read(fd, &de, sizeof(de)) == sizeof(de)) {
        if (de.inum == 0)
            continue;
        if (strlen(de.name) < s->bufidx - (p - s->buf))
            continue;

        for (int i = 0; i < s->bufidx - (p - s->buf); i++) {
            if (de.name[i] != p[i])
                goto end;
        }

        rl_drop_word(key, s);
        if (s->bufidx != 0)
            rl_emit(s, " ", 1);
        rl_emit(s, de.name, strlen(de.name));
        break;
    end:
        continue;
    }

    close(fd);

    return true;
}

bool rl_transition_normal(int key, struct rl_state *s)
{
    rl_transition(s, (void *)key_binds_normal);
    return true;
}

bool rl_transition_escape(int key, struct rl_state *s)
{
    rl_transition(s, (void *)key_binds_escape);
    return true;
}

bool rl_transition_control(int key, struct rl_state *s)
{
    rl_transition(s, (void *)key_binds_control);
    return true;
}

bool rl_drop_all(int key, struct rl_state *s)
{
    while (s->bufidx > 0) {
        s->bufidx--;
        s->curidx = min(s->curidx, s->bufidx);
    }
    return true;
}

bool rl_drop1(int key, struct rl_state *s)
{
    if (s->curidx > 0) {
        memmove(s->buf + s->curidx - 1, s->buf + s->curidx, s->bufidx - s->curidx);
        s->bufidx--;
        s->curidx--;
    }
    return true;
}

bool rl_drop_word(int key, struct rl_state *s)
{
    while (s->curidx > 0 && s->buf[s->curidx - 1] != ' ') {
        rl_drop1(key, s);
    }
    rl_drop1(key, s);
    return true;
}

bool rl_delete(int key, struct rl_state *s)
{
    rl_transition(s, (void *)key_binds_normal);
    if (s->curidx == s->bufidx) {
        return true;
    }

    s->curidx++;
    rl_drop1(key, s);

    return true;
}

bool rl_emit_char(int key, struct rl_state *s)
{
    rl_emit(s, (char *)&key, 1);
    return true;
}

bool rl_newline(int key, struct rl_state *s)
{
    s->curidx = s->bufidx;
    rl_emit(s, "\n", 1);
    return false;
}

char *readline(const char *prompt)
{
    printf(2, "%s", prompt);

    struct rl_state s;
    memset(&s, 0, sizeof(s));
    s.buflen = 128;
    s.buf = malloc(s.buflen);
    s.transitions = (void *)&key_binds_normal;

    uint8_t c;

    while (true) {
        ssize_t r;
        r = read(1, &c, 1);
        if (r < 1)
            break;

        rl_handler *handlers = (rl_handler *)s.transitions;
        rl_handler trans = handlers[c];

        int bufidx = s.bufidx;
        int curidx = s.curidx;

        if (!trans(c, &s))
            break;

        if (bufidx == s.bufidx) {
            if (curidx == s.curidx)
                continue;
            if (curidx == s.curidx - 1) {
                printf(1, "\e[C");
                continue;
            }
            if (curidx == s.curidx + 1) {
                printf(1, "\e[D");
                continue;
            }
        }

        if (s.bufidx == s.curidx) {
            if (bufidx == s.bufidx - 1) {
                printf(1, "%c", s.buf[bufidx]);
                continue;
            }

            if (bufidx == s.bufidx + 1) {
                printf(1, "\b \b");
                continue;
            }
        }

        size_t is = (s.curidx + strlen(prompt)) * 3 + 1;
        int padlength = max(bufidx - s.bufidx, 0);

        char *curm = (char *)malloc(is);
        char *pad = (char *)malloc(padlength + 1);

        assert(curm != NULL, "readline: malloc returned NULL");
        assert(pad != NULL, "readline: malloc returned NULL");

        memset(curm, 0, is);
        for (int i = 0; i < s.curidx + strlen(prompt); i++)
            strcat(curm, "\e[C");

        memset(pad, ' ', padlength);
        ;
        pad[padlength] = 0;

        printf(1, "\r%s%.*s%s\r%s", prompt, s.bufidx, s.buf, pad, curm);

        free(curm);
        free(pad);
    }

    printf(1, "\n");

    if (s.bufidx == 0) {
        free(s.buf);
        return NULL;
    }

    rl_emit(&s, "\0", 2);

    /* remove trailing newline */
    size_t len = strlen(s.buf);
    if (len && s.buf[len - 1] == '\n')
        s.buf[len - 1] = 0;
    return s.buf;
}

void add_history(const char *line)
{
    struct history *h;
    size_t len = strlen(line);
    char *copy;

    copy = malloc(len + 1);
    assert(copy, "malloc failed");
    memcpy(copy, line, len);
    copy[len] = 0;
    h = malloc(sizeof(struct history));
    assert(h, "malloc failed");
    memset(h, 0, sizeof(struct history));
    h->line = copy;
    h->len = len;
    if (history_head == NULL) {
        history_head = h;
    } else {
        assert(history_head->prev == NULL, "prev must be NULL");
        h->next = history_head;
        h->next->prev = h;
        history_head = h;
    }
}

void reset_history(void)
{
    history_head = NULL;
}
