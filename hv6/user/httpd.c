#include "socket.h"
#include "user.h"

#define PORT 80
#define PRODUCT "httpd/0.1"
#define HTTP_VERSION "1.0"

#define E_BAD_REQ 1000

#define BUFFSIZE 1024
#define MAXPENDING 5

enum {
    HTTP_GET = 0,
    HTTP_POST,
};

static const char *http_verbs[] = {
    [HTTP_GET] = "GET",
    [HTTP_POST] = "POST",
};

static int debug = 1;
static int forkclient = 1;

struct http_request {
    int sock;
    struct sockaddr_in *client;
    int verb;
    char *url;
    char *version;
};

struct responce_header {
    int code;
    char *header;
};

struct responce_header headers[] = {
    {200, "HTTP/" HTTP_VERSION " 200 OK\r\n"
          "Server: " PRODUCT "\r\n"},
    {0, 0},
};

struct error_messages {
    int code;
    char *msg;
};

struct error_messages errors[] = {
    {400, "Bad Request"}, {404, "Not Found"},
};

static void die(char *m)
{
    dprintf(2, "httpd: %s\n", m);
    exit();
}

static void req_free(struct http_request *req)
{
    free(req->url);
    free(req->version);
}

static void log(struct http_request *req, int code)
{
    unsigned int hh, mm, ss;
    uint64_t now;

    if (!debug)
        return;
    if (!req->url)
        return;
    now = sys_now() / 1000;
    hh = (now / 3600) % 60;
    mm = (now / 60) % 60;
    ss = now % 60;
    dprintf(1, "%s - - [%02u:%02u:%02u] \"%s %s %s\" %d -\n", inet_ntoa(req->client->sin_addr), hh,
            mm, ss, http_verbs[req->verb], req->url, req->version, code);
}

static ssize_t sendn(int sockfd, const void *buf, size_t len)
{
    ssize_t i = 0, r;

    while (i < len) {
        r = send(sockfd, buf + i, len - i, 0);

        if (r < 0)
            break;
        i += r;
    }
    return i;
}

static int send_header(struct http_request *req, int code)
{
    struct responce_header *h = headers;
    while (h->code != 0 && h->header != 0) {
        if (h->code == code)
            break;
        h++;
    }

    if (h->code == 0)
        return -1;

    int len = strlen(h->header);
    if (sendn(req->sock, h->header, len) != len) {
        die("failed to send bytes to client");
    }

    log(req, code);
    return 0;
}

static int send_data(struct http_request *req, int fd)
{
    char buf[256];
    int n;

    for (;;) {
        n = read(fd, buf, sizeof(buf));
        if (n < 0) {
            dprintf(2, "send_data: read failed: %d\n", n);
            return n;
        } else if (n == 0) {
            return 0;
        }

        if (sendn(req->sock, buf, n) != n)
            die("failed to sent file to client");
    }
}

static int send_size(struct http_request *req, off_t size)
{
    char buf[64];
    size_t n;

    snprintf(buf, sizeof(buf), "Content-Length: %ld\r\n", (long)size);
    n = strlen(buf);

    if (sendn(req->sock, buf, n) != n)
        return -1;

    return 0;
}

static const char *mime_type(const char *file)
{
    char *p = strrchr(file, '.');

    if (p) {
        ++p;
        if (!strcmp(p, "html") || !strcmp(p, "htm"))
            return "text/html";
        if (!strcmp(p, "css"))
            return "text/css";
        if (!strcmp(p, "js"))
            return "text/javascript";
    }

    /* should be application/octet-stream but this is easier for debugging */
    return "text/plain";
}

static int send_content_type(struct http_request *req, const char *type)
{
    char buf[128];
    size_t n;

    snprintf(buf, sizeof(buf), "Content-Type: %s\r\n", type);
    n = strlen(buf);

    if (sendn(req->sock, buf, n) != n)
        return -1;

    return 0;
}

static int send_header_fin(struct http_request *req)
{
    const char *fin = "Connection: close\r\nAccess-Control-Allow-Origin: *\r\n\r\n";
    int fin_len = strlen(fin);

    if (sendn(req->sock, fin, fin_len) != fin_len)
        return -1;

    return 0;
}

static int decode_hex(uint8_t c)
{
    if (c >= '0' && c <= '9')
        return c - '0';
    if (c >= 'A' && c <= 'F')
        return 10 + (c - 'A');
    if (c >= 'a' && c <= 'f')
        return 10 + (c - 'a');
    return 0;
}

static void decode_url(char *t, const char *s, size_t n)
{
    size_t i;

    for (i = 0; i < n; ++i, ++t) {
        switch (s[i]) {
        case '%':
            /* FIXME: sanity check on s */
            *t = decode_hex(s[i + 1]) * 16 + decode_hex(s[i + 2]);
            i += 2;
            break;
        case '+':
            *t = ' ';
            break;
        default:
            *t = s[i];
            break;
        }
    }
    *t = 0;
}

/* given a request, this function creates a struct http_request */
static int http_request_parse(struct http_request *req, char *request)
{
    const char *url;
    const char *version;
    char *query;
    int url_len, version_len;

    if (!req)
        return -1;

    if (!strncmp(request, "GET ", 4)) {
        /* skip GET */
        request += 4;
        req->verb = HTTP_GET;
    } else if (!strncmp(request, "POST ", 5)) {
        /* skip POST */
        request += 5;
        req->verb = HTTP_POST;
    } else {
        return -E_BAD_REQ;
    }

    /* get the url */
    url = request;
    while (*request && *request != ' ')
        request++;
    url_len = request - url;

    req->url = malloc(url_len + 1);
    memmove(req->url, url, url_len);
    req->url[url_len] = '\0';

    /* omit query */
    query = strchr(req->url, '?');
    if (query)
        *query = '\0';

    /* skip space */
    request++;

    version = request;
    while (*request && *request != '\r' && *request != '\n')
        request++;
    version_len = request - version;

    req->version = malloc(version_len + 1);
    memmove(req->version, version, version_len);
    req->version[version_len] = '\0';

    /* no entity parsing */

    return 0;
}

static int send_error(struct http_request *req, int code)
{
    char buf[512];
    size_t n;

    struct error_messages *e = errors;
    while (e->code != 0 && e->msg != 0) {
        if (e->code == code)
            break;
        e++;
    }

    if (e->code == 0)
        return -1;

    snprintf(buf, sizeof(buf), "HTTP/" HTTP_VERSION " %d %s\r\n"
                               "Server: " PRODUCT "\r\n"
                               "Connection: close\r\n"
                               "Content-type: text/html\r\n"
                               "\r\n"
                               "<html><body><p>%d - %s</p></body></html>\r\n",
             e->code, e->msg, e->code, e->msg);
    n = strlen(buf);

    if (sendn(req->sock, buf, n) != n)
        return -1;

    log(req, code);
    return 0;
}

static int send_exec(struct http_request *req)
{
    int r;
    pid_t pid;
    char cmd[512];
    const char *url = req->url;

    /* skip the leading '/' as some browsers already send it */
    if (url[0] == '/')
        ++url;
    decode_url(cmd, url, strlen(url));
#if 0
    dprintf(1, "httpd: %s\n", cmd);
#endif

    r = send_header(req, 200);
    if (r < 0)
        return r;

    r = send_content_type(req, "text/plain");
    if (r < 0)
        return r;

    r = send_header_fin(req);
    if (r < 0)
        return r;

    pid = fork();
    if (pid < 0)
        die("send_exec: fork");
    if (pid) {
        wait();
        return 0;
    }

    /* run the executable */
    if (req->sock != 1) {
        if (dup2(req->sock, 1) < 0)
            die("send_exec: dup 1");
        close(req->sock);
    }
    if (dup2(1, 2) < 0)
        die("send_exec: dup 2");
    r = execl("sh", "sh", cmd, NULL);
    if (r < 0)
        dprintf(1, "exec: %d", r);
    exit();
    return 0;
}

static int send_file(struct http_request *req)
{
    int r;
    off_t file_size = -1;
    int fd;
    struct stat stat;

    /* hack */
    if (req->verb == HTTP_POST)
        return send_exec(req);

    if ((fd = open(req->url, O_RDONLY)) < 0)
        return send_error(req, 404);

    if ((r = fstat(fd, &stat)) < 0) {
        close(fd);
        return send_error(req, 404);
    }

    if (stat.type != T_FILE) {
        close(fd);
        return send_error(req, 404);
    }

    file_size = stat.size;

    if ((r = send_header(req, 200)) < 0)
        goto end;

    if ((r = send_size(req, file_size)) < 0)
        goto end;

    if ((r = send_content_type(req, mime_type(req->url))) < 0)
        goto end;

    if ((r = send_header_fin(req)) < 0)
        goto end;

    r = send_data(req, fd);

end:
    close(fd);
    return r;
}

static int has_newline(const char *buf, size_t n)
{
    const char *p;

    while (n) {
        p = memchr(buf, '\r', n - 1);
        if (!p)
            break;
        ++p;
        if (*p == '\n')
            return 1;
        n -= (p - buf);
        buf = p;
    }

    return 0;
}

static void handle_client(int sock, struct sockaddr_in *client)
{
    struct http_request con_d;
    int r;
    char buffer[BUFFSIZE];
    size_t received = 0;
    struct http_request *req = &con_d;

    while (1) {
        r = recv(sock, buffer + received, sizeof(buffer) - received, 0);
        if (r < 0)
            die("exiting");
        received += r;
        if (!has_newline(buffer, received)) {
            if (received == sizeof(buffer))
                die("no newline found");
            continue;
        }

        memset(req, 0, sizeof(*req));

        req->sock = sock;
        req->client = client;

        r = http_request_parse(req, buffer);
        if (r == -E_BAD_REQ)
            send_error(req, 400);
        else if (r < 0)
            die("parse failed");
        else
            send_file(req);

        req_free(req);

        /* no keep alive */
        break;
    }

    close(sock);
}

int main(int argc, char **argv)
{
    int serversock, clientsock;
    struct sockaddr_in server, client;

    if ((serversock = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP)) < 0)
        die("failed to create socket");

    memset(&server, 0, sizeof(server));
    server.sin_family = AF_INET;
    server.sin_addr.s_addr = htonl(INADDR_ANY);
    server.sin_port = htons(PORT);

    if (bind(serversock, (struct sockaddr *)&server, sizeof(server)) < 0) {
        die("failed to bind the server socket");
    }

    if (listen(serversock, MAXPENDING) < 0)
        die("failed to listen on server socket");

    dprintf(1, "httpd: waiting for http connections...\n");

    while (1) {
        socklen_t clientlen = sizeof(client);

        clientsock = accept(serversock, (struct sockaddr *)&client, &clientlen);
        if (clientsock < 0)
            die("failed to accept client connection");
        if (forkclient) {
            pid_t pid = fork();

            if (pid) {
                close(clientsock);
                while (pid != wait())
                    yield();
            } else {
                handle_client(clientsock, &client);
                exit();
            }
        } else {
            handle_client(clientsock, &client);
        }
    }

    close(serversock);
    return 0;
}
