#include "socket.h"
#include "user.h"

int main(int argc, char **argv)
{
    const char *url, *path;
    char host[64], buf[512];
    ssize_t i, n;
    struct hostent *hp;
    int sockfd, r;
    struct sockaddr_in addr = {
        .sin_family = PF_INET, .sin_port = htons(80),
    };

    if (argc < 2) {
        dprintf(2, "usage: httpget url\n");
        return 0;
    }
    url = argv[1];

    path = strchr(url, '/');
    if (path) {
        memcpy(host, url, path - url);
        host[path - url] = 0;
    } else {
        strcpy(host, url);
        path = "/";
    }

    hp = gethostbyname(host);
    assert(hp, "gethostbyname");
    addr.sin_addr = *(struct in_addr *)(hp->h_addr);
    dprintf(1, "* Trying %s (%s)\n", hp->h_name, inet_ntoa(addr.sin_addr));

    sockfd = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
    assert(sockfd >= 0, "socket");

    r = connect(sockfd, (const struct sockaddr *)&addr, sizeof(struct sockaddr_in));
    assert(r == 0, "connect");

    /* send http request */
    snprintf(buf, sizeof(buf), "GET %s HTTP/1.0\r\nHost: %s\r\nUser-Agent: curl\r\n\r\n", path, host);
    for (i = 0, n = strlen(buf); i < n;) {
        r = send(sockfd, buf + i, n - i, 0);
        assert(r > 0, "send");
        i += r;
    }
    write(1, buf, n);

    /* print http response */
    while (1) {
        n = recv(sockfd, buf, sizeof(buf), 0);
        if (n <= 0)
            break;
        write(1, buf, n);
    }

    close(sockfd);
    return 0;
}
