#include "socket.h"
#include "user.h"

/* RFC 867: Daytime Protocol */
#define SERVER_HOST "utcnist.colorado.edu"
#define SERVER_PORT 13

int main(int argc, char **argv)
{
    struct hostent *hp;
    int sockfd, r;
    struct sockaddr_in addr = {
        .sin_family = PF_INET, .sin_port = htons(SERVER_PORT),
    };

    hp = gethostbyname(SERVER_HOST);
    assert(hp, "gethostbyname");
    addr.sin_addr = *(struct in_addr *)(hp->h_addr);
    dprintf(1, "daytime: %s %s\n", hp->h_name, inet_ntoa(addr.sin_addr));

    sockfd = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP);
    assert(sockfd >= 0, "socket");

    r = connect(sockfd, (const struct sockaddr *)&addr, sizeof(struct sockaddr_in));
    assert(r == 0, "connect");

    while (1) {
        char buf[512];
        ssize_t n;

        n = recv(sockfd, buf, sizeof(buf), 0);
        if (n <= 0)
            break;
        write(1, buf, n);
    }

    close(sockfd);
    return 0;
}
