#include <uapi/psf.h>
#include "socket.h"
#include "user.h"

#define PORT 5900

#define WIDTH 640
#define HEIGHT 480

#define SECURITY_NONE 1
#define SECURITY_RES_OK 0

#define ENCODING_RAW 0
#define ENCODING_COPYRECT 1

#define PSF_FILE "ter-x16n.psf"

const char *rfb_version = "RFB 003.008\n";

struct ClientInit {
    uint8_t shared;
} __packed;

struct PixelFormat {
    uint8_t bits_per_pixel;
    uint8_t depth;
    uint8_t big_endian;
    uint8_t true_color;
    uint16_t red_max;
    uint16_t green_max;
    uint16_t blue_max;
    uint8_t red_shift;
    uint8_t green_shift;
    uint8_t blue_shift;
    uint8_t padding_0[3];
} __packed;

static struct PixelFormat format = {
    .bits_per_pixel = 8,
    .depth = 8,
    .big_endian = 0,
    .true_color = 1,
    .red_max = htons(0x3),
    .green_max = htons(0x3),
    .blue_max = htons(0x3),
    .red_shift = 4,
    .green_shift = 2,
    .blue_shift = 0,
    .padding_0 = {0},
};

struct ServerInit {
    uint16_t fbwidth;
    uint16_t fbheight;
    struct PixelFormat format;
    uint32_t name_length;
    uint8_t name[3];
} __packed;

enum ClientMessageType {
    SetPixelFormat = 0,
    SetEncodings = 2,
    FramebufferUpdateRequest = 3,
    KeyEvent = 4,
    PointerEvent = 5,
    ClientCutText = 6,
};

enum ServerMessageType {
    FramebufferUpdate = 0,
    SetColorMapEntries = 1,
    Bell = 2,
    ServerCutText = 3,
};

struct SetPixelFormat {
    uint8_t padding_0[3];
    struct PixelFormat format;
} __packed;

struct FramebufferUpdateRequest {
    uint8_t incremental;
    uint16_t xpos;
    uint16_t ypos;
    uint16_t width;
    uint16_t height;
} __packed;

struct KeyEvent {
    uint8_t down;
    uint8_t padding_0[2];
    uint32_t key;
} __packed;

struct PointerEvent {
    uint8_t button_mask;
    uint16_t xpos;
    uint16_t ypos;
} __packed;

struct ClientCutText {
    uint8_t padding_0[3];
    uint32_t length;
} __packed;

struct SetEncodings {
    uint8_t padding_0[1];
    uint16_t number_of_encodings;
} __packed;

struct FramebufferUpdate {
    uint8_t padding_0[1];
    uint16_t num_rectangles;
} __packed;

struct RectangleHeader {
    uint16_t xpos;
    uint16_t ypos;
    uint16_t width;
    uint16_t height;
    int32_t encoding;
} __packed;

noreturn static void die(char *m)
{
    dprintf(2, "vncd: %s\n", m);
    exit();
}

static ssize_t sendn(int sockfd, const void *buf, size_t len)
{
    ssize_t i = 0, r;

    while (i < len) {
        r = send(sockfd, buf + i, len - i, 0);

        if (r <= 0)
            break;
        i += r;
    }
    return i;
}

static ssize_t recvn(int sockfd, void *buf, size_t len)
{
    size_t received = 0;

    while (received < len) {
        ssize_t r = recv(sockfd, buf + received, len - received, 0);
        if (r < 0)
            die("exiting");
        received += r;
    }
    return received;
}

static struct psf2_header psf2;
static uint8_t *glyphs;

static void load_font(void)
{
    int fd;
    size_t n, size;

    fd = open(PSF_FILE, O_RDONLY);
    assert(fd >= 0, "open file failed");

    n = pread(fd, &psf2, sizeof(psf2), 0);
    assert(n == sizeof(psf2), "pread");
    if (psf2.magic[0] != PSF2_MAGIC0 ||
        psf2.magic[1] != PSF2_MAGIC1 ||
        psf2.magic[2] != PSF2_MAGIC2 ||
        psf2.magic[3] != PSF2_MAGIC3)
        panic("psf2 magic mismatched");

    assert(psf2.charsize == psf2.height * ((psf2.width + 7) / 8), "charsize = height * ((width + 7) / 8");
    dprintf(1, "vncd: %u %ux%u glyphs\n", psf2.length, psf2.width, psf2.height);

    size = psf2.charsize * psf2.length;
    glyphs = malloc(size);
    n = pread(fd, glyphs, size, psf2.headersize);
    assert(n == size, "pread glyphs");
    close(fd);
}

static void handle_client(int);

int main(int argc, char **argv)
{
    int serversock, clientsock;
    struct sockaddr_in server, client;

    load_font();

    if ((serversock = socket(PF_INET, SOCK_STREAM, IPPROTO_TCP)) < 0)
        die("failed to create socket");

    memset(&server, 0, sizeof(server));
    server.sin_family = AF_INET;
    server.sin_addr.s_addr = htonl(INADDR_ANY);
    server.sin_port = htons(PORT);

    if (bind(serversock, (struct sockaddr *)&server, sizeof(server)) < 0) {
        die("failed to bind the server socket");
    }

    if (listen(serversock, 1) < 0)
        die("failed to listen on server socket");

    dprintf(1, "vncd: waiting for vnc connections...\n");


    while(1) {
        socklen_t clientlen = sizeof(client);
        pid_t pid;

        clientsock = accept(serversock, (struct sockaddr *)&client, &clientlen);
        if (clientsock < 0)
            die("failed to accept client connection");

        pid = fork();
        if (pid) {
            close(clientsock);
            while (pid != wait())
                yield();
        } else {
            dprintf(1, "vncd: client connected from %s\n", inet_ntoa(client.sin_addr));
            handle_client(clientsock);
            exit();
        }
    }

    close(serversock);
    return 0;
}

void set_pixel_format(int clientsock, struct SetPixelFormat *mesg)
{
#if 0
    dprintf(1, "SetPixelFormat\n");
#endif
    format = mesg->format;
    dprintf(1, "vncd: bits-per-pixel: %d\n", format.bits_per_pixel);
    if (format.bits_per_pixel != 8) {
        dprintf(2, "vncd: unsupported format!\n");
        exit();
    }
    return;
}

static uint8_t vgabuf[HEIGHT][WIDTH];

static void draw_char(int row, int col, uint8_t ch)
{
    uint8_t *data = &glyphs[ch * psf2.charsize], color;
    int x, y;

    for (y = 0; y < 16; ++y) {
        for (x = 0; x < 8; ++x) {
            color = (data[y] & (1U << (8 - x))) ? 0xff : 0;
            if (ch == 0)
                color = 0;
            vgabuf[row * 16 + y][col * 8 + x] = color;
        }
    }
}

static void draw_cursor(int row, int col)
{
    static int blink;
    uint8_t color = 0xff;
    int x, y;

    if (blink) {
        blink = 0;
        return;
    }

    blink = 1;

    for (y = 0; y < 16; ++y) {
        for (x = 0; x < 8; ++x) {
            vgabuf[row * 16 + y][col * 8 + x] = color;
        }
    }
}

void framebuffer_update_request(int clientsock, struct FramebufferUpdateRequest *mesg)
{
#if 0
    dprintf(1, "FramebufferUpdateRequest\n");
#endif

    uint8_t type = FramebufferUpdate;
    sendn(clientsock, &type, 1);

    struct FramebufferUpdate update = {
        .padding_0 = {0}, .num_rectangles = htons(1),
    };
    sendn(clientsock, &update, sizeof(update));

    struct RectangleHeader rect_hdr = {
        .xpos = htons(0),
        .ypos = htons(0),
        .width = htons(WIDTH),
        .height = htons(HEIGHT),
        .encoding = htonl(ENCODING_RAW),
    };
    sendn(clientsock, &rect_hdr, sizeof(rect_hdr));

#if 0
    static int counter = 0;
    for (int row = 0; row < HEIGHT; ++row) {
        for (int col = 0; col < WIDTH; ++col) {
            vgabuf[row][col] = (row + col + counter) % 256;
        }
    }
    counter += 10;
#else
    int pos, row, col;
    uint8_t *buf;

    buf = membuf(&pos);
    for (row = 0; row < 25; ++row) {
        for (col = 0; col < 80; ++col) {
            draw_char(row, col, *buf);
            ++buf;
        }
    }
    draw_cursor(pos / 80, pos % 80);
#endif

    sendn(clientsock, vgabuf, sizeof(vgabuf));
}

void pointer_event(int clientsock, struct PointerEvent *mesg)
{
    dprintf(1, "PointerEvent\n");
}

void key_event(int clientsock, struct KeyEvent *mesg)
{
    dprintf(1, "KeyEvent\n");
}

void set_encodings(int clientsock, struct SetEncodings *mesg)
{
    uint16_t num = ntohs(mesg->number_of_encodings);
    dprintf(1, "vncd: client num of encodings: %d\n", num);
    int32_t *encodings = (int32_t *)malloc(num * sizeof(int32_t));
    if (recvn(clientsock, encodings, num * sizeof(int32_t)) < 0)
        die("failed to get encodings");
    dprintf(1, "vncd: client supported encodings: ");
    for (int i = 0; i < num; ++i) {
        encodings[i] = ntohl(encodings[i]);
        dprintf(1, "%d, ", encodings[i]);
    }
    dprintf(1, "\n");
    free(encodings);
    return;
}

void client_cut_text(int clientsock, struct ClientCutText *mesg)
{
    dprintf(1, "ClientCutText\n");
    die("cut");
}

static void update_loop(int clientsock)
{
    uint8_t buf[256];
    for (;;) {
        uint8_t message_type;
        if (recvn(clientsock, &message_type, 1) != 1)
            die("failed to get message type");

        size_t size;
        switch (message_type) {
        case SetPixelFormat:
            size = sizeof(struct SetPixelFormat);
            break;
        case SetEncodings:
            size = sizeof(struct SetEncodings);
            break;
        case FramebufferUpdateRequest:
            size = sizeof(struct FramebufferUpdateRequest);
            break;
        case PointerEvent:
            size = sizeof(struct PointerEvent);
            break;
        case KeyEvent:
            size = sizeof(struct KeyEvent);
            break;
        case ClientCutText:
            size = sizeof(struct ClientCutText);
            break;
        default:
            die("Unknown message type");
        }

        if (recvn(clientsock, &buf, size) != size)
            die("failed to get message");

        switch (message_type) {
        case SetPixelFormat:
            set_pixel_format(clientsock, (struct SetPixelFormat *)buf);
            break;
        case SetEncodings:
            set_encodings(clientsock, (struct SetEncodings *)buf);
            break;
        case FramebufferUpdateRequest:
            framebuffer_update_request(clientsock, (struct FramebufferUpdateRequest *)buf);
            break;
        case PointerEvent:
            pointer_event(clientsock, (struct PointerEvent *)buf);
            break;
        case KeyEvent:
            key_event(clientsock, (struct KeyEvent *)buf);
            break;
        case ClientCutText:
            client_cut_text(clientsock, (struct ClientCutText *)buf);
            break;
        }
    }
}

static void handle_client(int clientsock)
{
    sendn(clientsock, rfb_version, strlen(rfb_version));

    char client_version[13];
    client_version[12] = '\0';
    if (recvn(clientsock, client_version, 12) < 0)
        die("failed to get client version");
    dprintf(1, "vncd: client version %s\n", client_version);

    uint8_t sec_info[] = {1, SECURITY_NONE};
    sendn(clientsock, sec_info, 2);

    char client_sec;
    if (recvn(clientsock, &client_sec, 1) < 0)
        die("failed to get client security level");
    if (client_sec != SECURITY_NONE)
        die("client not using SECURITY_NONE");
    dprintf(1, "vncd: client security: SECURITY_NONE\n");

    uint32_t sec_res = SECURITY_RES_OK;
    sec_res = htonl(sec_res);
    sendn(clientsock, &sec_res, sizeof(sec_res));

    struct ClientInit client_init;
    if (recvn(clientsock, &client_init, sizeof(client_init)) < 0)
        die("failed to receive client init");
    dprintf(1, "vncd: client shared flag: %d\n", client_init.shared);

    struct ServerInit server_init = {
        .fbwidth = htons(WIDTH),
        .fbheight = htons(HEIGHT),
        .format = format,
        .name_length = htonl(3),
        .name = {'h', 'v', '6'},
    };

    sendn(clientsock, &server_init, sizeof(server_init));
    update_loop(clientsock);
}
