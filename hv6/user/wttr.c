#include "user.h"

int main(int argc, char **argv)
{
    execl("httpget", "httpget", "wttr.in/?0", NULL);
    return 0;
}
