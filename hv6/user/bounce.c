#include "stat.h"
#include "types.h"
#include "user.h"

int main(int argc, char *argv[])
{
    pid_t self;

    fork();
    self = getpid();
    for (int i = 0;; ++i) printf(1, "Hello from %ld: %d\n", self, i);

}
