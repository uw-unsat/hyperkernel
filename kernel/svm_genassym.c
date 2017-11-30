#include <uapi/assym.h>
#include "svm.h"

ASSYM(VMCB_EXITCODE, offsetof(struct vmcb, ctrl.exitcode));
ASSYM(VMCB_RAX, offsetof(struct vmcb, state.rax));
ASSYM(VMCB_RIP, offsetof(struct vmcb, state.rip));
