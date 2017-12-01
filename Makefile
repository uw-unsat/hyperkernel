-include config.mk

PROJECT      ?= hv6
ARCH         ?= x86_64
O            ?= o.$(ARCH)
NR_CPUS      ?= 1
QEMU_ACCEL   ?= kvm:tcg
QEMU_CPU     ?= max
QEMU_DISPLAY ?= none
# some Ubuntu doesn't have e1000e
QEMU_NIC     ?= e1000
BOCHS_CPU    ?= broadwell_ult
IOMMU        ?= intel-iommu
USE_LL       ?= 0

SRCARCH      := $(ARCH)
ifeq ($(ARCH),x86_64)
SRCARCH      := x86
endif

V             = @
Q             = $(V:1=)
QUIET_CC      = $(Q:@=@echo    '     CC       '$@;)
QUIET_CC_IR   = $(Q:@=@echo    '     CC_IR    '$@;)
QUIET_IRPY    = $(Q:@=@echo    '     IRPY     '$@;)
QUIET_PY2     = $(Q:@=@echo    '     PY2      '$@;)
QUIET_CC_USER = $(Q:@=@echo    '     CC.user  '$@;)
QUIET_LD      = $(Q:@=@echo    '     LD       '$@;)
QUIET_LD_USER = $(Q:@=@echo    '     LD.user  '$@;)
QUIET_GEN     = $(Q:@=@echo    '     GEN      '$@;)
QUIET_CXX     = $(Q:@=@echo    '     C++      '$@;)
QUIET_AR      = $(Q:@=@echo    '     AR       '$@;)
QUIET_RANLIB  = $(Q:@=@echo    '     RANLIB   '$@;)

CFLAGS       += -fno-PIE
CFLAGS       += -ffreestanding -MD -MP
CFLAGS       += -Wall
CFLAGS       += -g
CFLAGS       += -mno-red-zone
CFLAGS       += -mno-sse -mno-mmx -mno-sse2 -mno-3dnow -mno-avx
CFLAGS       += -DCOMMIT_HASH=$(shell git rev-parse --short --verify HEAD)
CFLAGS       += -DCOMMIT_BRANCH=$(shell git rev-parse --abbrev-ref --verify HEAD)
CFLAGS       += -imacros kernel/config.h
CFLAGS       += -I include -I $(O)/include

KERNEL_CFLAGS = $(CFLAGS) -DNR_CPUS=$(NR_CPUS) -fwrapv -I $(PROJECT) -I kernel -I kernel/include

USER_CFLAGS   = $(CFLAGS)

MKDIR_P      := mkdir -p
LN_S         := ln -s
UNAME_S      := $(shell uname -s)
TOP          := $(shell echo $${PWD-`pwd`})
HOST_CC      := cc
PY2          := python2

# Try the latest version first
LLVM_CONFIG  := llvm-config-5.0
ifeq ($(shell which $(LLVM_CONFIG) 2> /dev/null),)
LLVM_CONFIG  := llvm-config
endif
# Homebrew hides llvm here
ifeq ($(shell which $(LLVM_CONFIG) 2> /dev/null),)
LLVM_CONFIG  := /usr/local/opt/llvm/bin/llvm-config
endif
ifeq ($(shell which $(LLVM_CONFIG) 2> /dev/null),)
LLVM_PREFIX  :=
else
LLVM_PREFIX  := "$(shell '$(LLVM_CONFIG)' --bindir)/"
endif
LLVM_CC      += $(LLVM_PREFIX)clang -target $(ARCH)-linux-gnu -Wno-initializer-overrides
LLVM_LINK    := $(LLVM_PREFIX)llvm-link

KERNEL_LDS   := $(O)/kernel/kernel.lds

ARGS := $(wordlist 2,$(words $(MAKECMDGOALS)),$(MAKECMDGOALS))
$(eval $(ARGS):;@:)

all: $(PROJECT)

include irpy/Makefrag
include kernel/Makefrag
include $(PROJECT)/Makefrag

ifeq ($(UNAME_S),Darwin)
USE_CLANG    ?= 1
TOOLPREFIX   ?= $(ARCH)-linux-gnu-
endif

ifdef USE_CLANG
CC           := $(LLVM_CC)
else
CC           := $(TOOLPREFIX)gcc
endif
LD           := $(TOOLPREFIX)ld
AR           := $(TOOLPREFIX)ar
RANLIB       := $(TOOLPREFIX)ranlib
NM           := $(TOOLPREFIX)nm
OBJCOPY      := $(TOOLPREFIX)objcopy
OBJDUMP      := $(TOOLPREFIX)objdump
GDB          := $(TOOLPREFIX)gdb

QEMU         := qemu-system-$(ARCH)
QEMUOPTS     += -M q35,accel=$(QEMU_ACCEL),kernel-irqchip=split -cpu $(QEMU_CPU)
QEMUOPTS     += -serial mon:stdio -s
QEMUOPTS     += -display $(QEMU_DISPLAY)
QEMUOPTS     += -smp cpus=$(NR_CPUS)
QEMUOPTS     += -device isa-debug-exit
QEMUOPTS     += -debugcon file:/dev/stdout
QEMUOPTS     += -netdev user,id=net0,hostfwd=tcp::10007-:7,hostfwd=tcp::10080-:80,hostfwd=tcp::5900-:5900
QEMUOPTS     += -device $(QEMU_NIC),netdev=net0 -object filter-dump,id=filter0,netdev=net0,file=$(O)/qemu.pcap
QEMUOPTS     += -device $(IOMMU),intremap=on

ifdef QEMUEXTRA
QEMUOPTS     += $(QEMUEXTRA)
endif

all: $(PROJECT)

verify: $(PROJECT)-verify

qemu: $(PROJECT)-qemu

bochs: iso
	CPU=$(BOCHS_CPU) NR_CPUS=$(NR_CPUS) ISO=$(O)/$(PROJECT).iso bochs -q -f boot/bochsrc

grub-iso: $(PROJECT)
	$(Q)$(MKDIR_P) $(O)/hv6/iso/boot/grub
	echo 'set default=0' > $(O)/hv6/iso/boot/grub/grub.cfg
	echo 'set timeout=3' >> $(O)/hv6/iso/boot/grub/grub.cfg
	echo 'menuentry "hv6" { multiboot /boot/kernel }' >> $(O)/hv6/iso/boot/grub/grub.cfg
	cp $(HV6_BIN) $(O)/hv6/iso/boot/kernel
	grub-mkrescue -o $(O)/hv6-grub.iso $(O)/hv6/iso

iso: $(PROJECT)
	-rm -rf $(O)/$(PROJECT)/iso
	$(Q)$(MKDIR_P) $(O)/$(PROJECT)/iso
	$(Q)cp -r boot/isolinux $(O)/$(PROJECT)/iso/
	$(Q)cp $(O)/$(PROJECT).bin $(O)/$(PROJECT)/iso/
	$(Q)echo 'default mboot.c32 /$(PROJECT).bin' > $(O)/$(PROJECT)/iso/isolinux.cfg
	$(Q)mkisofs -r -f -o $(O)/$(PROJECT).iso -b isolinux/isolinux.bin -c isolinux/boot.cat -no-emul-boot -boot-load-size 4 -boot-info-table $(O)/$(PROJECT)/iso
	$(Q)./scripts/isohybrid.pl $(O)/$(PROJECT).iso

burn-iso: iso
	@echo; \
	if [ `uname -s` = 'Darwin' ]; then \
		diskutil list external physical; \
	else lsblk; fi; \
	echo; \
	read -p "Choose a disk> " disk; \
	if [ ! -b "$$disk" ]; then \
		echo "$$disk not a block device"; \
	else \
		cmd="sudo dd if=$(O)/$(PROJECT).iso of=\"$$disk\""; \
		if [ `uname -s` = 'Darwin' ]; then \
			cmd="diskutil unmountDisk \"$$disk\"; $$cmd"; \
		fi; \
		echo "WARNING: Improperly specifying disk may result in loss of data."; \
		echo; \
		echo $$cmd; \
		read -p "Execute command? (y/n) " choice; \
		case "$$choice" in \
			y|Y ) eval $$cmd;; \
			* ) echo "Aborting";; \
		esac; \
	fi;

tar:
	tar czf $(PROJECT).tar.gz README.md Makefile boot drivers include irpy kernel lib scripts user web .gitignore $(PROJECT)

%.asm: %.elf
	$(QUIET_GEN)$(OBJDUMP) -S $< > $@

%.bin: %.elf
	$(QUIET_GEN)$(OBJCOPY) -O binary $< $@

%.map: %.elf
	$(QUIET_GEN)$(NM) -n $< > $@

$(O)/user/%.o: user/%.S
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC_USER)$(CC) -o $@ -c $(USER_CFLAGS) $<

$(O)/user/%.o: user/%.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC_USER)$(CC) -o $@ -c $(USER_CFLAGS) $<

$(O)/%.o: %.S
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(CC) -o $@ -c $(KERNEL_CFLAGS) $<

$(O)/%.o: %.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC)$(CC) -o $@ -c $(KERNEL_CFLAGS) $<

$(O)/kernel/%.o: KERNEL_CFLAGS += -I $(dir $@)

$(O)/%assym.h: $(O)/%genassym.o
	$(QUIET_GEN)NM=$(NM) scripts/genassym.sh $< > $@

$(O)/%.ll: %.c
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_CC_IR)$(LLVM_CC) -o $@~ -c -S -emit-llvm $(KERNEL_CFLAGS) -O2 $<
	$(Q)./scripts/no_undef.sh $@~
	$(Q)mv $@~ $@

$(O)/%.py: $(O)/%.ll irpy/compiler/irpy
	$(Q)$(MKDIR_P) $(@D)
	@touch $(join $(dir $@), __init__.py)
	$(QUIET_IRPY)./irpy/compiler/irpy "$<" > "$@"

$(O)/%.lds: %.lds.S
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_GEN)$(CPP) -o $@ -P $(KERNEL_CFLAGS) $<

$(O)/%.dtb: %.dts
	$(Q)$(MKDIR_P) $(@D)
	$(QUIET_GEN)dtc -o $@ -O dtb $<

clean:
	-rm -rf $(O)

format:
	find . -regextype egrep -regex '.*\.(c|h|cc|hh|cpp)$$' -not -path './user/lwip/*' -print -exec clang-format -style=file -i {} \;

.PHONY: kernel qemu qemu-gdb bochs iso tar gdb clean tags check irpy verify esp format

