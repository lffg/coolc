AS ?= as
CC ?= clang
RUST ?= rustc

TARGET_DIR := target

SOURCES := $(wildcard *.rs)

BASENAMES := $(patsubst %.rs,%,$(SOURCES))

TARGETS := $(addprefix target/,$(BASENAMES))
RUN_TARGETS := $(addprefix run-,$(BASENAMES))

.PHONY: all clean $(RUN_TARGETS)

all: $(TARGETS)

$(RUN_TARGETS): run-%: $(TARGET_DIR)/%
	./$^

$(TARGET_DIR)/%: %.rs
	@mkdir -p $(TARGET_DIR)
	$(RUST) --emit=asm -C panic=abort -C overflow-checks=off -C llvm-args='--x86-asm-syntax=intel' --edition 2021 -o $@.s $<
	$(AS) -o $@.o $@.s
	$(CC) -o $@ $@.o

%:
	$(error use `make run-$@` or `make target/$@` instead)

# The 'clean' target removes the build artifact directory.
clean:
	rm -rf $(TARGET_DIR)
