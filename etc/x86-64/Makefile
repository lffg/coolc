AS ?= as
CC ?= clang

TARGET_DIR := target

SOURCES := $(wildcard *.s)

BASENAMES := $(patsubst %.s,%,$(SOURCES))

TARGETS := $(addprefix target/,$(BASENAMES))
RUN_TARGETS := $(addprefix run-,$(BASENAMES))

.PHONY: all clean $(RUN_TARGETS)

all: $(TARGETS)

$(RUN_TARGETS): run-%: $(TARGET_DIR)/%
	./$^

$(TARGET_DIR)/%: %.s
	@mkdir -p $(TARGET_DIR)
	$(AS) -o $@.o $<
	$(CC) -o $@ $@.o

%:
	$(error use `make run-$@` or `make target/$@` instead)

# The 'clean' target removes the build artifact directory.
clean:
	rm -rf $(TARGET_DIR)
