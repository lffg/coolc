CARGO := cargo

SUBMISSION_PREFIX ?= submission-
SUBMISSION_DIR := submission

.PHONY: bench
bench:
	$(CARGO) bench -p cool-bench

.PHONY: clean
clean:
	rm -rf $(SUBMISSION_DIR)

.PHONY: submit
submit:
ifeq ($(NAME),)
	$(error must provide NAME variable)
endif
	@echo "archiving as directory $(SUBMISSION_PREFIX)$(NAME)"
	mkdir -p $(SUBMISSION_DIR)
	tar -c -z -f $(SUBMISSION_DIR)/$(NAME).tar.gz \
		--transform 's,^,$(SUBMISSION_PREFIX)$(NAME)/,' \
		--exclude=target \
		--exclude=$(SUBMISSION_DIR) \
		.
	uuencode $(SUBMISSION_DIR)/$(NAME).tar.gz $(SUBMISSION_DIR)/$(NAME).tar.gz \
		> $(SUBMISSION_DIR)/$(NAME).u
	@echo "done:"
	ls $(SUBMISSION_DIR)
