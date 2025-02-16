CARGO := cargo

.PHONY: bench
bench:
	$(CARGO) bench -p cool-bench
