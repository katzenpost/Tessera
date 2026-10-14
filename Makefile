# Tessera
#
# Lake does the building; this file collects the things one actually wants to run.

SHELL := /bin/bash
LAKE  ?= lake
BIN   := .lake/build/bin

# Bare `lake build` builds only the library, so the executables are named.
EXES := tessera-test tessera-vterm tessera-demo tessera-bench

# Extra LeanBench flags, e.g. `make bench BENCH_ARGS='--match diff --samples 5'`.
BENCH_ARGS ?=

# Quiet: otherwise Lake replays LeanBench's missing-docstring warnings on every run.
BENCH := $(LAKE) -q --log-level=error exe tessera-bench

.DEFAULT_GOAL := help

.PHONY: all build test sorries ci vterm bench bench-text bench-draw demo clean help

all: build ## build everything, library and executables

# Building tessera-test also checks Tessera/Tests/Axioms.lean and Tessera/Tests/Rejects.lean,
# which fail to compile if a theorem rests on more than Lean's own axioms or if a program that
# must be rejected is accepted.
build: ## build everything, library and executables
	$(LAKE) build --log-level=warning Tessera $(EXES)

test: build ## run the test suites
	@LEAN_ABORT_ON_PANIC=1 $(BIN)/tessera-test

sorries: ## fail if any declaration stands on sorry or native_decide
	@if grep -rnE '\b(sorry|native_decide)\b' --include='*.lean' Tessera examples; then \
	  echo "found sorry or native_decide"; exit 1; \
	else echo "no sorries"; fi

ci: sorries test ## everything CI runs: the proofs, the rejects, the axioms and the suites

# Needs libvterm (Debian and Ubuntu: libvterm-dev), so it is not part of `ci`; CI runs it as a job
# of its own.
vterm: build ## check the output, and every character's width, on libvterm
	cc -O2 -Wall -o $(BIN)/vterm_screen tests/vterm/vterm_screen.c $$(pkg-config --cflags --libs vterm)
	@LEAN_ABORT_ON_PANIC=1 $(BIN)/tessera-vterm $(BIN)/vterm_screen

bench: build ## run every benchmark; pass LeanBench flags via BENCH_ARGS
	@$(BENCH) $(BENCH_ARGS)

bench-text: build ## benchmark filtering and tokenizing untrusted text
	@$(BENCH) --suite text $(BENCH_ARGS)

bench-draw: build ## benchmark layout, diff and redraw of a chat window
	@$(BENCH) --suite draw $(BENCH_ARGS)

demo: build ## run the demo
	@$(BIN)/tessera-demo

clean: ## remove all build artefacts
	$(LAKE) clean

help: ## list the targets
	@grep -hE '^[a-z-]+:.*##' $(MAKEFILE_LIST) \
	  | sed -E 's/:.*## / /' \
	  | awk '{ printf "  \033[36m%-12s\033[0m %s\n", $$1, substr($$0, index($$0, " ") + 1) }'
