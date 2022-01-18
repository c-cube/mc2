# copyright (c) 2014, guillaume bury
# copyright (c) 2017, simon cruanes

.PHONY: clean build build-dev

J ?= 3
TIMEOUT ?= 30
TARGETS ?= @install
OPTS ?= -j $(J) --profile=release

TIME=10s

all: build test

build:
	@dune build $(TARGETS) $(OPTS)

build-install:
	@dune build @install -p mc2

clean:
	@dune clean

install: build-install
	@dune install

uninstall:
	@dune uninstall

doc:
	@dune build @doc -p mc2

test:
	@echo "run API tests…"
	@dune runtest --force --no-buffer
	#@echo "run benchmarks…"
	# @/usr/bin/time -f "%e" ./tests/run smt
	#@/usr/bin/time -f "%e" ./tests/run mcsat

TESTTOOL=benchpress
TESTOPTS ?= -j $(J) -c tests/$(TESTTOOL).sexp --progress
DATE=$(shell date +%FT%H:%M)

snapshots:
	@mkdir -p snapshots

$(TESTTOOL)-quick: snapshots
	$(TESTTOOL) run $(TESTOPTS) \
	  --timeout $(TIMEOUT) \
	  --summary snapshots/quick-$(DATE).txt \
	  --csv snapshots/quick-$(DATE).csv --task mc2-local-test tests/{bugs,hanoi,pigeon,sat,unsat,ssa}

$(TESTTOOL)-full: snapshots
	$(TESTTOOL) run $(TESTOPTS) \
	  --timeout $(TIMEOUT) \
	  --summary snapshots/full-$(DATE).txt \
	  --csv snapshots/full-$(DATE).csv --task mc2-local-test $$home/workspace/smtlib/

$(TESTTOOL)-QF_LRA:
	$(TESTTOOL) run -c tests/benchpress.sexp -t $(TIMEOUT) \
	  --progress -p mc2-dev -p z3 tests/QF_LRA
$(TESTTOOL)-QF_UF:
	$(TESTTOOL) run -c tests/benchpress.sexp -t $(TIMEOUT) \
	  --progress -p mc2-dev -p z3 tests/QF_UF
$(TESTTOOL)-QF_UFLRA:
	$(TESTTOOL) run -c tests/benchpress.sexp -t $(TIMEOUT) \
	  --progress -p mc2-dev -p z3 tests/QF_UFLRA

reinstall: uninstall install

ocp-indent:
	@which ocp-indent > /dev/null || { \
	  	echo 'ocp-indent not found; please run `opam install ocp-indent`'; \
		exit 1 ; \
	  }

reindent: ocp-indent
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 echo "reindenting: "
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 ocp-indent -i

WATCH?=$(TARGETS)
watch:
	@dune build $(WATCH) $(OPTS) -w

.PHONY: clean doc all bench install uninstall remove reinstall enable_log disable_log bin test
