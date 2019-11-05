# copyright (c) 2014, guillaume bury
# copyright (c) 2017, simon cruanes

.PHONY: clean build build-dev

J ?= 3
TIMEOUT ?= 30
TARGETS ?= @install
OPTS ?= -j $(J)

build:
	@dune build $(TARGETS) $(OPTS) --profile=release

all: build test

build-install:
	@dune build @install -p mc2

enable_log:
	@cd src/core; ln -sf log_real.ml log.ml

disable_log:
	@cd src/core; ln -sf log_dummy.ml log.ml

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

TESTOPTS ?= -j $(J)
TESTTOOL=logitest
DATE=$(shell date +%FT%H:%M)
FULL_TEST?=QF_UF

logitest-quick:
	@mkdir -p snapshots
	$(TESTTOOL) run -c tests/conf.toml tests/ $(TESTOPTS) \
	  --timeout $(TIMEOUT) \
	  --meta `git rev-parse HEAD` --summary snapshots/quick-$(DATE).txt \
	  --csv snapshots/quick-$(DATE).csv

logitest-full:
	@mkdir -p snapshots
	@DATE=`date +%F.%H:%M`
	@echo "full test on FULL_TEST=$(FULL_TEST)"
	$(TESTTOOL) run -c tests/conf.toml $(FULL_TEST) $(TESTOPTS) \
	  --timeout $(TIMEOUT) \
	  --meta `git rev-parse HEAD` --summary snapshots/full-$(FULL_TEST)-$(DATE).txt \
	  --csv snapshots/full-$(FULL_TEST)-$(DATE).csv

reinstall: uninstall install

ocp-indent:
	@which ocp-indent > /dev/null || { \
	  	echo 'ocp-indent not found; please run `opam install ocp-indent`'; \
		exit 1 ; \
	  }

reindent: ocp-indent
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 echo "reindenting: "
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 ocp-indent -i

watch:
	@dune build $(TARGETS) $(OPTS) -w

.PHONY: clean doc all bench install uninstall remove reinstall enable_log disable_log bin test
