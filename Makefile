# copyright (c) 2014, guillaume bury
# copyright (c) 2017, simon cruanes

.PHONY: clean build build-dev

J ?= 3
TIMEOUT ?= 30
TARGETS ?= @install
OPTS ?= -j $(J)

TIME=10s

all: build test

testperf: build
	./src/tests/reluplex/make_relu_example.py > /tmp/test.smt2
	./src/tests/reluplex/match_relu.py /tmp/test.smt2 > /tmp/test_with_relu.smt2
	time yices-smt2 /tmp/test.smt2
	# - ./mc2 -stat /tmp/test.smt2 -time $(TIME)
	# - ./mc2 -stat /tmp/test.smt2 -lra-alt=1 -time $(TIME)
	# - ./mc2 -stat /tmp/test.smt2 -lra-alt=2 -time $(TIME)
	# - ./mc2 -stat /tmp/test.smt2 -lra-alt=3 -time $(TIME)
	# - ./mc2 -stat /tmp/test.smt2 -lra-alt=4 -time $(TIME)
	# - ./mc2 -stat /tmp/test_with_relu.smt2 -time $(TIME)
	# - ./mc2 -stat /tmp/test_with_relu.smt2 -lra-alt=1 -time $(TIME)
	# - ./mc2 -stat /tmp/test_with_relu.smt2 -lra-alt=2 -time $(TIME)
	# - ./mc2 -stat /tmp/test_with_relu.smt2 -lra-alt=3 -time $(TIME)
	# - ./mc2 -stat /tmp/test_with_relu.smt2 -lra-alt=4 -time $(TIME)
	# - ./mc2 -stat /tmp/test_with_relu.smt2 -lra-alt=5 -time $(TIME)
	- ./mc2 -stat /tmp/test_with_relu.smt2 -lra-alt=6 # -time $(TIME)

testrelu: build
	./mc2 src/tests/reluplex/test_relu.smt2 -v 100

testrelu0: build
	./mc2 src/tests/reluplex/test_relu.smt2 -v 0

build:
	@dune build $(TARGETS) $(OPTS) --profile=release

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
