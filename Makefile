# copyright (c) 2014, guillaume bury
# copyright (c) 2017, simon cruanes

.PHONY: clean build build-dev

J?=3
TIMEOUT?=30
TARGETS=src/main.exe
OPTS= -j $(J)

testrelu: build
	./mc2 src/tests/reluplex/test_relu.smt2 -v 100
	
build:
	jbuilder build $(TARGETS) $(OPTS)

build-install:
	jbuilder build @install

build-dev:
	jbuilder build $(TARGETS) $(OPTS) --dev

enable_log:
	cd src/core; ln -sf log_real.ml log.ml

disable_log:
	cd src/core; ln -sf log_dummy.ml log.ml

clean:
	jbuilder clean

install: build-install
	jbuilder install

uninstall:
	jbuilder uninstall

doc:
	jbuilder build @doc

test:
	@echo "run API tests…"
	jbuilder runtest
	@echo "run benchmarks…"
	# @/usr/bin/time -f "%e" ./tests/run smt
	# @/usr/bin/time -f "%e" ./src/tests/run mcsat
	@/opt/local/bin/gtime -f "%e" ./src/tests/run

TESTOPTS ?= -j $(J)
TESTTOOL=logitest
DATE=$(shell date +%FT%H:%M)
FULL_TEST?=QF_UF

logitest-quick:
	@mkdir -p snapshots
	$(TESTTOOL) run -c src/tests/conf.toml src/tests/ $(TESTOPTS) \
	  --timeout $(TIMEOUT) \
	  --meta `git rev-parse HEAD` --summary snapshots/quick-$(DATE).txt \
	  --csv snapshots/quick-$(DATE).csv

logitest-full:
	@mkdir -p snapshots
	@DATE=`date +%F.%H:%M`
	@echo "full test on FULL_TEST=$(FULL_TEST)"
	$(TESTTOOL) run -c src/tests/conf.toml $(FULL_TEST) $(TESTOPTS) \
	  --timeout $(TIMEOUT) \
	  --meta `git rev-parse HEAD` --summary snapshots/full-$(FULL_TEST)-$(DATE).txt \
	  --csv snapshots/full-$(FULL_TEST)-$(DATE).csv

reinstall: | uninstall install

ocp-indent:
	@which ocp-indent > /dev/null || { \
	  	echo 'ocp-indent not found; please run `opam install ocp-indent`'; \
		exit 1 ; \
	  }

reindent: ocp-indent
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 echo "reindenting: "
	@find src '(' -name '*.ml' -or -name '*.mli' ')' -print0 | xargs -0 ocp-indent -i

watch:
	while find src/ -print0 | xargs -0 inotifywait -e delete_self -e modify ; do \
		echo "============ at `date` ==========" ; \
		make build-dev ; \
	done

.PHONY: clean doc all bench install uninstall remove reinstall enable_log disable_log bin test
