# copyright (c) 2014, guillaume bury
# copyright (c) 2017, simon cruanes

.PHONY: clean build build-dev

TARGETS=src/main.exe
OPTS= -j 3

build:
	jbuilder build $(TARGETS) $(OPTS)

build-dev:
	jbuilder build $(TARGETS) $(OPTS) --dev

enable_log:
	cd src/core; ln -sf log_real.ml log.ml

disable_log:
	cd src/core; ln -sf log_dummy.ml log.ml

clean:
	jbuilder clean

install: lib
	jbuilder install

uninstall:
	jbuilder uninstall

test:
	@echo "run API tests…"
	jbuilder runtest
	@echo "run benchmarks…"
	# @/usr/bin/time -f "%e" ./tests/run smt
	@/usr/bin/time -f "%e" ./src/tests/run mcsat

TESTOPTS ?= -j 3
TESTTOOL=logitest

logitest:
	@mkdir -p snapshots
	$(TESTTOOL) run -c src/tests/conf.toml $(TESTOPTS) \
	  --meta `git rev-parse HEAD` --summary snapshots/`date -I`.txt

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
