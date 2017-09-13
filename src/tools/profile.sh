#!/usr/bin/env bash

if [ -z "$FREQ" ] ; then FREQ=300 ; fi

perf record -F "$FREQ" --call-graph=dwarf $@

perf script \
  | stackcollapse-perf --kernel \
  | sed 's/caml//g' \
  | flamegraph > perf.svg

