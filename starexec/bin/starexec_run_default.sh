#!/bin/sh
./mc2.exe "$1" -t "$STAREXEC_WALLCLOCK_LIMIT" | sed -e 's/Sat .*/sat/' -e 's/Unsat .*/unsat/'
