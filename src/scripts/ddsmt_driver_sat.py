#!/usr/bin/python

import subprocess, sys

filename: str = sys.argv[1]

z3_out = subprocess.run([b'z3', filename], capture_output=True).stdout
if z3_out != b'unsat\n':
    sys.exit(0)

b_out = subprocess.run([b'./mc2.exe', filename], capture_output=True).stdout
if b_out.startswith(b'Sat') and b'Error' not in b_out:
    print('ohno', file=sys.stderr)
    sys.exit(1)

