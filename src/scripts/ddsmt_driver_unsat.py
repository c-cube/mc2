#!/usr/bin/python

import subprocess, sys
expect = 'UNSAT'

filename: str = sys.argv[1]

z3_out = subprocess.run([b'z3', filename], capture_output=True).stdout
if b'unsat' not in z3_out or b'error' in z3_out:
    sys.exit(0)

b_out = subprocess.run([b'./blast3.exe', filename], capture_output=True).stdout
if b_out.startswith(b'SAT') and b'Error' not in b_out:
    print('ohno', file=sys.stderr)
    sys.exit(1)

