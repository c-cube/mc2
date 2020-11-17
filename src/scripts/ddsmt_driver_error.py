#!/usr/bin/python

import subprocess, sys
filename: str = sys.argv[1]

z3_out = subprocess.run([b'z3', filename], capture_output=True).stdout
if b'error' in z3_out:
    sys.exit(0)

p = subprocess.run([b'./blast3.exe', filename], capture_output=True)
if any((x in y) for x in [b'Error:',b'Fatal error'] for y in [p.stdout,p.stderr]):
    print('ohno', file=sys.stderr)
    sys.exit(1)

