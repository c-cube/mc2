#!/usr/bin/env python3

import fileinput
import re

with fileinput.input() as f:
    txt = ''.join(f)

print(re.sub(r'\(relu ([^) ]*)\)', r'(ite (>= \1 0) \1 0)', txt), end='')
