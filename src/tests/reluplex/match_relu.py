#!/usr/bin/env python3

import fileinput
import re

with fileinput.input() as f:
    txt = ''.join(f)

print(re.sub(r'\(= (\w*) \(ite \(>= (\w*) 0\) \2 0\)\)', r'(relu \2 \1)', txt), end='')
