#!/usr/bin/env python3

import fileinput
import re

with fileinput.input() as f:
    txt = ''.join(f)

print(re.sub(r'\(ite \(>= (\w*) 0\) \1 0\)', r'(relu \1)', txt), end='')
