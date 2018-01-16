import subprocess
import re

mc2 = '/Users/louisabraham/github/mc2/mc2'
make_relu_example = '/Users/louisabraham/github/mc2/src/tests/reluplex/make_relu_example.py'
match_relu = '/Users/louisabraham/github/mc2/src/tests/reluplex/match_relu.py'

test = '/tmp/test.smt2'
test_with_relu = '/tmp/test_with_relu.smt2'


def generate_example(hidden):
    with open(test, 'w') as f:
        err = subprocess.run([make_relu_example, '--hidden=%s' % hidden], stdout=f,
                             stderr=subprocess.PIPE).stderr
        if err not in (b'unsat?\n', b'sat?\n'):
            print(err.decode())
            raise Exception
    with open(test_with_relu, 'w') as f:
        subprocess.run([match_relu, test], stdout=f)


def get_time(out):
    out = out.strip()
    # if out == 'Timeout':
    #     return None
    m = re.match('(Sat|Unsat) \(\d+\.\d+/(\d+\.\d+)/\d+\.\d+\)', out)
    return float(m.group(2))


def bench(file, lra_alt=None, timeout=None):
    command = [mc2, file]
    if lra_alt is not None:
        command.append('-lra-alt=%s' % lra_alt)
    if timeout is not None:
        command.append('-time=%ss' % timeout)
    proc = subprocess.run(command, stdout=subprocess.PIPE)
    if proc.returncode == 2:
        assert proc.stdout.decode().strip() == 'Timeout'
        return None
    return get_time(proc.stdout.decode())


timeout = [0, 0, 0, 0]
time = [0, 0, 0, 0]
for i in range(10):
    generate_example('15,15')
    for i, t in enumerate([
            bench(test, 0, 20),
            bench(test, 6, 20),
            bench(test_with_relu, 0, 20),
            bench(test_with_relu, 0, 20)]
    ):
        if t is None:
            timeout[i] += 1
        else:
            time[i] += t
print(timeout)
print(time)
