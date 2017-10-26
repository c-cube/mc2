#!/usr/bin/env python3

import sys, csv, argparse

def read_csv(f):
    with open(f) as fd:
        content = fd.readlines()[1:]
    return list(csv.DictReader(content)) 

def analyze_file(f, potential_errors=False):
    """Analyze result file {f} (which should be a .csv file).
    
    Print per-solver analysis, and errors which happen quickly (true errors, not timeouts).
    """
    print(f"## analyze `{f}`")
    table = read_csv(f)
    print(f"read {len(table)} records")
    if not table: return
    provers = [x for x in table[0].keys() if ".time" not in x and x != "problem"]
    print(f"provers: {provers}")
    sat = {}
    unsat = {}
    unknown = {}
    error = {}
    if potential_errors:
        quick_errors = []
    for row in table:
        for prover in provers:
            res = row[prover]
            if res == 'unsat':
                unsat[prover] = 1 + unsat.get(prover, 0)
            elif res == 'sat':
                sat[prover] = 1 + sat.get(prover, 0)
            elif res == 'unknown':
                unknown[prover] = 1 + unknown.get(prover, 0)
            elif res == 'error':
                error[prover] = 1 + error.get(prover, 0)
                time = float(row[prover + '.time'])
                if potential_errors and time < 5:
                    quick_errors.append((prover, row['problem'], time))
            else:
                print(f"unknown result for {prover} on {row}: {res}")
    for prover in provers:
        print(f"{prover:{12}}: sat {sat.get(prover,0):6}" \
            f" | unsat {unsat.get(prover,0):6}" \
            f" | solved {sat.get(prover,0)+unsat.get(prover,0):6}" \
            f" | unknown {unknown.get(prover,0):6}" \
            f" | error {error.get(prover,0):6}")

    if potential_errors:
        for (prover,filename,time) in quick_errors:
            print(f"potential error: {prover} on `{filename}` after {time}")

def main(files, potential_errors=False) -> ():
    for f in files:
        analyze_file(f, potential_errors=potential_errors)

if __name__ == "__main__":
    p = argparse.ArgumentParser('analyze result files')
    p.add_argument('files', nargs='+', help='files to analyze')
    p.add_argument('--errors', dest='potential_errors', \
            action='store_true', help='detect potential errors')
    args = p.parse_args()
    main(files=args.files, potential_errors=args.potential_errors)
