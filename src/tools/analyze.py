#!/usr/bin/env python3

import sys, csv

def read_csv(f):
    with open(f) as fd:
        content = fd.readlines()[1:]
    return list(csv.DictReader(content)) 

def analyze_file(f):
    """Analyze result file {f} (which should be a .csv file).
    
    Print per-solver analysis, and errors which happen quickly (true errors, not timeouts).
    """
    print(f"analyze `{f}`")
    table = read_csv(f)
    print(f"read {len(table)} records")
    if not table: return
    provers = [x for x in table[0].keys() if ".time" not in x and x != "problem"]
    print(f"provers: {provers}")
    sat = {}
    unsat = {}
    unknown = {}
    error = {}
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
                if time < 20:
                    quick_errors.append((prover, row['problem'], time))
            else:
                print(f"unknown result for {prover} on {row}: {res}")
    for prover in provers:
        print(f"{prover:{12}}: sat {sat.get(prover,0):6}" \
            f" | unsat {unsat.get(prover,0):6}" \
            f" | solved {sat.get(prover,0)+unsat.get(prover,0):6}" \
            f" | unknown {unknown.get(prover,0):6}" \
            f" | error {error.get(prover,0):6}")

    for (prover,filename,time) in quick_errors:
        print(f"potential error: {prover} on `{filename}` after {time}")

def main() -> ():
    for f in sys.argv[1:]:
        analyze_file(f)

if __name__ == "__main__":
    main()
