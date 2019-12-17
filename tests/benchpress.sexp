

(prover
  (name mc2-dev)
  (cmd "${cur_dir}/../mc2 --check --time $timeout $file")
  (unsat "Unsat")
  (sat "Sat")
  (unknown "Timeout|Unknown")
  (version "git:."))

(prover
  (name mc2-nogc-dev)
  (cmd "${cur_dir}/../mc2 --check --no-gc --time $timeout $file")
  (unsat "Unsat")
  (sat "Sat")
  (unknown "Timeout|Unknown")
  (version "git:."))

(dir
  (path $cur_dir)
  (pattern ".*\\.(smt2|cnf)")
  (expect (try (run smtlib-read-status) (run z3))))

(task
  (name mc2-local-test)
  (action
    (run_provers
      (provers mc2-dev mc2-nogc-dev z3)
      (timeout 30)
      (dirs))))
