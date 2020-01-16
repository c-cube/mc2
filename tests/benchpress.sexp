

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

(task
  (name mc2-ci)
  (synopsis "pull last commit, build it, and run basic tests")
  (action
    (progn
      (run_cmd "git pull origin master --ff-only")
      (git_checkout (dir $cur_dir) (ref "master"))
      (run_cmd "dune build @install -p mc2")
      (run_provers
        (provers mc2-dev)
        (timeout 10)
        (dirs $cur_dir/tests/sat $cur_dir/tests/unsat)))))
