

(prover
  (name mc2-dev)
  (binary "${cur_dir}/../mc2.exe")
  (cmd "${cur_dir}/../mc2.exe --check --time $timeout $file")
  (unsat "Unsat")
  (sat "Sat")
  (unknown "Timeout|Unknown")
  (version "git:."))

(prover
  (name mc2-nogc-dev)
  (binary "${cur_dir}/../mc2.exe")
  (cmd "${cur_dir}/../mc2.exe --check --no-gc --time $timeout $file")
  (unsat "Unsat")
  (sat "Sat")
  (unknown "Timeout|Unknown")
  (version "git:."))

(dir
  (path $cur_dir)
  (pattern ".*\\.(smt2|cnf)")
  (expect (try (run smtlib-read-status) (run z3) (const unknown))))

(task
  (name mc2-local-test)
  (synopsis "run mc2 on directories provided on the command line")
  (action
    (run_provers
      (provers mc2-dev mc2-nogc-dev z3)
      (timeout 30)
      (dirs))))

(task
  (name mc2-all-tests)
  (synopsis "run mc2 on all files in tests/")
  (action
    (run_provers
      (provers mc2-dev z3)
      (timeout 30)
      (dirs $cur_dir))))

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
