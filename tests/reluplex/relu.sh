#!/bin/sh

./make_relu_example.py > test_relu1.smt2 && time yices-smt2 test_relu1.smt2 && ../../../mc2 test_relu1.smt2 -time 20s
./match_relu.py test_relu1.smt2 > test_relu2.smt2
../../../mc2 test_relu2.smt2 -time 20s