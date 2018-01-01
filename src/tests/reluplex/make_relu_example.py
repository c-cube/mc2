#!/usr/bin/env python3

import numpy as np
from sklearn.neural_network import MLPClassifier
from scipy.special import expit as logistic_sigmoid


# def ReLU(x):
#     return np.maximum(0, x)
# 
# def eval_nn(clf, inp):
#     inp = [[inp]]
#     n = clf.n_layers_ - 2
#     for i, (m, b) in enumerate(zip(clf.coefs_, clf.intercepts_)):
#         inp = np.dot(inp, m) + b
#         inp = ReLU(inp) if i < n else logistic_sigmoid(inp)
#     return inp
#
#
# def f(inp):
#     inp = [[inp]]
#     return clf._predict(inp)


def format_number(x):
    return ('%%.0%sf' % precision) % x if x >= 0 else ('(- %%.0%sf)' % precision) % (-x)


def nn_to_smt2(clf, input_bounds=None, output_bounds=None):
    ans = '(set-logic QF_LRA)\n\n'
    ans += ';; Declare the neuron variables\n'
    layer_sizes = (len(input_bounds),) + \
        clf.hidden_layer_sizes + (len(output_bounds),)
    coefs, bias = clf.coefs_, clf.intercepts_
    n = len(layer_sizes)
    for i in range(n):
        for j in range(layer_sizes[i]):
            ans += '(declare-fun n_%s_%s () Real)\n' % (i, j)
    if input_bounds is not None:
        ans += '\n;; Bound input ranges\n\n'
        for i, (l, u, ll, uu) in enumerate(input_bounds):
            if l is not None:
                ans += '(assert (>= n_0_%s %s))\n' % (i, l)
            if u is not None:
                ans += '(assert (<= n_0_%s %s))\n' % (i, u)
            if ll is not None:
                ans += '(assert (> n_0_%s %s))\n' % (i, ll)
            if uu is not None:
                ans += '(assert (< n_0_%s %s))\n' % (i, uu)
    if output_bounds is not None:
        ans += '\n;; Goal\n\n'
        for i, (l, u, ll, uu) in enumerate(output_bounds):
            if l is not None:
                ans += '(assert (>= n_%s_%s %s))\n' % (n - 1, i, l)
            if u is not None:
                ans += '(assert (<= n_%s_%s %s))\n' % (n - 1, i, u)
            if ll is not None:
                ans += '(assert (> n_%s_%s %s))\n' % (n - 1, i, ll)
            if uu is not None:
                ans += '(assert (< n_%s_%s %s))\n' % (n - 1, i, uu)
    ans += '\n;; Declare the transition rules between neurons\n\n'
    for i in range(1, n):
        ans += ';; Layer %s\n' % i
        for j in range(layer_sizes[i]):
            col = list(map(format_number, coefs[i - 1][:, j]))
            b = format_number(bias[i - 1][j])
            products = [
                '(* n_%s_%s %s)' % (i - 1, k, col[k])
                for k in range(layer_sizes[i - 1])
            ]
            expr = '(+ %s %s)' % (' '.join(products), b)
            if i < n - 1:
                form = '(assert (let ((ws %s)) (= n_%s_%s (ite (>= ws 0) ws 0))))' % (
                    expr, i, j)
            else:
                form = '(assert (let ((ws %s)) (= n_%s_%s ws)))' % (
                    expr, i, j)
            ans += form + '\n'
    ans += '\n(check-sat)\n'
    return ans

precision = 6 # number of decimals
n = 20 # number of samples
k = 1 # dimension
X = np.random.rand(n, k)
y = [1] * (n - 1) + [0]
clf = MLPClassifier(solver='lbfgs', max_iter=100000,
                    hidden_layer_sizes=(5,)*3)
from sys import stderr

clf.fit(X, y)
print(clf.predict(X[-1:]) and 'unsat?' or 'sat?', file=stderr)
# bounds are in the order lower, upper, strict lower, strict upper
print(nn_to_smt2(clf, input_bounds=[
      (0, 1, None, None)] * k, output_bounds=[(None, None, 0, 1)]))
