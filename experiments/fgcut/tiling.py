"""Sum of volumes of the realized maximal chains of N_P × N_Q equals vol(Δ^{k-1} × Δ^{l-1})?"""
import itertools, sys
from fractions import Fraction
from math import factorial
import sympy
def subsets(n): return [frozenset(c) for r in range(1, n+1) for c in itertools.combinations(range(n), r)]
def bary(S, n): return [Fraction(1 if i in S else 0, len(S)) for i in range(n)]
def run(k, l):
    cells = [(A, B) for A in subsets(k) for B in subsets(l)]
    le = lambda c, d: c[0] >= d[0] and c[1] <= d[1]
    # maximal chains: start from minimal cells ([k],{j}), cover steps
    def covers(c):
        A, B = c
        return [(A - {i}, B) for i in A if len(A) > 1] + [(A, B | {j}) for j in range(l) if j not in B]
    chains = []
    def ext(ch):
        cs = covers(ch[-1])
        if not cs: chains.append(ch); return
        for d in cs: ext(ch + [d])
    for j in range(l): ext([(frozenset(range(k)), frozenset([j]))])
    d = (k - 1) + (l - 1)
    tot = Fraction(0); degenerate = 0
    for ch in chains:
        assert len(ch) == d + 1
        pts = [bary(A, k)[:-1] + bary(B, l)[:-1] for A, B in ch]
        M = sympy.Matrix([[p[i] - pts[0][i] for i in range(d)] for p in pts[1:]])
        v = abs(M.det()) / factorial(d)
        if v == 0: degenerate += 1
        tot += Fraction(str(v))
    target = Fraction(1, factorial(k - 1) * factorial(l - 1))
    print((k, l), len(chains), 'chains; volume sum', tot, 'target', target, 'degenerate', degenerate, 'OK' if tot == target and not degenerate else 'MISMATCH')
for k, l in [(2, 2), (2, 3), (3, 3), (3, 4)]: run(k, l)
