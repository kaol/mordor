"""Stronger local forms of the Boundary Witness Conjecture (log §34.3m): for a boundary pair m ∈ max D, u ∈ min U,
is there always a witness in the cross  row m ∪ column u ?"""
import sys, locate as W, lattices as LT
from posets import all_posets
stats = {'forall pairs': [0, 0], 'forall comparable pairs': [0, 0], 'exists pair': [0, 0], 'exists comparable pair': [0, 0]}
ex = {}
def run(P):
    S = W.Solver(P); n, leq = P.n, P.leq
    for D in W.downsets(P):
        U = [y for y in range(n) if y not in D]
        maxD = [x for x in D if not any(leq[x, z] and z != x for z in D)]
        minU = [y for y in U if not any(leq[z, y] and z != y for z in U)]
        res = {}
        for m in maxD:
            for u in minU:
                C = [(m, y) for y in U] + [(x, u) for x in D]
                res[(m, u)] = not S.no_witness_possible(D, C)            # True: every F has a witness in the cross
        comp = {k: v for k, v in res.items() if leq[k[0], k[1]]}
        for name, ok in (('forall pairs', all(res.values())), ('forall comparable pairs', all(comp.values()) if comp else None),
                         ('exists pair', any(res.values())), ('exists comparable pair', any(comp.values()) if comp else None)):
            if ok is None: continue
            stats[name][0] += 1; stats[name][1] += (not ok)
            if not ok and name not in ex: ex[name] = (P.name, sorted(D))
for n in map(int, sys.argv[1:]):
    for P in all_posets(n): run(P)
    print(n, {k: f"{v[1]} fail / {v[0]}" for k, v in stats.items()}, flush=True)
print(ex)
