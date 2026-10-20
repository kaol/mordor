"""Boundary Witness Conjecture on bounded posets (not only lattices), all posets with n elements."""
import sys, itertools, numpy as np
import locate as W

class Pos:
    def __init__(self, leq, name):
        self.leq = leq; self.n = leq.shape[0]; self.name = name
        self.bot = int(np.flatnonzero(leq.all(1))[0]); self.top = int(np.flatnonzero(leq.all(0))[0])
        lt = leq & ~np.eye(self.n, dtype=bool)
        self.covers = [(x, y) for x in range(self.n) for y in range(self.n) if lt[x, y] and not (lt[x] & lt[:, y]).any()]

def all_posets(n):
    k = n - 2; seen = set(); out = []
    pairs = [(i, j) for i in range(k) for j in range(k) if i != j]
    for mask in range(1 << len(pairs)):
        rel = np.eye(k, dtype=bool)
        for t, (i, j) in enumerate(pairs):
            if mask >> t & 1: rel[i, j] = True
        if (rel & rel.T & ~np.eye(k, dtype=bool)).any(): continue
        if ((rel.astype(int) @ rel.astype(int) > 0) & ~rel).any(): continue
        canon = min(tuple(rel[np.ix_(p, p)].ravel()) for p in itertools.permutations(range(k)))
        if canon in seen: continue
        seen.add(canon)
        leq = np.zeros((n, n), dtype=bool); leq[0, :] = True; leq[:, n - 1] = True; leq[1:n-1, 1:n-1] = rel
        out.append(Pos(leq, f"P{n}_{len(out)}"))
    return out

for n in map(int, sys.argv[1:]):
    tot = 0; fails = []; nlat = 0
    Ps = all_posets(n)
    for P in Ps:
        S = W.Solver(P)
        for D in W.downsets(P):
            tot += 1
            if S.no_witness_possible(D, W.cellsets(P, D)['maxD ∪ minU lines']): fails.append((P.name, sorted(D), P.leq.astype(int).tolist()))
    print(f"n={n}: {len(Ps)} bounded posets, {tot} down-sets, boundary-witness failures: {len(fails)}", flush=True)
    for f in fails[:3]: print("   ", f)
