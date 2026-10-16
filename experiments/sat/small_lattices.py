"""Round 23: all lattices with <= 8 elements (bounded posets filtered to lattices), Cut Lemma on every down-set."""
import sys, time, itertools
pass
from lat import *
from cutlemma import cut_counterexample_exists
def lattices_upto(N):
    seen = set(); out = []
    for k in range(0, N - 1):           # k inner elements, n = k + 2
        pairs = [(i, j) for i in range(k) for j in range(i+1, k)]
        for mask in range(1 << len(pairs)):
            rel = [[i == j for j in range(k)] for i in range(k)]
            for t, (i, j) in enumerate(pairs):
                if mask >> t & 1: rel[i][j] = True
            if any(rel[i][j] and rel[j][l] and not rel[i][l] for i in range(k) for j in range(k) for l in range(k)): continue
            n = k + 2; leq = [[False]*n for _ in range(n)]
            for i in range(n): leq[0][i] = leq[i][n-1] = True
            for i in range(k):
                for j in range(k): leq[i+1][j+1] = rel[i][j]
            # lattice test
            ok = True
            for x in range(n):
                for y in range(n):
                    ub = [z for z in range(n) if leq[x][z] and leq[y][z]]
                    if sum(all(leq[z][w] for w in ub) for z in ub) != 1: ok = False; break
                if not ok: break
            if not ok: continue
            canon = min(tuple(tuple(rel[p[i]][p[j]] for j in range(k)) for i in range(k)) for p in itertools.permutations(range(k)))
            if (k, canon) in seen: continue
            seen.add((k, canon)); out.append(Lattice(n, leq, f"L{n}#{len(out)}"))
    return out
t = time.time(); Ls = lattices_upto(8)
from collections import Counter
print("lattices by size:", dict(sorted(Counter(L.n for L in Ls).items())), f"({time.time()-t:.0f}s)", flush=True)
inst = 0
for L in Ls:
    if L.n < 2: continue
    for D in downsets(L):
        inst += 1
        if cut_counterexample_exists(L, D): print("COUNTEREXAMPLE", L.name, L.covers, sorted(D), flush=True)
print(f"all lattices with <= 8 elements: {len(Ls)} lattices, {inst} (lattice, down-set) instances checked  {time.time()-t:.0f}s")
