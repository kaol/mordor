"""Shape of the last SAT model of the ground search: distinct elements, rank/side profile, depth histogram.
  python3 model_shape.py H maxterms [fit|front]"""
import sys, numpy as np, cut_ground as c, collections, functools
H = int(sys.argv[1]); cap = int(sys.argv[2])
ok, G = c.run(H, cap, per_round=1, wlog=True, room=(sys.argv[3] if len(sys.argv) > 3 else 'fit'), forget=10**6)
L = G._lastL; model = G._lastmodel; n = L.shape[0]
M = set(model[model > 0].tolist())
inD = [G.d_[i] in M for i in range(n)]
# quotient by equivalence
eq = L & L.T
rep = [min(np.flatnonzero(eq[i])) for i in range(n)]
cls = sorted(set(rep))
print(f"{n} terms, {len(cls)} distinct elements")
@functools.lru_cache(None)
def up(i): return 1 + max([up(j) for j in cls if j != i and L[i, j] and not L[j, i]], default=0)
@functools.lru_cache(None)
def dn(i): return 1 + max([dn(j) for j in cls if j != i and L[j, i] and not L[i, j]], default=0)
sys.setrecursionlimit(10000)
tab = collections.Counter((dn(i) - 1, 'D' if inD[i] else 'C') for i in cls)
print("elements per (rank from bottom, side):")
for r in range(H + 2):
    print(f"  rank {r}: D {tab[(r,'D')]:4d}   C {tab[(r,'C')]:4d}")
# width of each rank level: pairwise incomparable?
for side in 'DC':
    S = [i for i in cls if (inD[i] == (side == 'D'))]
    maxl = [i for i in S if not any(L[i, j] and not L[j, i] for j in S if j != i)] if side == 'D' else \
           [i for i in S if not any(L[j, i] and not L[i, j] for j in S if j != i)]
    print(f"  {'maximal D' if side=='D' else 'minimal C'}: {len(maxl)}")
dep = collections.Counter(G.depth[i] for i in cls); print("depth histogram:", dict(sorted(dep.items())))
