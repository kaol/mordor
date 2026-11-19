"""k = 1 anatomy of the MinUpCell configuration without uniqueness (log §34.3z²⁰⁴).

Models: SAT models of 'minhyp multi notop nofeeder' (R_1 tight kept) with rank(m) = 2.  For each: a(⊥), x0 = F(⊥, m),
w = F(m, y*) (y* = gfp of y ↦ m ⊔ F(m, y)), the atoms of R_1 below w (≤ m / ∥ m), which of them carry an interval
cell, and where the second tops come from.   python3 k1_probe.py (closure … | sweep …)
"""
import sys, collections, json
sys.argv += ['multi', 'notop', 'nofeeder']
sys.path.insert(0, '../separation')
from rstages import stages, b_of, a_of
from gfp_top import ystar
from tight_probe import lattices
import single_claims as sc
FLAGS = ('multi', 'notop', 'nofeeder')
C = collections.Counter(); best = {}
def keep(tag, n, d):
    if tag not in best or n < best[tag]:
        best[tag] = n; json.dump(d, open(f'k1_{tag}_min{n}.json', 'w'))
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS]):
    if L.height < 3: continue
    for m in range(L.n):
        if L.rank[m] != 2 or L.rank[m] >= L.height: continue
        F = sc.query(L, m, 'minhyp', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; st = stages(L, F); bot = min(range(n), key=lambda x: h[x])
        inR = lambda x, j: st[x] is not None and st[x] <= j
        cell = lambda x, z: le[x][z] and z != x and (le[F[x][z]][x] or le[z][F[x][z]])
        ic = lambda x: any(cell(x, z) for z in range(n))
        ys = ystar(L, F, m); w = F[m][ys]
        A1 = [x for x in range(n) if inR(x, 1) and h[x] == 1]
        tops = [z for z in range(n) if inR(z, 2) and h[z] == 2 and z != m]
        x0 = F[bot][m]
        below = [e for e in A1 if le[e][w]]
        par = [e for e in below if not le[e][m]]
        C['models'] += 1
        C[('a(⊥) = ⊥', a_of(L, F, bot) == bot)] += 1
        C[('x0 = F(⊥,m) ∈ R_1 atom, x0 ≤ m ⊓ w', x0 in A1 and le[x0][m] and le[x0][w])] += 1
        C[('#atoms of R_1 below w ∥ m', len(par))] += 1
        C[('some atom e ≤ w, e ∥ m has IC(e)', any(ic(e) for e in par))] += 1
        C[('some atom e ≤ w, e ∥ m has a cell at a top ≠ m', any(cell(e, z) and z in tops for e in par for z in range(n)))] += 1
        C[('some atom e ∥ m (anywhere) has a cell at a top', any(cell(e, z) and z in tops for e in A1 if not le[e][m] for z in range(n)))] += 1
        C[('some atom e ≤ m has a cell at a top', any(cell(e, z) and z in tops for e in A1 if le[e][m] for z in range(n)))] += 1
        if par and not any(ic(e) for e in par):
            C['cell-free pair (m, e): e ∈ R_1 ∩ ↓w, e ∥ m, ¬IC(e)'] += 1
            keep('cellfree_pair', n, dict(sets=L.S, F=F, m=m, e=par[0], w=w))
for k_, v in sorted(C.items(), key=str): print(k_, v)
for k_, v in sorted(best.items()): print('MIN', k_, v)
