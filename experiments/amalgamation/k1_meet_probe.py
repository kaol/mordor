"""k = 1, d ≤ m branch (log §34.3z²⁰⁵): is the row c = m ⊓ w (an atom of R_1) the carrier of the cell?

Models as in k1_probe.py.  For each with c = m ⊓ w ∈ R_1 of height 1: does row c have a cell in (c, w] / (c, y*] /
anywhere off m; which atoms of R_1 carry UpCell; how the cell of c arises (upper = a(c), lower = b-preimage).
   python3 k1_meet_probe.py (closure … | sweep …)
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
        best[tag] = n; json.dump(d, open(f'k1m_{tag}_min{n}.json', 'w'))
for L in lattices([a for a in sys.argv[1:] if a not in FLAGS]):
    if L.height < 3: continue
    for m in range(L.n):
        if L.rank[m] != 2: continue
        F = sc.query(L, m, 'minhyp', False)
        if not F: continue
        n = L.n; le = L.le; h = L.rank; st = stages(L, F)
        inR = lambda x, j: st[x] is not None and st[x] <= j
        cell = lambda x, z: le[x][z] and z != x and (le[F[x][z]][x] or le[z][F[x][z]])
        ys = ystar(L, F, m); w = F[m][ys]
        c = L.S.index(L.S[m] & L.S[w])
        A1 = [x for x in range(n) if inR(x, 1) and h[x] == 1]
        if c not in A1: C['branch d ≤ m absent (m ⊓ w ∉ R_1 atoms)'] += 1; continue
        C['branch: c = m ⊓ w ∈ R_1'] += 1
        cw = [z for z in range(n) if cell(c, z) and le[z][w]]
        cy = [z for z in range(n) if cell(c, z) and le[z][ys] and not le[m][z]]
        coff = [z for z in range(n) if cell(c, z) and not le[m][z]]
        up = [x for x in A1 if any(cell(x, z) and not le[m][z] for z in range(n))]
        C[('row c has a cell in (c, w]', bool(cw))] += 1
        C[('row c has a cell in (c, y*] off m', bool(cy))] += 1
        C[('row c has a cell off m', bool(coff))] += 1
        C[('UpCell carriers', tuple(sorted('c' if x == c else ('≤m' if le[x][m] else '∥m') + ('≤w' if le[x][w] else '') for x in up)))] += 1
        if cw:
            ac = a_of(L, F, c)
            C[('cell of c in (c,w]: a(c) ∈ (c, w]', le[c][ac] and ac != c and le[ac][w], 'some lower cell in (c,w]', any(le[F[c][z]][c] for z in cw))] += 1
        if not cw: keep('nocw', n, dict(sets=L.S, F=F, m=m, c=c, w=w))
        if not coff: keep('nocoff', n, dict(sets=L.S, F=F, m=m, c=c, w=w))
for k_, v in sorted(C.items(), key=str): print(k_, v)
for k_, v in sorted(best.items()): print('MIN', k_, v)
