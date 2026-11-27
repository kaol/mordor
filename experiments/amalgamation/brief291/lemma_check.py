"""Free sanity check (no search) of the brief's paper lemmas on every distinct stored model in W0-flat
(W0 and the Tb-at-M2-dropped slice).  These lemmas have paper proofs; a failure here is a bug in a proof.
  Swap    : m in M2, y high, F(q,y) <= m for every atom q <= m  ==>  m <= F(m,y)
  Bcell   : m in M2, y high, F(m,y) <= m  ==>  F(m,y) = m ;  b(y) in Z ==> b(y) in M2 and F(b(y),y) = b(y)
  ConfLand: m in M2, z on row m's descent with m <= z and Conf_m(z)  ==>  lambda(m) = m
  MuLow   : (exists x in Z\\bot, mu(x) <= x)  <=>  (exists x in Z\\bot, mu(x) = x)  <=>  GoodTop-or-fixed-atom
  LowUp   : {x in Z\\bot : mu(x) <= x} = (up-set of Fix(mu)) & Z
  GTimpLfpCol: some m in M2 self-lands ==> b(r_m) = m  (so GoodTop ==> LfpCol)"""
import sys; sys.path.insert(0, '.'); from world import *
from collections import Counter
ms = [(n, w) for n, w in dedup(load_all()) if w.w0flat()]
print(__doc__); print('models (W0-flat, distinct, stored):', len(ms))
C = Counter()
def mu(w, x):
    p = w.lam(x); return p if w.F[w.bot][p] == w.bot else w.F[w.bot][p]
for name, w in ms:
    le, F, h = w.le, w.F, w.h; Zs = set(w.Z)
    conf = lambda m, y: all(le[F[q][y]][m] for q in w.atoms if le[q][m])
    ok = all(le[m][F[m][y]] for m in w.M2 for y in w.hi if conf(m, y)); C[('Swap', ok)] += 1
    ok = all(F[m][y] == m for m in w.M2 for y in w.hi if le[F[m][y]][m]) and \
         all(w.b(y) in w.M2 and F[w.b(y)][y] == w.b(y) for y in w.hi if w.b(y) in Zs); C[('Bcell', ok)] += 1
    ok = all(w.lam(m) == m for m in w.M2 for z in w.desc(m) if le[m][z] and z != m and conf(m, z)); C[('ConfLand', ok)] += 1
    Z1 = [x for x in w.Z if x != w.bot]
    low = set(x for x in Z1 if le[mu(w, x)][x]); fix = set(x for x in Z1 if mu(w, x) == x)
    C[('MuLow', bool(low) == bool(fix))] += 1
    C[('LowUp', low == set(x for x in Z1 if any(le[c][x] for c in fix)))] += 1
    C[('GTimpLfpCol', all(w.b(w.last_hi(m)) == m for m in w.M2 if w.lam(m) == m))] += 1
for k in sorted(C, key=str): print(k, C[k])
