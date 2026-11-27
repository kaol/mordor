import sys; sys.path.insert(0, '.'); from world import *
from collections import Counter
ms = [(n, w) for n, w in dedup(load_all()) if w.w0flat()]
def mu(w, x):
    p = w.lam(x); return p if w.F[w.bot][p] == w.bot else w.F[w.bot][p]
def gfpD(w):
    v = w.top
    while w.F[v][v] != v: v = w.F[v][v]
    return v
def lfpD(w):
    v = w.bot
    while w.F[v][v] != v: v = w.F[v][v]
    return v
C = Counter()
for name, w in ms:
    le = w.le; c = [x for x in w.Z if x != w.bot and mu(w, x) == x][0]
    kind = 'atom' if w.h[c] == 1 else 'M2'
    land = w.lam(c)                       # = c for M2 witness; = p (exit column) for fixed atom
    g = gfpD(w); l = lfpD(w); d, N = w.dN(); tb = w.tdesc()
    bs = {y: w.b(y) for y in w.hi}
    feats = {
      'c<=gfpD': le[c][g], 'land<=gfpD': le[land][g], 'gfpD in Z': g in w.Z, 'h(gfpD)': w.h[g],
      'c=b(y) some hi y': any(bs[y] == c for y in w.hi), 'land=b(y) some hi y': any(bs[y] == land for y in w.hi),
      'c <= d': le[c][d], 'c >= d': le[d][c], 'c maximal in Z': all(not (le[c][y] and y != c) for y in w.Z),
      'mu(d)=c': mu(w, d) == c, 'mu(mu(bot))=c': mu(w, mu(w, w.bot)) == c,
      'b(t_{N-1}) vs c': ('=' if bs.get(tb[N-1]) == c else ('<=' if le[bs[tb[N-1]]][c] else ('>=' if le[c][bs[tb[N-1]]] else '|'))) if N and tb[N-1] in bs else 'na',
      '#M2 lambda(m)<=... mu(m)<=m': sum(1 for m in w.M2 if le[mu(w, m)][m]),
    }
    for k, v in feats.items(): C[(kind, k, v)] += 1
for k in sorted(C, key=str): print(k, C[k])
