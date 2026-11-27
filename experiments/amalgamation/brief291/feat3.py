import sys; sys.path.insert(0, '.'); from world import *
from collections import Counter
ms = dedup(load_all())
def mu(w, x):
    p = w.lam(x)
    if p is None: return None
    return p if w.F[w.bot][p] == w.bot else w.F[w.bot][p]
C = Counter()
for name, w in ms:
    if not (w.mono and w.a(w.bot) == w.bot and w.h[w.top] >= 3): C['not base-a'] += 1; continue
    zt = all(w.h[z] <= 2 for z in w.Z); n1 = bool(w.M2)
    ta = all(w.Ta(x) for x in w.Z)
    tb1 = all(w.Tb(x) for x in w.Z if w.h[x] == 1); tb2 = all(w.Tb(x) for x in w.M2)
    if not (zt and ta): C[('ZT', zt, 'Ta', ta)] += 1; continue
    k = sum(1 for x in w.Z if x != w.bot and mu(w, x) == x)
    C[('n1', n1, 'Tb1', tb1, 'Tb2', tb2, '#Fix(mu)\\bot', k)] += 1
for k in sorted(C, key=str): print(k, C[k])
