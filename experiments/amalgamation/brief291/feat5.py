import sys; sys.path.insert(0, '.'); from world import *
from collections import Counter
ms = [(n, w) for n, w in dedup(load_all()) if w.w0flat()]
def mu(w, x):
    p = w.lam(x); return p if w.F[w.bot][p] == w.bot else w.F[w.bot][p]
C = Counter()
for name, w in ms:
    le = w.le; Z = [x for x in w.Z if x != w.bot]
    low = [x for x in Z if le[mu(w, x)][x]]
    c = [x for x in Z if mu(w, x) == x][0]
    tag = 'W0' if w.w0() else 'flat'
    upcl = all(y in low for x in low for y in Z if le[x][y])
    mono = all(le[mu(w, x)][mu(w, y)] for x in Z for y in Z if le[x][y])
    lowup = set(low) == set(y for y in Z if le[c][y])
    cmin = all(le[c][x] for x in low)
    maxl = [x for x in Z if all(not (le[x][y] and x != y) for y in Z)]
    C[(tag, 'Low up-closed', upcl)] += 1; C[(tag, 'mu monotone on Z\\bot', mono)] += 1
    C[(tag, 'Low = up(c)', lowup)] += 1; C[(tag, 'c least in Low', cmin)] += 1
    C[(tag, 'some maximal of Z in Low', any(x in low for x in maxl))] += 1
    C[(tag, 'all maximal of Z in Low', all(x in low for x in maxl))] += 1
for k in sorted(C, key=str): print(k, C[k])
