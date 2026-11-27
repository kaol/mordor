import sys; sys.path.insert(0, '.'); from world import *
from collections import Counter
ms = [(n, w) for n, w in dedup(load_all()) if w.w0flat()]
print('stored W0-flat models (samples only):', len(ms))
def mu(w, x):
    p = w.lam(x); return p if w.F[w.bot][p] == w.bot else w.F[w.bot][p]
C = Counter(); ex = []
for name, w in ms:
    fz = [x for x in w.Z if x != w.bot and mu(w, x) == x]
    nfa = sum(1 for x in fz if w.h[x] == 1); nfm = sum(1 for x in fz if w.h[x] == 2)
    low = [x for x in w.Z if x != w.bot and w.le[mu(w, x)][x]]
    C[('W0' if w.w0() else 'flat', 'fixed atoms', nfa, 'selfland', nfm)] += 1
    C[('W0' if w.w0() else 'flat', 'some mu(x)<=x', bool(low))] += 1
    if len(fz) != 1: ex.append((name, nfa, nfm))
for k in sorted(C, key=str): print(k, C[k])
print('models with |Fix(mu)\\bot| != 1:', ex[:10])
