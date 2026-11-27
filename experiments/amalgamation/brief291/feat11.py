import sys; sys.path.insert(0, '.'); from world import *
from collections import Counter
ms = [(n, w) for n, w in dedup(load_all()) if w.w0flat() and w.nofix()]
C = Counter()
def ascent(w, y):
    v = w.bot; ch = [v]
    while w.F[v][y] != v: v = w.F[v][y]; ch.append(v)
    return ch
for name, w in ms:
    le = w.le; Zs = set(w.Z); tag = 'noexit' if w.noexit() else 'exit'
    Y = set(v for x in w.Z for v in w.desc(x)[:w.lidx(x)]); Ym = [y for y in Y if not any(z != y and le[z][y] for z in Y)]
    def AR(y):
        R = set(x for x in w.Z if y in w.desc(x)); ch = ascent(w, y)
        return w.b(y) in Zs and all(e in R for e in ch[1:])
    C[(tag, 'AscentRows some ymin', any(AR(y) for y in Ym))] += 1
    C[(tag, 'AscentRows some y in Y', any(AR(y) for y in Y))] += 1
    C[(tag, 'phi(y) in R(y) some ymin', any(w.F[w.bot][y] in [x for x in w.Z if y in w.desc(x)] for y in Ym))] += 1
print(dict(C))
