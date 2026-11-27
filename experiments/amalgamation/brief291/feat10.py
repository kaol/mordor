import sys; sys.path.insert(0, '.'); from world import *
from collections import Counter
ms = [(n, w) for n, w in dedup(load_all()) if w.w0flat() and w.nofix()]
C = Counter()
for name, w in ms:
    le = w.le; Zs = set(w.Z)
    Y = set(v for x in w.Z for v in w.desc(x)[:w.lidx(x)]); Ym = [y for y in Y if not any(z != y and le[z][y] for z in Y)]
    meet = lambda y: w.b(y) in Zs and any(le[w.b(y)][z] and le[z][y] for z in w.desc(w.b(y)))
    C[('MeetMin', any(meet(y) for y in Ym))] += 1
    C[('MeetY', any(meet(y) for y in Y))] += 1
    if not any(meet(y) for y in Ym): print('MeetMin fails on', name, 'Ymin', Ym, [(y, w.b(y)) for y in Ym], 'witness', w.witnesses(), 'r_w', [w.last_hi(m) for m in w.witnesses()])
print(dict(C))
