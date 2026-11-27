import sys; sys.path.insert(0, '.'); from world import *
from collections import Counter
ms = [(n, w) for n, w in dedup(load_all()) if w.w0flat()]
C = Counter()
def ascent(w, y):
    v = w.bot; ch = [v]
    while w.F[v][y] != v: v = w.F[v][y]; ch.append(v)
    return ch
for name, w in ms:
    le, F, h = w.le, w.F, w.h; Zs = set(w.Z); tag = 'W0' if w.w0() else 'flat'
    Y = set(v for x in w.Z for v in w.desc(x)[:w.lidx(x)])            # high elements on descents of rows of Z
    Ymin = [y for y in Y if not any(z != y and le[z][y] for z in Y)]
    for y in Ymin:
        ch = ascent(w, y); inZ = [e for e in ch if e in Zs]; estar = inZ[-1] if len(inZ) < len(ch) else None
        if estar is None: C[(tag, 'min y: ascent stays in Z (b(y) in Z)')] += 1; continue
        C[(tag, 'min y: y on desc(e*)', y in w.desc(estar))] += 1
        C[(tag, 'min y: some ascent elt in Z has y on its desc', any(y in w.desc(e) for e in inZ))] += 1
    C[(tag, 'some min y with y on desc(e*)')] += any((lambda ch: (lambda inZ: len(inZ) < len(ch) and y in w.desc(inZ[-1]))([e for e in ch if e in Zs]))(ascent(w, y)) for y in Ymin)
    C[(tag, 'models')] += 1
for k in sorted(C, key=str): print(k, C[k])
