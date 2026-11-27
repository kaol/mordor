import sys; sys.path.insert(0, '.'); from world import *
from collections import Counter
ms = [(n, w) for n, w in dedup(load_all()) if w.w0flat()]
C = Counter()
for name, w in ms:
    le, F, h = w.le, w.F, w.h; Zs = set(w.Z); tag = ('W0' if w.w0() else 'flat') + ('-noexit' if w.noexit() else '-exit')
    Y = set(v for x in w.Z for v in w.desc(x)[:w.lidx(x)])
    Ymin = [y for y in Y if not any(z != y and le[z][y] for z in Y)]
    allin = all(w.b(y) in Zs for y in Ymin); somein = any(w.b(y) in Zs for y in Ymin)
    selfl = [y for y in Ymin if w.b(y) in Zs and y in w.desc(w.b(y))]
    C[(tag, 'all ymin: b(y) in Z', allin)] += 1; C[(tag, 'some ymin: b(y) in Z', somein)] += 1
    C[(tag, 'some ymin: y on desc(b(y)), b(y) in Z', bool(selfl))] += 1
    C[(tag, '#Ymin', len(Ymin))] += 1
    if tag == 'flat-noexit':
        W = w.witnesses()[0]
        C[(tag, 'witness = b(y) for every ymin', all(w.b(y) == W for y in Ymin))] += 1
for k in sorted(C, key=str): print(k, C[k])
