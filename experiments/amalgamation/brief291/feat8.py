import sys, json; sys.path.insert(0, '.'); from world import *
from collections import Counter
ms = [(n, w) for n, w in dedup(load_all()) if w.w0flat() and w.nofix()]
print('stored W0flat & NoFix models (samples only):', len(ms))
C = Counter(); bad = []
def Ys(w):
    le = w.le; Y = set(v for x in w.Z for v in w.desc(x)[:w.lidx(x)])
    return Y, [y for y in Y if not any(z != y and le[z][y] for z in Y)]
for name, w in ms:
    Zs = set(w.Z); tag = 'noexit' if w.noexit() else 'exit'; Y, Ym = Ys(w)
    rx = set(w.last_hi(x) for x in w.Z)
    C[(tag, 'LfpMin: some ymin b(y) in Z', any(w.b(y) in Zs for y in Ym))] += 1
    C[(tag, 'LfpMinAll: every ymin b(y) in Z', all(w.b(y) in Zs for y in Ym))] += 1
    C[(tag, 'LfpLand: some ymin, b(y) in Z and y on desc(b(y))', any(w.b(y) in Zs and y in w.desc(w.b(y)) for y in Ym))] += 1
    C[(tag, 'LfpR: some r_x with b(r_x) in Z', any(w.b(y) in Zs for y in rx))] += 1
    C[(tag, 'LfpY: some y in Y with b(y) in Z', any(w.b(y) in Zs for y in Y))] += 1
    if not all(w.b(y) in Zs for y in Ym) or not any(w.b(y) in Zs and y in w.desc(w.b(y)) for y in Ym): bad.append(name)
for k in sorted(C, key=str): print(k, C[k])
print('models failing LfpMinAll or LfpLand:', bad)
