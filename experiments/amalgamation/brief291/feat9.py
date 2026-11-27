import sys, json; sys.path.insert(0, '.'); from world import *
from collections import Counter
ms = [(n, w) for n, w in dedup(load_all()) if w.w0flat()]
C = Counter(); ex = {}
def Ys(w):
    le = w.le; Y = set(v for x in w.Z for v in w.desc(x)[:w.lidx(x)])
    return Y, [y for y in Y if not any(z != y and le[z][y] for z in Y)]
def ascent(w, y):
    v = w.bot; ch = [v]
    while w.F[v][y] != v: v = w.F[v][y]; ch.append(v)
    return ch
for name, w in ms:
    Zs = set(w.Z); tag = ('W0' if w.w0() else 'flat') + ('-nofix' if w.nofix() else '-fix'); Y, Ym = Ys(w)
    for y in Ym:
        R = [x for x in w.Z if y in w.desc(x)]
        ch = ascent(w, y)
        # A1: phi(y) in R(y)
        a1 = w.F[w.bot][y] in R
        # A2: x in R(y), F(x,y) in Z  ==> F(x,y) in R(y)
        a2 = all(w.F[x][y] in R for x in R if w.F[x][y] in Zs)
        # A3: every ascent element in Z (k>=1) lies in R(y)
        a3 = all(e in R for e in ch[1:] if e in Zs)
        for k, v in dict(A1=a1, A2=a2, A3=a3).items():
            C[(tag, k, v)] += 1
            if not v: ex.setdefault((tag, k), name)
for k in sorted(C, key=str): print(k, C[k])
print(ex)
