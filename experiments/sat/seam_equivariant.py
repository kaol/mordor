"""Round 23: seam search with translation-equivariance (columns i -> i+1) and locality (no jumps into the seam)."""
import sys, time
pass
from lat import *
def colinfo(kind, k):
    if kind == "D":
        L = D_cols(k); col = lambda i: [2+2*i, 3+2*i]
    else:
        L = E(k); col = lambda i: [2+3*i, 3+3*i, 4+3*i]
    sigma = {0: 0, 1: 1}
    for i in range(k-1):
        for p, q in zip(col(i), col(i+1)): sigma[p] = q
    return L, col, sigma
def equiv_search(kind, k, free_cols=1):
    # free_cols trailing columns form the seam
    L, col, sg = colinfo(kind, k); n = L.n
    last = set(e for i in range(k-free_cols, k) for e in col(i))
    inner = {0, 1} | set(e for i in range(k-1-free_cols) for e in col(i))   # sigma(inner) avoids the free columns' right end
    def extra(e):
        C, Dd = add_composites(e)
        for x in range(n):
            if x in last: continue
            for w in range(n): e.cl += [[-C[x][w], Dd[x][w]], [C[x][w], -Dd[x][w]]]
        for x in inner:
            for y in inner:
                if x in (0, 1) and y in (0, 1): continue
                for v in sg:   # F(x,y)=v (v shiftable) => F(sx,sy)=s(v)
                    e.cl.append([-e.F[x][y][v], e.F[sg[x]][sg[y]][sg[v]]])
            for y in inner:
                if x in (0, 1) and y in (0, 1): continue
                e.cl.append([e.F[x][y][v] for v in sg])          # locality: no jump into the seam
            if x not in (0, 1):
                e.cl.append([e.A[x][v] for v in sg]); e.cl.append([e.B[x][v] for v in sg])
                for v in sg:
                    e.cl.append([-e.A[x][v], e.A[sg[x]][sg[v]]]); e.cl.append([-e.B[x][v], e.B[sg[x]][sg[v]]])
    e = Enc(L, polar=True, commute=False, extra=extra); s = e.solver()
    if not s.solve(): return None
    F, a, b = e.decode(s.get_model())
    return L, F, a, b, [x for x in range(n) if a[b[x]] != b[a[x]]]
for kind, fc in (("D", 1), ("D", 2), ("E", 1), ("E", 2)):
    for k in range(3, 9):
        t = time.time(); r = equiv_search(kind, k, fc)
        print(f"{kind}_{k} seam={fc}: {'SAT, defects ' + str(r[4]) + ' a=' + str(r[2]) + ' b=' + str(r[3]) if r else 'UNSAT'}  ({time.time()-t:.1f}s)", flush=True)
