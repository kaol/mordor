"""Round 23: abstract polar pairs with b.a <= a.b need not admit a principal cut (realizability is essential)."""
# Abstract polar monotone pairs (a,b) with b.a <= a.b: must a principal cut exist?
#  type D: d != top, a(d) <= d, and (y !<= d  =>  b(y) !<= d)
#  type U: u != bot, b(u) >= u, and (x !>= u  =>  a(x) !>= u)
import sys, time
pass
from lat import *
from pysat.solvers import Cadical153
def search(L, extra_props=()):
    n, le = L.n, L.leq; nv = [0]; cl = []
    def new(): nv[0] += 1; return nv[0]
    def onehot(): v = [new() for _ in range(n)]; cl.append(v); cl.extend([[-v[i], -v[j]] for i in range(n) for j in range(i+1, n)]); return v
    A = [onehot() for _ in range(n)]; B = [onehot() for _ in range(n)]
    for (x, x2) in L.covers:
        for p in range(n):
            for q in range(n):
                if not le[p][q]: cl += [[-A[x][p], -A[x2][q]], [-B[x][p], -B[x2][q]]]
    bt, tp = L.bot, L.top
    cl += [[A[bt][bt]], [A[tp][tp]], [B[bt][bt]], [B[tp][tp]]]
    C = [onehot() for _ in range(n)]; Dd = [onehot() for _ in range(n)]   # C = a.b, Dd = b.a
    for x in range(n):
        for u in range(n):
            for w in range(n): cl += [[-B[x][u], -A[u][w], C[x][w]], [-A[x][u], -B[u][w], Dd[x][w]]]
        for p in range(n):
            for q in range(n):
                if not le[q][p]: cl.append([-C[x][p], -Dd[x][q]])
    # forbid principal cuts
    for d in range(n):
        if d == tp: continue
        # NOT( a(d)<=d  and  forall y not<=d: b(y) not<=d )  ==  a(d) not<=d  OR  exists y not<=d with b(y)<=d
        lits = [A[d][v] for v in range(n) if not le[v][d]]
        lits += [B[y][v] for y in range(n) if not le[y][d] for v in range(n) if le[v][d]]
        # B[y][v] alone is a sufficient witness literal
        cl.append(lits)
    for u in range(n):
        if u == bt: continue
        lits = [B[u][v] for v in range(n) if not le[u][v]]
        lits += [A[x][v] for x in range(n) if not le[u][x] for v in range(n) if le[u][v]]
        cl.append(lits)
    for prop in extra_props: prop(L, A, B, cl, new)
    s = Cadical153(bootstrap_with=cl)
    if s.solve():
        m = set(l for l in s.get_model() if l > 0)
        return [next(v for v in range(n) if A[x][v] in m) for x in range(n)], [next(v for v in range(n) if B[x][v] in m) for x in range(n)]
    return None
def crossfix(L, A, B, cl, new):   # F4': a(x)=x => b(x)<=x ; F5: b(y)=y => y<=a(y)  (realizability-implied)
    n, le = L.n, L.leq
    for x in range(n):
        for v in range(n):
            if not le[v][x]: cl.append([-A[x][x], -B[x][v]])
            if not le[x][v]: cl.append([-B[x][x], -A[x][v]])
if __name__ == "__main__":
    for props, name in (((), "abstract"), ((crossfix,), "abstract + cross-fix")):
        t = time.time(); cnt = 0; ex = None
        for L in moore_family(4):
            if L.n < 3: continue
            r = search(L, props); cnt += 1
            if r and ex is None: ex = (L.name, r)
        print(f"{name}: {cnt} lattices; first pair with semi-commutation but no principal cut: {ex}  {time.time()-t:.0f}s", flush=True)
