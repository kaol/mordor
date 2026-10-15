"""Round 23: is the Cut Lemma contradiction one-dimensional (a single row x in D or column y in U infeasible)?"""
import sys, time
pass
from lat import *
from pysat.solvers import Cadical153
def line_feasible(L, D, x, row=True):
    """row: exists monotone r on U with r(y) not<= x and not>= y for all y in U.
       col (x plays y in U): exists monotone g on D with g(z) not<= z and not>= y."""
    n = L.n; U = [y for y in range(n) if y not in D]; dom = U if row else sorted(D)
    v = {z: [None]*n for z in dom}; nv = 0; cl = []
    for z in dom:
        for w in range(n):
            nv += 1; v[z][w] = nv
        cl.append([v[z][w] for w in range(n)])
        for w in range(n):
            for w2 in range(w+1, n): cl.append([-v[z][w], -v[z][w2]])
            bad = (L.leq[w][x] or L.leq[z][w]) if row else (L.leq[w][z] or L.leq[x][w])
            if bad: cl.append([-v[z][w]])
    for z in dom:
        for z2 in dom:
            if z != z2 and L.leq[z][z2]:
                for p in range(n):
                    for q in range(n):
                        if not L.leq[p][q]: cl.append([-v[z][p], -v[z2][q]])
    return Cadical153(bootstrap_with=cl).solve()
t = time.time(); tot = one_d = 0; bad = []
for L in list(moore_family(4)) + [E(3)]:
    if L.n < 2: continue
    for D in downsets(L):
        tot += 1; U = set(range(L.n)) - D
        if any(not line_feasible(L, D, x, True) for x in D) or any(not line_feasible(L, D, y, False) for y in U):
            one_d += 1
        elif len(bad) < 5: bad.append((L.name, sorted(D)))
print(f"instances {tot}; contradiction already in a single row or column: {one_d}; first exceptions: {bad}  {time.time()-t:.0f}s")
