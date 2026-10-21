"""Upper bounds for |L1| and |L2| in a witness-free (F, D) on M_ω² × C_n (sound: relaxations of the real constraints).

|L1|: atoms at cells over {⊥, ⊤}² × C_n, values drawn from a value-only pool (depth-0 constraints only).
|L2| given |L1| = k: the dc2_lazy master (level-0/1 constraints, no blocks); count used L2 atoms (prefix-symmetric)."""
import sys, itertools
from pysat.solvers import Cadical153
import dc2_lazy as d

def l1_bound(n):
    r = 0
    while l1_reach(n, r + 1): r += 1
    return r

def l1_reach(n, pool, thick=False, dpat=None):
    d.LAYERS = list(range(n))
    best = 0
    I = d.Inst(0, 0, n)
    S = Cadical153(); V = d.Vars()
    dm = lambda p: V('D', p)
    for p in I.P1:
        for q in I.covers(p, I.c1): S.add_clause([-dm(q), dm(p)])
    S.add_clause([dm((d.B, d.B, 0))]); S.add_clause([-dm((d.T, d.T, n - 1))])
    A = [('a', i) for i in range(pool)]
    dom = [d.B, d.T] + A
    pairs = [(x, y) for x in I.P1 for y in I.P1 if not I.ple(y, x)]
    ps = set(pairs)
    for x, y in pairs:
        d.pair_constraints(S, V, x, y, dom, dm(x), dm(y))
        for x2 in I.covers(x, I.c1):
            if (x2, y) in ps: d.mono(S, V, (x, y), (x2, y), dom, dom, [-dm(x2), dm(y)])
        for y2 in I.covers(y, I.c1):
            if (x, y2) in ps: d.mono(S, V, (x, y), (x, y2), dom, dom, [-dm(x), dm(y)])
    for a in A:
        u = V('used', a)
        for x, y in pairs:
            for i in range(2):
                # used only at genuine cells
                S.add_clause([u, -V('v', x, y, i, a), -dm(x), dm(y)])
        S.add_clause([-u] + [V('z', a, x, y, i) for x, y in pairs for i in range(2)])
        for x, y in pairs:
            for i in range(2):
                z = V('z', a, x, y, i)
                S.add_clause([-z, V('v', x, y, i, a)]); S.add_clause([-z, dm(x)]); S.add_clause([-z, -dm(y)])
    for j in range(pool - 1): S.add_clause([-V('used', A[j + 1]), V('used', A[j])])
    d.precedence(S, V, 'A', [(x, y, i) for x, y in pairs for i in range(2)], A)
    ass = [V('used', A[pool - 1])]
    if thick: ass += [V('D', (d.B, d.B, 1)), -V('D', (d.T, d.T, 0))]
    if dpat: ass += [V('D', p) if v else -V('D', p) for p, v in dpat.items()]
    return S.solve(assumptions=ass)

def l2_bound(k, n, cap=60):
    d.LAYERS = list(range(n))
    r = 0
    while r < cap:
        I = d.Inst(k, r + 1, n)
        S, V, pairs, dom = d.build_master(I)
        if not S.solve(assumptions=[V('used', I.L2[r])]): break
        r += 1
    return r

if __name__ == "__main__":
    n = int(sys.argv[1])
    K = l1_bound(n)
    print(f"n={n}: |L1| ≤ {K}", flush=True)
    for k in range(1, K + 1):
        print(f"n={n} k={k}: |L2| ≤ {l2_bound(k, n)}", flush=True)
