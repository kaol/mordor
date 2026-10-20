"""Can the witnesses of S∞′_N all be pushed into its last chain? (log §34.3q)

Order encoding: g[c][z] ⟺ F(c) ≤ z. A witness is allowed only at cells (x, y) where x or y lies in the last chain
Z_N or is w_N. SAT for every N would mean the obstruction can always be deferred to the newest chain (the escape
mechanism); UNSAT means some witness is forced among the earlier chains."""
import itertools, sys
from pysat.solvers import Cadical153
sys.path.insert(0, __file__.rsplit('/', 1)[0])

def sinfp(N):
    E = ['bot', 'd', 'e', 'c', 'top']; rel = [('bot', 'd'), ('bot', 'e'), ('d', 'c'), ('e', 'c')]
    last = set()
    for i in range(1, N + 1):
        zs = [('z', i, j) for j in range(1, i + 1)]; w = ('w', i); E += zs + [w]
        rel += [('d', zs[0])] + list(zip(zs, zs[1:])) + [(zs[-1], w), ('c', w)]
        if i == N: last |= set(zs) | {w}
    rel += [(x, 'top') for x in E if x != 'top']
    idx = {x: k for k, x in enumerate(E)}; n = len(E)
    le = [[a == b for b in range(n)] for a in range(n)]
    for a, b in rel: le[idx[a]][idx[b]] = True
    for k in range(n):
        for a in range(n):
            if le[a][k]:
                for b in range(n):
                    if le[k][b]: le[a][b] = True
    return E, le, {idx[x] for x in last}

def covers(le, n):
    return [(a, b) for a in range(n) for b in range(n) if a != b and le[a][b]
            and not any(c not in (a, b) and le[a][c] and le[c][b] for c in range(n))]

def solve(N, protect_last=True, extra=None):
    E, le, last = sinfp(N); n = len(E); cov = covers(le, n)
    v = {}; var = lambda k: v.setdefault(k, len(v) + 1)
    S = Cadical153()
    Dv = [var(('D', a)) for a in range(n)]
    S.add_clause([Dv[E.index('bot')]]); S.add_clause([-Dv[E.index('top')]])
    for a, b in cov: S.add_clause([-Dv[b], Dv[a]])
    for x in range(n):
        for y in range(n):
            f = [var(('f', x, y, z)) for z in range(n)]
            S.add_clause(f)
            for z1, z2 in itertools.combinations(range(n), 2): S.add_clause([-f[z1], -f[z2]])
            for z in range(n):
                g = var(('g', x, y, z))
                for vv in range(n):
                    S.add_clause([-f[vv], g] if le[vv][z] else [-f[vv], -g])
            if protect_last and (x in last or y in last): continue
            for z in range(n):
                if le[z][x] or le[y][z]: S.add_clause([-Dv[x], Dv[y], -f[z]])
    for a, b in cov:            # monotone in each argument along covers
        for o in range(n):
            for z in range(n):
                S.add_clause([-var(('g', b, o, z)), var(('g', a, o, z))])
                S.add_clause([-var(('g', o, b, z)), var(('g', o, a, z))])
    r = S.solve()
    if not r: return False, None
    m = set(l for l in S.get_model() if l > 0)
    D = {E[a] for a in range(n) if Dv[a] in m}
    F = {(E[x], E[y]): next(E[z] for z in range(n) if var(('f', x, y, z)) in m) for x in range(n) for y in range(n)}
    return True, (D, F)

if __name__ == '__main__':
    for N in range(2, 8):
        r, sol = solve(N)
        print(f"N={N}: witnesses pushable into the last chain: {'yes (SAT)' if r else 'no (UNSAT)'}", flush=True)
        if r:
            D, F = sol
            print('   D∖{bot,d,e} chain cut:', sorted(x for x in D if isinstance(x, tuple)))
            print('   F(bot,top) =', F[('bot', 'top')], ' F(d,top) =', F[('d', 'top')], ' F(e,top) =', F[('e', 'top')],
                  ' c in D:', 'c' in D, ' e in D:', 'e' in D)
