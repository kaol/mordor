"""Near/far abstraction for S∞′ (log §34.3q). Result: SAT at every size tried, so no fixed finite region forces a witness.

S∞′: ⊥ < d, e < c; chains Z_i (length i) above d; w_i above c and top Z_i; ⊤. Near region: ⊥, d, e, c, ⊤ and the
first M chains with their w_i. A counterexample on the infinite lattice evaluates F on near × near at finitely many
values; far values lie in at most |near|² far chains, each of which order-embeds (with its cut point) into a long
model chain. So if "monotone on near cells, no witness on near D × U cells" is UNSAT in the model with K far chains of
length L, the Cut Lemma holds on S∞′ (for K ≥ number of near cells, L ≥ 2·(values per chain) + 1)."""
import itertools, sys
from pysat.solvers import Cadical153

def model(M, K, L):
    E = ['bot', 'd', 'e', 'c', 'top']
    chains = []
    for i in range(1, M + 1): chains.append(('n', i, i))
    for k in range(K): chains.append(('f', k, L))
    rel = [('bot', 'd'), ('bot', 'e'), ('d', 'c'), ('e', 'c')]
    near = ['bot', 'd', 'e', 'c', 'top']
    for kind, i, ln in chains:
        zs = [(kind, i, j) for j in range(1, ln + 1)]; w = (kind, i, 'w')
        E += zs + [w]
        rel += [('d', zs[0])] + list(zip(zs, zs[1:])) + [(zs[-1], w), ('c', w)]
        if kind == 'n': near += zs + [w]
    rel += [(x, 'top') for x in E if x != 'top']
    idx = {x: n for n, x in enumerate(E)}; n = len(E)
    le = [[a == b for b in range(n)] for a in range(n)]
    for a, b in rel: le[idx[a]][idx[b]] = True
    for k in range(n):
        for a in range(n):
            if le[a][k]:
                for b in range(n):
                    if le[k][b]: le[a][b] = True
    return E, [idx[x] for x in near], le

def solve(M, K, L):
    E, near, le = model(M, K, L); n = len(E)
    v = {}
    var = lambda k: v.setdefault(k, len(v) + 1)
    S = Cadical153()
    Dv = [var(('D', a)) for a in range(n)]
    S.add_clause([Dv[E.index('bot')]]); S.add_clause([-Dv[E.index('top')]])
    for a in range(n):
        for b in range(n):
            if le[a][b] and a != b: S.add_clause([-Dv[b], Dv[a]])
    cells = [(x, y) for x in near for y in near]
    for c in cells:
        S.add_clause([var(('F', c, z)) for z in range(n)])
        for z1, z2 in itertools.combinations(range(n), 2): S.add_clause([-var(('F', c, z1)), -var(('F', c, z2))])
    for c1 in cells:
        for c2 in cells:
            if c1 != c2 and le[c1[0]][c2[0]] and le[c1[1]][c2[1]]:
                for z1 in range(n):
                    for z2 in range(n):
                        if not le[z1][z2]: S.add_clause([-var(('F', c1, z1)), -var(('F', c2, z2))])
    for (x, y) in cells:
        for z in range(n):
            if le[z][x] or le[y][z]:      # witness if x ∈ D, y ∉ D
                S.add_clause([-Dv[x], Dv[y], -var(('F', (x, y), z))])
    r = S.solve()
    if r:
        m = set(l for l in S.get_model() if l > 0)
        D = [E[a] for a in range(n) if Dv[a] in m]
        Fv = {(E[x], E[y]): next(E[z] for z in range(n) if var(('F', (x, y), z)) in m) for (x, y) in cells
              if Dv[x] in m and Dv[y] not in m}
        return True, D, Fv
    return False, None, None

if __name__ == '__main__':
    for M, K, L in [(0, 4, 6), (0, 25, 12), (1, 36, 14)]:
        r, D, Fv = solve(M, K, L)
        print(f"M={M} K={K} L={L}: {'SAT (no witness among near cells)' if r else 'UNSAT'}", flush=True)
        if r:
            print('   D =', D[:20]); print('   F on near D×U:', dict(list(Fv.items())[:12]))
