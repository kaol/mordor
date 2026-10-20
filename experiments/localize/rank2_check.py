"""Rank-2 test family for the box criterion with resets (log §34.3t).

R2 = S∞′ with one more layer of hubs: ⊥ < d, e < c; hubs d < h_i (i ∈ ℕ), each carrying chains Z_{i,n} of every length
n above it; v_i = h_i ∨ c and w_{i,n} = v_i ∨ top Z_{i,n}. Infinitely many hubs (h_i, v_i) occur in the corner
neighbourhoods of d and c, so neither §34.3s theorem applies at those corners. On truncations R2_N (i, n ≤ N) we test
the D-free criterion of `IdealFinite.cut_of_box_hub_criterion` (its reset alternatives) for every box [s, t] and
interior corner c whose labels use indices ≤ K, reading "finite" as "does not grow from N₁ to N₂" (the family is
uniform in i and n).

Result: 5 of 179 classes fail, among them [⊥, ⊤] with corner c, where both sides fail. So box localization plus
neighbourhood resets does not reach R2. R2 has finite proper principal ideals and is chain-finite, so
`IdealFinite.cut_of_ideal_finite` settles it.
"""
import sys
from boxes import Lat

def r2(N):
    E = ['bot', 'top', 'd', 'e', 'c'] + [('h', i) for i in range(1, N + 1)] + [('v', i) for i in range(1, N + 1)]
    E += [('z', i, n, j) for i in range(1, N + 1) for n in range(1, N + 1) for j in range(1, n + 1)]
    E += [('w', i, n) for i in range(1, N + 1) for n in range(1, N + 1)]
    R = [('bot', x) for x in E if x != 'bot'] + [(x, 'top') for x in E if x != 'top'] + [('d', 'c'), ('e', 'c')]
    for i in range(1, N + 1):
        R += [('d', ('h', i)), (('h', i), ('v', i)), ('c', ('v', i))]
        for n in range(1, N + 1):
            R += [(('h', i), ('z', i, n, 1))] + [(('z', i, n, j), ('z', i, n, j + 1)) for j in range(1, n)]
            R += [(('z', i, n, n), ('w', i, n)), (('v', i), ('w', i, n))]
    return Lat(E, R)

def idx(x):
    return [k for k in (x[1:] if isinstance(x, tuple) else []) if isinstance(k, int)]

def data(L, K):
    le, n, E = L.le, L.n, L.E
    out = {}
    for s in range(n):
        for t in range(n):
            if s == t or not le[s][t]: continue
            if max(idx(E[s]) + idx(E[t]) + [0]) > K: continue
            box = [z for z in range(n) if le[s][z] and le[z][t]]
            spine = any(p not in (s, t) and all(le[z][p] or le[p][z] for z in box) for p in box)
            for c in box:
                if c in (s, t) or max(idx(E[c]) + [0]) > K: continue
                W = [z for z in box if L.meet[z][c] != s and L.join[z][c] != t]
                Ws = set(W)
                down = {E[g]: sum(1 for z in W if le[z][g]) for g in W}
                up = {E[g]: sum(1 for z in W if le[g][z]) for g in W}
                notle = {E[g] for g in W if not le[g][c]}
                notge = {E[g] for g in W if not le[c][g]}
                out[(E[s], E[t], E[c])] = dict(spine=spine, lo=L.inf(W, t) != s, hi=L.sup(W, s) != t,
                                               down=down, up=up, notle=notle, notge=notge, size=len(W))
    return out

def verdict(a, b):
    """a at N1, b at N2 > N1 for the same (s, t, c). "Infinite" = grows from N1 to N2. A set of such elements is
    read as finite when all its members carry indices ≤ 2 (the family is uniform in its indices)."""
    if b['spine']: return 'spine'
    grow_dn = {g for g in b['down'] if g in a['down'] and b['down'][g] > a['down'][g]}
    grow_up = {g for g in b['up'] if g in a['up'] and b['up'][g] > a['up'][g]}
    small = lambda G: all(max(idx(g) + [0]) <= 2 for g in G)
    lo_reset = not grow_up and small({g for g in grow_dn if g in b['notle']})   # c ∈ D: dual reset in W
    hi_reset = not grow_dn and small({g for g in grow_up if g in b['notge']})   # c ∉ D: reset in W
    lo, hi = b['lo'] or lo_reset, b['hi'] or hi_reset
    if lo and hi:
        return 'ok:' + ('⋀' if b['lo'] else 'R') + ('⋁' if b['hi'] else 'R')
    return 'FAIL lo=%s hi=%s' % (lo, hi)

if __name__ == '__main__':
    K = 2
    A, B = data(r2(4), K), data(r2(5), K)
    from collections import Counter
    cnt, fails = Counter(), []
    for key in B:
        if key not in A: continue
        v = verdict(A[key], B[key]); cnt[v.split()[0] if v.startswith('FAIL') else v] += 1
        if v.startswith('FAIL'): fails.append((key, v, B[key]['size'] - A[key]['size']))
    print('pairs:', sum(cnt.values()), dict(cnt))
    for f in fails[:40]: print(f)
