"""Product families against the full box criterion of `IdealFinite.cut_of_box_hub_criterion` (log §34.3t).

Every box [s, t] and interior c of a truncation L_N is classified as one of:
* spine;
* ideal-finite box (all |[s, g]|, g < t, stable in N);
* filter-finite box (all |[g, t]|, g > s, stable in N);
* shrink / reset on both sides, as in rank2_check.py;
* FAIL.

Truncations: Ω_N (chains of length 1..N side by side). The reset alternatives of the box criterion are not modelled
here. Instead, `nbhd_verdict` tests the neighbourhood hub condition of `Hubs.cut_of_nbhd_hubs` corner by corner.

Result:
* Ω × C₂ fails the box criterion at [⊥, ⊤], but every corner neighbourhood satisfies the hub condition on one side
  (0 of 14 corners fail), so `cut_of_nbhd_hubs` covers it.
* In Ω × Ω every corner fails on both sides, e.g. c = (⊤, ⊥). So Ω × Ω, a chain-finite product of two end-finite
  lattices with infinite principal ideals and filters, is outside every theorem of §34.3p–t.
"""
import itertools, sys
from boxes import Lat, omega, sinf

def product(L1, L2):
    E = [(a, b) for a in L1.E for b in L2.E]
    R = []
    for (a, b) in E:
        for (c, d) in E:
            if L1.le[L1.idx[a]][L1.idx[c]] and L2.le[L2.idx[b]][L2.idx[d]]: R.append(((a, b), (c, d)))
    return Lat(E, R)

def chain(k):
    E = list(range(k)); return Lat(E, [(i, i + 1) for i in range(k - 1)])

def dual(L):
    return Lat(L.E, [(L.E[j], L.E[i]) for i in range(L.n) for j in range(L.n) if L.le[i][j]])

def bot_top(L):
    b = [i for i in range(L.n) if all(L.le[i][j] for j in range(L.n))][0]
    t = [i for i in range(L.n) if all(L.le[j][i] for j in range(L.n))][0]
    return b, t

def classify(L, keys=None):
    le, n, E = L.le, L.n, L.E
    out = {}
    for s in range(n):
        for t in range(n):
            if s == t or not le[s][t]: continue
            if keys is not None and (E[s], E[t]) not in keys: continue
            box = [z for z in range(n) if le[s][z] and le[z][t]]
            spine = any(p not in (s, t) and all(le[z][p] or le[p][z] for z in box) for p in box)
            lowI = {E[g]: sum(1 for z in box if le[z][g]) for g in box if g != t}
            upI = {E[g]: sum(1 for z in box if le[g][z]) for g in box if g != s}
            for c in box:
                if c in (s, t): continue
                W = [z for z in box if L.meet[z][c] != s and L.join[z][c] != t]
                out[(E[s], E[t], E[c])] = dict(spine=spine, lowI=lowI, upI=upI, lo=L.inf(W, t) != s,
                                               hi=L.sup(W, s) != t, size=len(W))
    return out

def verdict(a, b):
    if b['spine']: return 'spine'
    if all(b['lowI'][g] == a['lowI'].get(g, -1) for g in a['lowI']) and len(b['lowI']) == len(a['lowI']):
        return 'ideal-finite box'
    if all(b['upI'][g] == a['upI'].get(g, -1) for g in a['upI']) and len(b['upI']) == len(a['upI']):
        return 'filter-finite box'
    if b['lo'] and b['hi']: return 'shrink'
    return 'FAIL'

def run(name, mk, N1, N2):
    A, B = classify(mk(N1)), classify(mk(N2))
    from collections import Counter
    cnt = Counter(); fails = []
    for k in A:
        if k not in B: continue
        v = verdict(A[k], B[k]); cnt[v] += 1
        if v == 'FAIL': fails.append(k)
    print(name, dict(cnt)); print('   e.g.', fails[:4])

def nbhd_sides(L):
    """per corner c: (side1, side2) data of N(c) = {z : z ⊓ c ≠ ⊥, z ⊔ c ≠ ⊤}"""
    b, t = bot_top(L); le, n, E = L.le, L.n, L.E
    out = {}
    for c in range(n):
        if c in (b, t): continue
        Nc = [z for z in range(n) if L.meet[z][c] != b and L.join[z][c] != t]
        out[E[c]] = ({E[g]: sum(1 for z in Nc if le[z][g]) for g in Nc},
                     {E[g]: sum(1 for z in Nc if le[g][z]) for g in Nc})
    return out

def nbhd_verdict(mk, Ns):
    """side 1: no ideal grows and the set of elements with growing filter is the same over both steps; dually."""
    D = [nbhd_sides(mk(N)) for N in Ns]
    res = {}
    for c in D[0]:
        def grow(k, i):  # k: 0 ideals / 1 filters; step i -> i+1
            a, b = D[i][c][k], D[i + 1][c][k]
            return {g for g in a if b[g] > a[g]}, {g for g in b if g not in a and b[g] > 1}
        side = []
        for k in (0, 1):
            g0, new0 = grow(k, 0); g1, new1 = grow(k, 1)
            other0, _ = grow(1 - k, 0); other1, _ = grow(1 - k, 1)
            # side k+1: the k-direction never grows; the (1-k)-growing set does not gain members
            side.append(not g0 and not g1 and len(other1) == len(other0))
        res[c] = tuple(side)
    bad = [c for c in res if not any(res[c])]
    return len(res), bad

if __name__ == '__main__':
    run('Omega x C2', lambda N: product(omega(N), chain(2)), 3, 4)
    run('Omega x Omega', lambda N: product(omega(N), omega(N)), 2, 3)
    for name, mk, Ns in [('Omega x C2', lambda N: product(omega(N), chain(2)), (3, 4, 5)),
                         ('Omega x Omega', lambda N: product(omega(N), omega(N)), (2, 3, 4))]:
        tot, bad = nbhd_verdict(mk, Ns)
        print(name, 'corners', tot, 'failing the hub condition on both sides:', len(bad), bad[:6])
