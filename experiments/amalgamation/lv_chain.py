"""Descent chains at level K − 1 under MinLevelW hypotheses (log §34.3z²⁴⁷); derived from lv_base.py.
Claim 'chain': some DescChain (p, c) at level K − 1 exists: p ∈ R_{K−1}, h(p) = K − 1, c ∈ R_K, h(c) = K, p ≤ c,
p ≤ F(p, c), c on the row-p descent from ⊤.  SAT = a model with no such chain.  Flags as in lv_base.py.

Hypotheses (MinLevelW at K ≥ 1): h(m) = K + 1, m ∈ R_{K+1} \\ R_K, R_K and R_{K+1} tight, w = F(m, y*) ∥ m
('full': also R_1, …, R_{K−1} tight).
'r1nt': R_1 non-tight is consistent with the hypotheses?
Claim 'base': some p ∈ R_{K−1} with h(p) = K − 1 has p ≤ a(p).  SAT = a model where every such p has p ≰ a(p).
  python3 lv_base.py K (sweep N MAX | closure K M SEED CNT) [full]
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from rstages import stages, a_of
K = int(sys.argv[1]); FULL = 'full' in sys.argv; R1NT = 'r1nt' in sys.argv; NOWPAR = 'nowpar' in sys.argv; NOMEM = 'nomem' in sys.argv; ONLYTK = 'onlyK' in sys.argv; GOOD = 'good' in sys.argv; NOAI = 'noai' in sys.argv; VAC = 'vac' in sys.argv   # vac: drop the claim (model count of the hypotheses)   # noai: also no A-interval base (every x ∈ R_{K−2} with h(x) ≤ K − 1 has h(a(x)) < K − 1)   # good: claim = some p ∈ R_{K−1} of height K − 1 whose row-p descent from ⊤ meets p or p ≤ a(p)   # nowpar: drop w ∥ m; nomem: drop m ∈ R_{K+1} \\ R_K; onlyK: tightness of R_K only (not R_{K+1})   # r1nt: instead of 'base', ask for R_1 non-tight
args = [a for a in sys.argv[2:] if a not in ('full', 'r1nt', 'nowpar', 'nomem', 'onlyK', 'good', 'noai', 'vac')]
C = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top; jn = L.join
    for m in range(n):
        if h[m] != K + 1 or L.height <= K + 1: continue
        E = Enc(L, K + 1); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
        A_ = lambda x, g: E.v('A', x, g)
        if not NOMEM: add([r(K + 1, m)]); add([-r(K, m)])
        for z in range(n):
            for j in range(1, K + 2):
                if h[z] > j and ((j == K) or (j == K + 1 and not ONLYTK) or FULL): add([-r(j, z)])
        U = lambda i, z: E.v('U', i, z); NO = L.height + 1
        for z in range(n): add([U(0, z)] if z == top else [-U(0, z)])
        for i in range(NO - 1):
            for z in range(n):
                lits = []
                for v in range(n):
                    for g in range(n):
                        if jn[m][g] == z: o = E.v('Ust', i, v, g); E.iff_and(o, [U(i, v), f(m, v, g)]); lits.append(o)
                E.iff_or(U(i + 1, z), lits)
        for z in range(n):
            for g in range(n):
                if (le[g][m] or le[m][g]) and not NOWPAR: add([-U(NO - 1, z), -f(m, z, g)])
        if R1NT: add([r(1, z) for z in range(n) if h[z] > 1])
        if NOAI and K >= 2:
            for x in range(n):
                if h[x] > K - 1: continue
                for g in range(n):
                    if h[g] >= K - 1 and le[x][g]: add([-r(K - 2, x), -A_(x, g)])
        for p in range(n):
            if h[p] != K - 1 or VAC: continue
            UP = lambda i, z: E.v('UP', p, i, z)
            for z in range(n): add([UP(0, z)] if z == top else [-UP(0, z)])
            for i in range(NO):
                for z in range(n):
                    lits = []
                    for v in range(n): o = E.v('UPs', p, i, v, z); E.iff_and(o, [UP(i, v), f(p, v, z)]); lits.append(o)
                    E.iff_or(UP(i + 1, z), lits)
            if GOOD:
                meet = E.v('meet', p); E.iff_or(meet, [UP(i, p) for i in range(NO + 1)])
                add([-r(K - 1, p), -meet])
                for g in range(n):
                    if le[p][g]: add([-r(K - 1, p), -A_(p, g)])
                continue
            for c in range(n):
                if h[c] != K or not le[p][c]: continue
                pge = E.v('pge', p, c); E.iff_or(pge, [f(p, c, v) for v in range(n) if le[p][v]])
                on = E.v('on', p, c); E.iff_or(on, [UP(i, c) for i in range(NO + 1)])
                add([-r(K - 1, p), -r(K, c), -pge, -on])
        if E.S.solve():
            F = E.decode(); st = stages(L, F)
            def desc(p):
                v = top; seen = []
                while v not in seen: seen.append(v); v = F[p][v]
                return seen
            inR = lambda x, j: st[x] is not None and st[x] <= j
            good = lambda p: p in desc(p) or le[p][a_of(L, F, p)]
            if VAC: ok = (not NOAI or not any(st[x] is not None and st[x] <= K - 2 and h[x] <= K - 1 and h[a_of(L, F, x)] >= K - 1 for x in range(n)))
            else: ok = (not NOAI or not any(st[x] is not None and st[x] <= K - 2 and h[x] <= K - 1 and h[a_of(L, F, x)] >= K - 1 for x in range(n))) and (not R1NT or any(h[z] > 1 and inR(z, 1) for z in range(n))) and (not any(h[p] == K - 1 and inR(p, K - 1) and good(p) for p in range(n)) if GOOD else not any(
                h[p] == K - 1 and inR(p, K - 1) and h[c] == K and inR(c, K) and le[p][c] and le[p][F[p][c]] and c in desc(p)
                for p in range(n) for c in range(n)))
            assert ok, 'SAT/Python mismatch'
            C['SAT'] += 1
            if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F, m=m))
        else: C['UNSAT'] += 1
        E.S.delete()
print('vac' if VAC else '', 'good' if GOOD else 'chain', 'noai' if NOAI else '', 'r1nt' if R1NT else '', 'nowpar' if NOWPAR else '', 'nomem' if NOMEM else '', 'onlyK' if ONLYTK else '', 'K =', K, 'full' if FULL else '', dict(C), 'smallest', best[0] if best else None)
if best and not VAC: json.dump(best[1], open(f'lv{"good" if GOOD else "chain"}{"_noai" if NOAI else ""}{"_r1nt" if R1NT else ""}{"_nowpar" if NOWPAR else ""}{"_nomem" if NOMEM else ""}{"_onlyK" if ONLYTK else ""}_K{K}{"_full" if FULL else ""}_min{best[0]}.json', 'w'))
