"""Base of the descent tower at level K − 1 (log §34.3z²⁴⁶).

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
K = int(sys.argv[1]); FULL = 'full' in sys.argv; R1NT = 'r1nt' in sys.argv   # r1nt: instead of 'base', ask for R_1 non-tight
args = [a for a in sys.argv[2:] if a not in ('full', 'r1nt')]
C = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top; jn = L.join
    for m in range(n):
        if h[m] != K + 1 or L.height <= K + 1: continue
        E = Enc(L, K + 1); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
        A_ = lambda x, g: E.v('A', x, g)
        add([r(K + 1, m)]); add([-r(K, m)])
        for z in range(n):
            for j in range(1, K + 2):
                if h[z] > j and (j >= K or FULL): add([-r(j, z)])
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
                if le[g][m] or le[m][g]: add([-U(NO - 1, z), -f(m, z, g)])
        if R1NT: add([r(1, z) for z in range(n) if h[z] > 1])
        else:
            for p in range(n):
                if h[p] != K - 1: continue
                for g in range(n):
                    if le[p][g]: add([-r(K - 1, p), -A_(p, g)])
        if E.S.solve():
            F = E.decode(); st = stages(L, F)
            ok = any(h[z] > 1 and st[z] is not None and st[z] <= 1 for z in range(n)) if R1NT else not any(h[p] == K - 1 and st[p] is not None and st[p] <= K - 1 and le[p][a_of(L, F, p)] for p in range(n))
            assert ok, 'SAT/Python mismatch'
            C['SAT'] += 1
            if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F, m=m))
        else: C['UNSAT'] += 1
        E.S.delete()
print('r1nt' if R1NT else 'base', 'K =', K, 'full' if FULL else '', dict(C), 'smallest', best[0] if best else None)
if best: json.dump(best[1], open(f'lv{"r1nt" if R1NT else "base"}_K{K}{"_full" if FULL else ""}_min{best[0]}.json', 'w'))
