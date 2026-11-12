"""Candidate invariants of the singleton lower configuration (log §34.3z¹⁵⁶).

Random true orbits. Configuration at k ≥ 0: R_k has heights ≤ k, R_{k+1} has heights ≤ k + 1 with a unique element m
of height k + 1, m ∉ R_k, ⊤ ∉ R_{k+2}, and some m' ∈ R_k of height k has m' < m and F(m', m) ≤ m' (lower cell).
'lower-only' additionally: no m'' ∈ R_k of height k has m ≤ F(m'', m) (no upper feed).
Records, per configuration, a list of candidate predicates (counts True/False).  python3 single_lower_mine.py SEED SECONDS
"""
import sys, random, time, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ystar, gfp_ok, ic

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter()
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F); n = L.n; le = L.le; rk = L.rank; jn = L.join; mt = L.meet
        A = [a_of(L, F, x) for x in range(n)]; B = [b_of(L, F, y) for y in range(n)]
        inR = lambda z, j: st[z] is not None and st[z] <= j
        for k in range(0, st[L.top] - 2):
            Rk = [z for z in range(n) if inR(z, k)]; R1 = [z for z in range(n) if inR(z, k + 1)]
            if max(rk[z] for z in Rk) > k or max(rk[z] for z in R1) > k + 1: continue
            tops = [z for z in R1 if rk[z] == k + 1]
            if len(tops) != 1: continue
            m = tops[0]
            if inR(m, k): continue
            P = [p for p in Rk if rk[p] == k and le[p][m] and p != m]
            low = [p for p in P if le[F[p][m]][p]]; up = [p for p in P if le[m][F[p][m]]]
            if not low: continue
            T['configurations'] += 1; T[('k', min(k, 3))] += 1
            if up: T['with upper feed'] += 1; continue
            T['lower-only'] += 1
            y = ystar(L, F, m); w = F[m][y]; mp = low[0]; y1 = jn[m][F[m][L.top]]
            cell = lambda c: c != m and le[m][c] and (le[F[m][c]][m] or le[c][F[m][c]])
            for key, val in [
                ('IC(m)', ic(L, F, m)), ('GFP(m)', gfp_ok(L, F, m)), ('F(m,m) ≤ m', le[F[m][m]][m]),
                ('upper cell (m < a(m))', le[m][A[m]] and A[m] != m), ('lower cell at a cover', any(le[F[m][c]][m] for c in L.covers_up[m])),
                ('m ⊔ F(m,⊤) is a cell column', cell(y1)), ('y* is a cover of m', y in L.covers_up[m]),
                ('F(m,⊤) ≥ all lower feeders', all(le[p][F[m][L.top]] for p in low)),
                ('w ≥ all lower feeders', all(le[p][w] for p in low)), ('b(m) ∈ R_{k−1}', k >= 1 and inR(B[m], k - 1)),
                ('b(m) = a feeder', B[m] in low), ('b(m) = ⊥', B[m] == L.bot), ('|lower feeders|', min(len(low), 3)),
                ('a(feeder) ≤ m', all(le[A[p]][m] for p in low)), ('F(feeder,⊤) ≤ m', all(le[F[p][L.top]][m] for p in low)),
                ('b(⊤) ≤ m', le[B[L.top]][m]), ('a(m) ≤ m', le[A[m]][m]), ('a(m) ∈ R_{k+1}', inR(A[m], k + 1)),
                ('m = a(x) for some x ∈ R_k', any(A[x] == m for x in Rk))]:
                T[(key, val)] += 1
    for k, v in sorted(T.items(), key=str): print(k, v)
