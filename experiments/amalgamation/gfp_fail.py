"""Anatomy of per-element GFP failures at tight stages (log §34.3z¹⁵⁴).

At random tight stages (k ≥ 1), for each top m ∈ T_k failing GFP (y* > m, w = F(m, y*) ∥ m), record where w, y*
and related terms sit relative to R_k, R_{k+1} and the other top elements.  python3 gfp_fail.py SEED SECONDS
"""
import sys, random, time, collections, json
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, a_of, b_of
from gfp_top import ystar, gfp_ok, ic

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter(); ex = []
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F); n = L.n; le = L.le
        A = [a_of(L, F, x) for x in range(n)]; B = [b_of(L, F, y) for y in range(n)]
        for k in range(1, st[L.top] - 1):
            R = [z for z in range(n) if st[z] <= k]
            if max(L.rank[z] for z in R) != k: continue
            Tk = [z for z in R if L.rank[z] == k]; inR = lambda z, j=k: st[z] <= j
            for m in Tk:
                if gfp_ok(L, F, m): continue
                y = ystar(L, F, m); w = F[m][y]; o = [t for t in Tk if t != m]
                T['GFP-failing tops'] += 1
                if not any(le[t][y] for t in o): ex.append(dict(sets=L.S, F=F, k=k, m=m))
                for key, val in [
                    ('IC(m)', ic(L, F, m)), ('|T_k|', len(Tk)), ('w ∈ R_k', inR(w)), ('w ∈ R_k+1', inR(w, k + 1)),
                    ('y* ∈ R_k+1', inR(y, k + 1)), ('some other top ≤ w', any(le[t][w] for t in o)),
                    ('some other top ≤ y*', any(le[t][y] for t in o)), ('F(m,m) ≤ m', le[F[m][m]][m]),
                    ('b(y*) ∈ R_k', inR(B[y])), ('b(y*) ≤ m', le[B[y]][m]), ('a(m) ≤ m ⊓ w', le[A[m]][L.meet[m][w]]),
                    ('m ⊓ w = b(m)?', L.meet[m][w] == B[m]), ('rank w vs k', (L.rank[w] > k) - (L.rank[w] < k)),
                    ('b(w) ∈ R_k', inR(B[w])), ('y* = m ⊔ some other top', any(L.join[m][t] == y for t in o)),
                    ('y* covers m', y in L.covers_up[m])]:
                    T[(key, val)] += 1
    for k, v in sorted(T.items(), key=str): print(k, v)
    if ex: json.dump(min(ex, key=lambda e: len(e['sets'])), open(f'gfp_fail_lonely_s{sys.argv[1]}.json', 'w')); print('lonely failures', len(ex), 'smallest |L|', min(len(e['sets']) for e in ex))
