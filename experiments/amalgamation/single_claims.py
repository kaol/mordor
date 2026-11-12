"""Exact tests of intermediate lemmas for the singleton cases (log §34.3z¹⁵⁶).

True orbit (amalg_sat.Enc), m of rank K ≥ 1 the unique rank-K element of R_K, m ∉ R_{K−1}, R_K ranks ≤ K,
R_{K−1} ranks ≤ K − 1, ⊤ ∉ R_{K+1}.  (Lean indexing: k = K − 1.)
Programme A configuration ('A'): a lower feeder m' ∈ R_{K−1}, rank K − 1, m' < m, F(m', m) ≤ m'.
Programme B configuration ('B'): an a-entry m = a(x), x ∈ R_{K−1}, x ≰ m, and m non-diagonal (m ≰ F(m, m)).
Each claim is tested by asking for a configuration violating it (SAT = counterexample, re-checked in Python).
  A claims: bm_eq_feeder  b(m) = m' for every lower feeder m'
            w_ge_bm       F(m, y*) ≥ b(m)        (y* = gfp of y ↦ m ⊔ F(m, y))
            top_ge_bm     F(m, ⊤) ≥ b(m)
            a_feeder_le   a(m') ≤ m for every lower feeder
            fmm_le        F(m, m) ≤ m
            gfp           y* = m or F(m, y*) = y*   (the comparability lemma, w ≤ m ∨ m ≤ w)
  C claims (multi-top transfer, Programme C: uniqueness of m dropped, m any target of rank K in R_K, not in R_{K−1}):
            C_bm_eq_feeder  b(m) = m' for every lower feeder m' of the target m
            C_a_feeder_le   a(m') ≤ m for every lower feeder
  B claims: bentry        b(m) ∈ R_{K−1}  (Programme B's conjecture; = BEntry by the height bound)
            bm_le_x       b(m) ≤ x
            bm_le_meet    b(m) ≤ x ⊓ m
            meet_pre      F(x ⊓ m, m) ≤ x ⊓ m
            fmm_le_B      F(m, m) ≤ m
            fmm_in        F(m, m) ∈ R_{K−1}
  'ahead': index-sensitivity test, m placed at stage J = K − 1 (one ahead): R_J ranks ≤ K with unique rank-K
           element m ∉ R_{J−1}, R_{J−1} ranks ≤ K − 1, ⊤ ∉ R_{J+1}, feeders/entries from R_{J−1}.
  python3 single_claims.py CLAIM [ahead] (sweep P NMAX | closure K M SEED COUNT)
"""
import sys, collections, itertools
sys.path.insert(0, '../separation')
import separator_stages as ss
from amalg_sat import Enc
from rstages import stages, a_of, b_of
from tight_probe import helpers, lattices
from gfp_top import ystar, gfp_ok

A_CLAIMS = ('C_bm_eq_feeder', 'C_a_feeder_le', 'bm_eq_feeder', 'w_ge_bm', 'top_ge_bm', 'a_feeder_le', 'fmm_le', 'gfp')
B_CLAIMS = ('bentry', 'bm_le_x', 'bm_le_meet', 'meet_pre', 'fmm_le_B', 'fmm_in')

def query(L, m, claim, ahead=False):
    n = L.n; le = L.le; rk = L.rank; K = rk[m]; jn = L.join; mt = L.meet; s = 1 if ahead else 0
    if K - s < 1: return None
    E = Enc(L, K + 1 - s); fle, yle, ic = helpers(E, L); r = lambda j, z: E.v('r', j - s, z)
    E.S.add_clause([-r(K + 1, L.top)]); E.S.add_clause([r(K, m)]); E.S.add_clause([-r(K - 1, m)])
    for z in range(n):
        if rk[z] > K or (rk[z] == K and z != m and not claim.startswith('C_')): E.S.add_clause([-r(K, z)])
        if rk[z] > K - 1: E.S.add_clause([-r(K - 1, z)])
    B = lambda y, g: E.v('B', y, g); A = lambda x, g: E.v('A', x, g); f = lambda x, y, v: E.v('f', x, y, v)
    bad = []                                            # witnesses of ¬claim
    if claim in A_CLAIMS:
        feeders = [p for p in L.covers_dn[m] if rk[p] == K - 1]
        if not feeders: E.S.delete(); return None
        low = {}
        for p in feeders:
            o = E.v('low', p); E.iff_and(o, [r(K - 1, p), fle(p, m, p)]); low[p] = o
        E.S.add_clause(list(low.values()))
        if claim in ('bm_eq_feeder', 'C_bm_eq_feeder'):
            for p in feeders: o = E.v('bad', p); E.iff_and(o, [low[p], -B(m, p)]); bad.append(o)
        elif claim in ('a_feeder_le', 'C_a_feeder_le'):
            for p in feeders:
                for g in range(n):
                    if not le[g][m]: o = E.v('bad', p, g); E.iff_and(o, [low[p], A(p, g)]); bad.append(o)
        elif claim == 'fmm_le':
            bad.append(-fle(m, m, m))
        elif claim == 'top_ge_bm':
            for g in range(n):
                for w in range(n):
                    if not le[g][w]: o = E.v('bad', g, w); E.iff_and(o, [B(m, g), f(m, L.top, w)]); bad.append(o)
        else:                                           # y* one-hot
            ys = [E.v('ys', y) for y in range(n) if le[m][y]]; E.S.add_clause(ys)
            for p, q in itertools.combinations(ys, 2): E.S.add_clause([-p, -q])
            for y in range(n):
                if not le[m][y]: continue
                Y = E.v('ys', y)
                E.S.add_clause([-Y] + [f(m, y, w) for w in range(n) if jn[m][w] == y])
                for z in range(n):
                    if le[z][y]: continue
                    for w in range(n):
                        if le[z][jn[m][w]]: E.S.add_clause([-Y, -f(m, z, w)])
                if claim == 'gfp':
                    if y != m: o = E.v('bad', y); E.iff_and(o, [Y, -f(m, y, y)]); bad.append(o)
                else:
                    for g in range(n):
                        for w in range(n):
                            if not le[g][w]: o = E.v('bad', y, g, w); E.iff_and(o, [Y, B(m, g), f(m, y, w)]); bad.append(o)
    else:
        xs = [x for x in range(n) if not le[x][m] and rk[x] <= K - 1]
        ent = {}
        for x in xs: o = E.v('aent', x); E.iff_and(o, [r(K - 1, x), A(x, m)]); ent[x] = o
        if not ent: E.S.delete(); return None
        E.S.add_clause(list(ent.values())); E.S.add_clause([-yle(m, m)])
        if claim == 'fmm_le_B': bad.append(-fle(m, m, m))
        elif claim == 'fmm_in':
            for g in range(n): o = E.v('bad', g); E.iff_and(o, [f(m, m, g), -r(K - 1, g)]); bad.append(o)
        elif claim == 'bentry':
            for g in range(n): o = E.v('bad', g); E.iff_and(o, [B(m, g), -r(K - 1, g)]); bad.append(o)
        else:
            for x in xs:
                q = mt[x][m]
                if claim == 'meet_pre':
                    o = E.v('bad', x); E.iff_and(o, [ent[x], -fle(q, m, q)]); bad.append(o)
                else:
                    tgt = x if claim == 'bm_le_x' else q
                    for g in range(n):
                        if not le[g][tgt]: o = E.v('bad', x, g); E.iff_and(o, [ent[x], B(m, g)]); bad.append(o)
    E.S.add_clause(bad)
    if not E.S.solve(): E.S.delete(); return False
    F = E.decode(); E.S.delete()
    st = stages(L, F); inR = lambda z, j: st[z] is not None and st[z] <= j - s
    assert inR(m, K) and not inR(m, K - 1) and not inR(L.top, K + 1)
    assert all(rk[z] < K or z == m or claim.startswith('C_') for z in range(n) if inR(z, K)) and all(rk[z] <= K for z in range(n) if inR(z, K)) and all(rk[z] <= K - 1 for z in range(n) if inR(z, K - 1))
    bm = b_of(L, F, m)
    if claim in A_CLAIMS:
        low = [p for p in L.covers_dn[m] if rk[p] == K - 1 and inR(p, K - 1) and le[F[p][m]][p]]; assert low
        y = ystar(L, F, m)
        viol = {'bm_eq_feeder': any(bm != p for p in low), 'C_bm_eq_feeder': any(bm != p for p in low),
                'C_a_feeder_le': any(not le[a_of(L, F, p)][m] for p in low), 'a_feeder_le': any(not le[a_of(L, F, p)][m] for p in low),
                'fmm_le': not le[F[m][m]][m], 'top_ge_bm': not le[bm][F[m][L.top]], 'w_ge_bm': not le[bm][F[m][y]],
                'gfp': not gfp_ok(L, F, m)}[claim]
    else:
        X = [x for x in range(n) if not le[x][m] and inR(x, K - 1) and a_of(L, F, x) == m]; assert X and not le[m][F[m][m]]
        viol = {'bentry': not inR(bm, K - 1), 'bm_le_x': any(not le[bm][x] for x in X),
                'bm_le_meet': any(not le[bm][mt[x][m]] for x in X), 'meet_pre': any(not le[F[mt[x][m]][m]][mt[x][m]] for x in X),
                'fmm_le_B': not le[F[m][m]][m], 'fmm_in': not inR(F[m][m], K - 1)}[claim]
    assert viol
    return F

if __name__ == '__main__':
    claim = sys.argv[1]; ahead = 'ahead' in sys.argv; C = collections.Counter(); best = None
    for L in lattices([a for a in sys.argv[2:] if a != 'ahead']):
        if L.height < 2: continue
        hit = None
        for m in range(L.n):
            if 1 <= L.rank[m] < L.height:
                res = query(L, m, claim, ahead)
                if res: hit = (m, res); break
        C['counterexample' if hit else 'none'] += 1
        if hit and (best is None or L.n < best[0].n): best = (L, hit)
    print(f"claim {claim}{' ahead' if ahead else ''}: {dict(C)}" + (f"; smallest counterexample |L| = {best[0].n}, rank(m) = {best[0].rank[best[1][0]]}" if best else ''), flush=True)
    if best:
        import json; json.dump(dict(sets=best[0].S, F=best[1][1], m=best[1][0]), open(f"single_claim_{claim}{'_ahead' if ahead else ''}_min{best[0].n}.json", 'w'))
