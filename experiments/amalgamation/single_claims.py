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
  noic_fi: (as a 'claim', a counterexample is) a configuration with b(m) = m' for a lower feeder and no interval cell
           at m — tests whether feeder identity alone (all the history the meet lemma uses) forces the cell
  B claims: bentry        b(m) ∈ R_{K−1}  (Programme B's conjecture; = BEntry by the height bound)
            bm_le_x       b(m) ≤ x
            bm_le_meet    b(m) ≤ x ⊓ m
            meet_pre      F(x ⊓ m, m) ≤ x ⊓ m
            fmm_le_B      F(m, m) ≤ m
            fmm_in        F(m, m) ∈ R_{K−1}
  'ahead': index-sensitivity test, m placed at stage J = K − 1 (one ahead): R_J ranks ≤ K with unique rank-K
           element m ∉ R_{J−1}, R_{J−1} ranks ≤ K − 1, ⊤ ∉ R_{J+1}, feeders/entries from R_{J−1}.
  §34.3z¹⁶⁴ claims (use with 'multi'): side_w  w ∈ R_K;  side  (m′, w] ∩ R_K ≠ ∅;  below_w  a height-K element of R_K below w
  §34.3z¹⁷³ (with 'multi'): bcup   some top x with b(x) ∈ R_{K−2}, b(x) < x has an upward cell away from m
                            sibup  some top x ≠ m′ with b(x) = b(m′) has an upward cell away from m
  §34.3z¹⁸⁹ (with 'multi'): stabletop  every stage-(K−1) sibling configuration (p, c) whose fibre has a maximum U (F(p,U) = c, m ≰ U,
                            S ⊆ ↓U) has a comparable column in (c, U]   [refuted: |L| = 10]
                            pairjump   every stage-(K−1) sibling configuration with two fibre columns v₁, v₂ whose join is off m and outside
                            the fibre has a comparable column in the fibre (covers "jump with m ≰ ⋁S ⇒ FibreTopAt")
  §34.3z¹⁹⁰ ablation flags for 'upcell': nofi (drop b(m) = m′), icok (drop ¬IC(m)), notightK1 (drop R_{K−1} tightness),
                            nofeeder (no lower feeder required), needcfg (require a stage-(K−1) sibling configuration)
  §34.3z¹⁸³ (with 'multi'): topfibre  some new top c of R_{K−1} with p ⋖ c, F(p,c) = p has a fibre column v (F(p,v) = c, m ≰ v) and a comparable column in (c, v]
  §34.3z¹⁷⁸ (with 'multi'): famup  FamilyUpCell: in a sibling configuration some new top with the same B-source has an upward cell away from m
  §34.3z¹⁷⁴ (with 'multi'): bcupnew  as bcup with x new at stage K − 1 (x ∉ R_{K−2}; then b(x) ⋖ x)
  §34.3z¹⁷² (with 'multi'): upcell  some top row x of R_{K−1} has a cell at a column z > x with m ≰ z
  §34.3z¹⁷¹ (with 'multi'), at the immediate feeder drop r = F(m′, w), m′ ≰ r:
            abovea    h(a(m′)) ≤ K − 1 ⇒ some top x ≥ a(m′) is a descent-witness row
            fxq       every top x ≤ r has r ≤ F(x, w)
            ontime    r an on-time top ⇒ some top x ≤ r with (x, w) a descent witness
            latejoin  r not an on-time top ⇒ some top x with x ⊔ r = a(r) and (x, a(r)) a descent witness
  §34.3z¹⁷⁰ (with 'multi'): dropbelow  for every feeder drop q ∈ (m′, w] (F(m′,q) ≤ q, m′ ≰ F(m′,q)) some top of R_{K−1} lies below F(m′,q)
  §34.3z¹⁶⁹ (with 'multi'): dwit  a descent witness: x ∈ T_{K−1}, v ≱ m, x < v, F(x,v) ≤ v, x ≤ F(x,q) on row-pre-fixed q ∈ (x, v]
  §34.3z¹⁶⁸ (with 'multi'): mech  some y ∈ T_{K−1} has a(y) a rank-K top ≠ m, or some rank-K top z ≠ m has b(z) ∈ R_{K−1}, b(z) ≤ z
  §34.3z¹⁶⁸ (with 'multi'): bdom  every late B-parent (F(x,z) = x, rank x < K − 1) of a top z ≠ m lies below a rank-(K−1) element of R_{K−1}
  §34.3z¹⁶⁷ (with 'multi'): alltops  every top z ≠ m of R_K has a fixed-edge parent (F(x,z) ∈ {x, z}) of rank K − 1
  §34.3z¹⁶⁵ (with 'multi'): topparent  some rank-K top z ≠ m has an A- or B-parent of rank K − 1;  sibling  the row m′ has a cell at a rank-K column z ≠ m;  soleB  m is the only B-entry of rank K;  soleA  no A-entry z ≠ m of rank K
  rmin=R: only m of rank ≥ R (TopParent is SecondEntry itself at rank 2, where every parent ≠ ⊥ has rank 1)
  flags: notop (drop ⊤ ∉ R_{K+1}), multi (drop uniqueness of m), post / strictpre (lower feeders diagonal post-fixed / not), nopostlayer (no rank-(K−1) element of R_{K−1} post-fixed)
  python3 single_claims.py CLAIM [ahead] [notop] [multi] (sweep P NMAX | closure K M SEED COUNT)
"""
import sys, collections, itertools
sys.path.insert(0, '../separation')
import separator_stages as ss
from amalg_sat import Enc
from rstages import stages, a_of, b_of
from tight_probe import helpers, lattices
from gfp_top import ystar, gfp_ok

A_CLAIMS = ('stabletop', 'pairjump', 'topfibre', 'famup', 'bcupnew', 'bcup', 'sibup', 'upcell', 'abovea', 'fxq', 'ontime', 'latejoin', 'dropbelow', 'dwit', 'mech', 'bdom', 'alltops', 'topparent', 'sibling', 'soleB', 'soleA', 'below_w', 'side', 'side_w', 'feeder_post', 'noic_fi', 'C_bm_eq_feeder', 'C_a_feeder_le', 'bm_eq_feeder', 'w_ge_bm', 'top_ge_bm', 'a_feeder_le', 'fmm_le', 'gfp')
B_CLAIMS = ('bentry', 'bm_le_x', 'bm_le_meet', 'meet_pre', 'fmm_le_B', 'fmm_in')

def ys_block(E, L, m, f):
    """One-hot y* = gfp of y ↦ m ⊔ F(m, y); yields (y, Y) for the candidate values."""
    n = L.n; le = L.le; jn = L.join
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
        yield y, Y

def query(L, m, claim, ahead=False):
    n = L.n; le = L.le; rk = L.rank; K = rk[m]; jn = L.join; mt = L.meet; s = 1 if ahead else 0
    if K - s < 1: return None
    E = Enc(L, K + 1 - s); fle, yle, ic = helpers(E, L); r = lambda j, z: E.v('r', j - s, z)
    if 'notop' not in sys.argv: E.S.add_clause([-r(K + 1, L.top)])
    E.S.add_clause([r(K, m)]); E.S.add_clause([-r(K - 1, m)])
    for z in range(n):
        if rk[z] > K or (rk[z] == K and z != m and not claim.startswith('C_') and 'multi' not in sys.argv): E.S.add_clause([-r(K, z)])
        if rk[z] > K - 1 and 'notightK1' not in sys.argv: E.S.add_clause([-r(K - 1, z)])   # 'notightK1' (§34.3z¹⁹⁰): drop R_{K−1} tightness
    B = lambda y, g: E.v('B', y, g); A = lambda x, g: E.v('A', x, g); f = lambda x, y, v: E.v('f', x, y, v)
    bad = []                                            # witnesses of ¬claim
    if claim in A_CLAIMS:
        feeders = [p for p in L.covers_dn[m] if rk[p] == K - 1]
        if not feeders: E.S.delete(); return None
        low = {}
        for p in feeders:
            o = E.v('low', p); E.iff_and(o, [r(K - 1, p), fle(p, m, p)]); low[p] = o
        if 'nofeeder' not in sys.argv: E.S.add_clause(list(low.values()))   # 'nofeeder' (§34.3z¹⁹⁰, upcell only): no lower feeder required
        for p in feeders:                            # §34.3z¹⁶⁵ flags: post (every lower feeder diagonal post-fixed) / strictpre (none is)
            if 'post' in sys.argv: E.S.add_clause([-low[p], yle(p, p)])
            if 'strictpre' in sys.argv: E.S.add_clause([-low[p], -yle(p, p)])
        if 'nopostlayer' in sys.argv:                # §34.3z¹⁶⁵: no rank-(K−1) element of R_{K−1} is diagonal post-fixed
            for x in range(n):
                if rk[x] == K - 1: E.S.add_clause([-r(K - 1, x), -yle(x, x)])
        if claim in ('stabletop', 'pairjump'):       # §34.3z¹⁸⁹ per-configuration fibre-join lemmas (see docstring)
            if K < 2: E.S.delete(); return None
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)
            E.S.add_clause([-ic(m)]); sels = []
            for c in range(n):
                if rk[c] != K - 1: continue
                for p in range(n):
                    if rk[p] != K - 2 or not le[p][c]: continue
                    com = [r(K - 1, c), -r(K - 2, c), r(K - 2, p), f(p, c, p)]
                    if claim == 'stabletop':
                        for U in range(n):
                            if not (le[c][U] and U != c and not le[m][U]): continue
                            S_ = E.v('stsel', p, c, U); sels.append(S_)
                            for lit in com + [f(p, U, c)]: E.S.add_clause([-S_, lit])
                            for v in range(n):
                                if le[c][v] and v != c and not le[m][v] and not le[v][U]: E.S.add_clause([-S_, -f(p, v, c)])
                            for y in range(n):
                                if le[c][y] and y != c and le[y][U]: E.S.add_clause([-S_, -fle(c, y, y)]); E.S.add_clause([-S_, -yle(c, y)])
                    else:
                        for v1 in range(n):
                            for v2 in range(v1 + 1, n):
                                if not (le[c][v1] and le[c][v2] and v1 != c and v2 != c and not le[v1][v2] and not le[v2][v1] and not le[m][jn[v1][v2]]): continue
                                S_ = E.v('pjsel', p, c, v1, v2); sels.append(S_)
                                for lit in com + [f(p, v1, c), f(p, v2, c), -f(p, jn[v1][v2], c)]: E.S.add_clause([-S_, lit])
                                for y in range(n):
                                    if le[c][y] and y != c and not le[m][y]:
                                        E.S.add_clause([-S_, -f(p, y, c), -fle(c, y, y)]); E.S.add_clause([-S_, -f(p, y, c), -yle(c, y)])
            if not sels: E.S.delete(); return None
            E.S.add_clause(sels)
        elif claim == 'topfibre':                    # §34.3z¹⁸³ TopFibre: some new top c of R_{K−1} with p ⋖ c, F(p,c) = p (p ∈ R_{K−2}),
            if K < (2 if 'k2' in sys.argv else 3): E.S.delete(); return None   # a fibre column v (c < v, m ≰ v, F(p,v) = c) and y ∈ (c, v] with F(c,y) ≤ y or y ≤ F(c,y); 'k2' admits K = 2 (p = ⊥)
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)
            E.S.add_clause([-ic(m)])
            for c in range(n):
                if rk[c] != K - 1: continue
                for p in range(n):
                    if rk[p] != K - 2 or not le[p][c]: continue
                    for v in range(n):
                        if not (le[c][v] and v != c and not le[m][v]): continue
                        for y in range(n):
                            if not (le[c][y] and y != c and le[y][v]): continue
                            base = [-r(K - 1, c), r(K - 2, c), -r(K - 2, p), -f(p, c, p), -f(p, v, c)]
                            E.S.add_clause(base + [-fle(c, y, y)]); E.S.add_clause(base + [-yle(c, y)])
        elif claim == 'famup':                       # §34.3z¹⁷⁸ FamilyUpCell: noic_fi + a sibling configuration (x, c new tops of R_{K−1},
            if K < 3: E.S.delete(); return None         # b(x) = b(c) = p, x ∥ c, u a drop column of x with F(p, u) = c, m ≰ u)
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)   # and no new top y with b(y) = p
            E.S.add_clause([-ic(m)])                                                            # has an upward cell away from m
            def geq(x, q):
                k_ = ('geq', x, q)
                if k_ not in E.vars: o = E.v(*k_); E.iff_or(o, [E.v('f', x, q, w_) for w_ in range(n) if le[x][w_]])
                return E.vars[k_]
            tops_ = [x for x in range(n) if rk[x] == K - 1]; sels = []
            for p in range(n):
                if rk[p] != K - 2: continue
                ch = [x for x in tops_ if le[p][x]]
                for x in ch:
                    for c in ch:
                        if c == x or le[c][x] or le[x][c]: continue
                        for u in range(n):
                            if not (le[x][u] and u != x and not le[m][u] and le[c][u]): continue
                            S_ = E.v('fsel', p, x, c, u); sels.append(S_)
                            for lit in (r(K - 1, x), -r(K - 2, x), r(K - 1, c), -r(K - 2, c), B(x, p), B(c, p), f(p, u, c),
                                        fle(x, u, u), -geq(x, u)):
                                E.S.add_clause([-S_, lit])
                            for y in ch:
                                for z in range(n):
                                    if le[y][z] and z != y and not le[m][z]:
                                        E.S.add_clause([-S_, -r(K - 1, y), r(K - 2, y), -B(y, p), -fle(y, z, y)])
                                        E.S.add_clause([-S_, -r(K - 1, y), r(K - 2, y), -B(y, p), -yle(y, z)])
            if not sels: E.S.delete(); return None
            E.S.add_clause(sels)
        elif claim in ('bcupnew', 'bcup', 'sibup'):  # §34.3z¹⁷³: UpCell restricted to tops x with b(x) ∈ R_{K−2}, b(x) < x (bcup)
            if K < 2: E.S.delete(); return None
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)   # / with b(x) = b(m′), x ≠ m′ (sibup)
            E.S.add_clause([-ic(m)])
            def adm(x):
                k_ = ('adm', x)
                if k_ in E.vars: return E.vars[k_]
                terms = []
                for g in range(n):
                    if claim in ('bcup', 'bcupnew'):     # bcupnew: also x new at stage K − 1 (x ∉ R_{K−2}), so b(x) ⋖ x
                        if le[g][x] and g != x:
                            t_ = E.v('admt', x, g); E.iff_and(t_, [B(x, g), r(K - 2, g)] + ([-r(K - 2, x)] if claim == 'bcupnew' else [])); terms.append(t_)
                    else:
                        for p in feeders:
                            if x == p: continue
                            t_ = E.v('admt', x, g, p); E.iff_and(t_, [B(x, g), B(p, g), E.v('fi', p)]); terms.append(t_)
                o = E.v(*k_); E.iff_or(o, terms) if terms else E.S.add_clause([-o])
                return o
            for x in range(n):
                if rk[x] != K - 1: continue
                for z in range(n):
                    if le[x][z] and z != x and not le[m][z]:
                        E.S.add_clause([-r(K - 1, x), -adm(x), -fle(x, z, x)]); E.S.add_clause([-r(K - 1, x), -adm(x), -yle(x, z)])
        elif claim == 'upcell':                      # §34.3z¹⁷²: noic_fi and no top row x of R_{K−1} has a cell at a column z > x with m ≰ z
            if 'nofeeder' in sys.argv: o = E.v('true'); E.S.add_clause([o]); bad.append(o)
            for p in feeders:                        # §34.3z¹⁹⁰ ablation flags: 'nofi' drops b(m) = m′, 'icok' drops ¬IC(m)
                if 'nofeeder' in sys.argv: break
                if 'nofi' in sys.argv: bad.append(low[p])
                else: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)
            if 'icok' not in sys.argv: E.S.add_clause([-ic(m)])
            if 'needcfg' in sys.argv:                # §34.3z¹⁹⁰: require a stage-(K−1) sibling configuration with nonempty fibre
                if K < 2: E.S.delete(); return None
                cs = []
                for c in range(n):
                    if rk[c] != K - 1: continue
                    for p in range(n):
                        if rk[p] != K - 2 or not le[p][c]: continue
                        for v in range(n):
                            if le[c][v] and v != c and not le[m][v]:
                                o = E.v('cfg', p, c, v); cs.append(o)
                                for lit in (r(K - 1, c), -r(K - 2, c), r(K - 2, p), f(p, c, p), f(p, v, c)): E.S.add_clause([-o, lit])
                if not cs: E.S.delete(); return None
                E.S.add_clause(cs)
            for x in range(n):
                if rk[x] != K - 1: continue
                for z in range(n):
                    if le[x][z] and z != x and not le[m][z]:
                        E.S.add_clause([-r(K - 1, x), -fle(x, z, x)]); E.S.add_clause([-r(K - 1, x), -yle(x, z)])
        elif claim in ('abovea', 'fxq', 'ontime', 'latejoin'):  # §34.3z¹⁷¹: the immediate feeder drop at w (r = F(m′, w), m′ ≰ r)
            E.S.add_clause([-ic(m)])
            def geq(x, q):
                k_ = ('geq', x, q)
                if k_ not in E.vars: o = E.v(*k_); E.iff_or(o, [E.v('f', x, q, w_) for w_ in range(n) if le[x][w_]])
                return E.vars[k_]
            def P(x, q):
                k_ = ('Pdrop', x, q)
                if k_ not in E.vars: o = E.v(*k_); E.iff_and(o, [fle(x, q, q), -geq(x, q)])
                return E.vars[k_]
            fails = lambda x, v: [-r(K - 1, x), -fle(x, v, v)] + [P(x, u) for u in range(n) if le[x][u] and u != x and le[u][v]]
            sels = []
            for y, Y in ys_block(E, L, m, f):
                for wv in range(n):
                    if jn[m][wv] != y or le[m][wv] or le[wv][m]: continue
                    for p in feeders:
                        for rv in range(n):
                            if not le[rv][wv] or le[p][rv]: continue
                            base = (Y, f(m, y, wv), low[p], B(m, p), f(p, wv, rv))
                            if claim == 'abovea':        # h(a(m′)) ≤ K − 1 and no top x ≥ a(m′) is a descent-witness row (any v ≱ m)
                                for g in range(n):
                                    if rk[g] > K - 1: continue
                                    S_ = E.v('tsel', y, wv, p, rv, g); sels.append(S_)
                                    for lit in base + (A(p, g),): E.S.add_clause([-S_, lit])
                                    for x in range(n):
                                        if rk[x] != K - 1 or not le[g][x]: continue
                                        for v in range(n):
                                            if le[x][v] and v != x and not le[m][v]: E.S.add_clause([-S_] + fails(x, v))
                            elif claim == 'fxq':           # some x ∈ T, x ≤ r, with r ≰ F(x, w)
                                for x in range(n):
                                    if rk[x] != K - 1 or not le[x][rv]: continue
                                    for t in range(n):
                                        if le[rv][t]: continue
                                        S_ = E.v('tsel', y, wv, p, rv, x, t); sels.append(S_)
                                        for lit in base + (r(K - 1, x), f(x, wv, t)): E.S.add_clause([-S_, lit])
                            elif claim == 'ontime':      # r an on-time top, and no x ∈ T, x ≤ r with (x, w) a descent witness
                                if rk[rv] != K - 1: continue
                                S_ = E.v('tsel', y, wv, p, rv); sels.append(S_)
                                for lit in base + (r(K - 1, rv),): E.S.add_clause([-S_, lit])
                                for x in range(n):
                                    if rk[x] == K - 1 and le[x][rv]: E.S.add_clause([-S_] + fails(x, wv))
                            else:                        # r not an on-time top; no x ∈ T with x ⊔ r = a(r) ≱ m and (x, a(r)) a witness
                                for g in range(n):
                                    S_ = E.v('tsel', y, wv, p, rv, g); sels.append(S_)
                                    for lit in base + (A(rv, g),): E.S.add_clause([-S_, lit])
                                    if rk[rv] == K - 1: E.S.add_clause([-S_, -r(K - 1, rv)])
                                    if le[m][g]: continue
                                    for x in range(n):
                                        if rk[x] == K - 1 and jn[x][rv] == g and x != g: E.S.add_clause([-S_] + fails(x, g))
            if not sels: E.S.delete(); return None
            bad.append(E.v('tany')); E.S.add_clause([-E.v('tany')] + sels)
        elif claim == 'dropbelow':                   # §34.3z¹⁷⁰: noic_fi with a feeder drop q ∈ (m′, w] (F(m′,q) ≤ q, m′ ≰ r = F(m′,q))
            E.S.add_clause([-ic(m)])                    # such that no rank-(K−1) element of R_{K−1} lies below r
            sels = []
            for y, Y in ys_block(E, L, m, f):
                for wv in range(n):
                    if jn[m][wv] != y or le[m][wv] or le[wv][m]: continue
                    for p in feeders:
                        for q in range(n):
                            if not (le[p][q] and q != p and le[q][wv]): continue
                            for rv in range(n):
                                if not le[rv][q] or le[p][rv]: continue
                                S_ = E.v('dsel', y, wv, p, q, rv); sels.append(S_)
                                for lit in (Y, f(m, y, wv), low[p], B(m, p), f(p, q, rv)): E.S.add_clause([-S_, lit])
                                for x in range(n):
                                    if rk[x] == K - 1 and le[x][rv]: E.S.add_clause([-S_, -r(K - 1, x)])
            if not sels: E.S.delete(); return None
            bad.append(E.v('dany')); E.S.add_clause([-E.v('dany')] + sels)
        elif claim == 'dwit':                        # §34.3z¹⁶⁹: noic_fi and no descent witness: no x ∈ T, v ≱ m with x < v, F(x,v) ≤ v and
            if 'nofeeder' in sys.argv: o = E.v('true'); E.S.add_clause([o]); bad.append(o)       # x ≤ F(x,q) for every
            else:                                                                               # row-pre-fixed q ∈ (x, v]
                for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)   # (§34.3z¹⁹¹: flags as upcell)
            E.S.add_clause([-ic(m)])
            def geq(x, q):
                k_ = ('geq', x, q)
                if k_ not in E.vars: o = E.v(*k_); E.iff_or(o, [E.v('f', x, q, w_) for w_ in range(n) if le[x][w_]])
                return E.vars[k_]
            def P(x, q):
                k_ = ('Pdrop', x, q)
                if k_ not in E.vars: o = E.v(*k_); E.iff_and(o, [fle(x, q, q), -geq(x, q)])
                return E.vars[k_]
            for x in range(n):
                if rk[x] != K - 1: continue
                for v in range(n):
                    if le[x][v] and v != x and not le[m][v]:
                        E.S.add_clause([-r(K - 1, x), -fle(x, v, v)] + [P(x, q) for q in range(n) if le[x][q] and q != x and le[q][v]])
        elif claim == 'mech':                        # §34.3z¹⁶⁸: noic_fi with neither canonical TopParent mechanism:
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)   # no y ∈ T with a(y) a top ≠ m,
            E.S.add_clause([-ic(m)])                                                            # no top z ≠ m with b(z) ∈ R_{K−1}, b(z) ≤ z
            for y in range(n):
                if rk[y] != K - 1: continue
                for g in range(n):
                    if rk[g] == K and g != m: E.S.add_clause([-r(K - 1, y), -A(y, g)])
            for z in range(n):
                if z == m or rk[z] != K: continue
                for g in range(n):
                    if le[g][z]: E.S.add_clause([-B(z, g), -r(K - 1, g)])
        elif claim == 'bdom':                        # §34.3z¹⁶⁸: noic_fi and a late B-parent x (F(x, z) = x, rank x < K − 1) of a top z ≠ m with no rank-(K−1) y ≥ x in R_{K−1}
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)
            E.S.add_clause([-ic(m)])
            pairs = [(z, x) for z in range(n) if z != m and rk[z] == K for x in range(n) if rk[x] < K - 1]
            if not pairs: E.S.delete(); return None
            E.S.add_clause([E.v('sel', z, x) for z, x in pairs])
            for z, x in pairs:
                S_ = E.v('sel', z, x)
                E.S.add_clause([-S_, r(K, z)]); E.S.add_clause([-S_, r(K - 1, x)]); E.S.add_clause([-S_, f(x, z, x)])
                for y in range(n):
                    if rk[y] == K - 1 and le[x][y]: E.S.add_clause([-S_, -r(K - 1, y)])
        elif claim == 'alltops':                     # §34.3z¹⁶⁷: noic_fi and some rank-K top z ≠ m of R_K has no fixed-edge parent of rank K − 1
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)
            E.S.add_clause([-ic(m)])
            Zs = [z for z in range(n) if z != m and rk[z] == K]
            if not Zs: E.S.delete(); return None
            E.S.add_clause([E.v('zsel', z) for z in Zs])
            for z in Zs:
                E.S.add_clause([-E.v('zsel', z), r(K, z)])
                for g in range(n):
                    if rk[g] == K - 1: E.S.add_clause([-E.v('zsel', z), -r(K - 1, g), -f(g, z, g)]); E.S.add_clause([-E.v('zsel', z), -r(K - 1, g), -f(g, z, z)])
        elif claim == 'topparent':                   # §34.3z¹⁶⁵: noic_fi and no rank-K top z ≠ m has a fixed-edge parent of rank K − 1 in R_{K−1}
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)
            E.S.add_clause([-ic(m)])
            for z in range(n):
                if z == m or rk[z] != K: continue
                for g in range(n):
                    if rk[g] == K - 1: E.S.add_clause([-B(z, g), -r(K - 1, g)]); E.S.add_clause([-r(K - 1, g), -A(g, z)])
        elif claim == 'sibling':                     # §34.3z¹⁶⁵: noic_fi and the row m′ has no cell at any rank-K column z ≠ m
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)
            E.S.add_clause([-ic(m)])
            for p in feeders:
                for z in range(n):
                    if z != m and rk[z] == K: E.S.add_clause([-E.v('fi', p), -fle(p, z, p)]); E.S.add_clause([-E.v('fi', p), -yle(p, z)])
        elif claim in ('soleB', 'soleA'):            # §34.3z¹⁶⁵: noic_fi with m the sole B-entry (soleB) / no A-entry z ≠ m (soleA) at rank K
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)
            E.S.add_clause([-ic(m)])
            for z in range(n):
                if z == m or rk[z] != K: continue
                for g in range(n):
                    if claim == 'soleB': E.S.add_clause([-B(z, g), -r(K - 1, g)])
                    else: E.S.add_clause([-r(K - 1, g), -A(g, z)])
        elif claim == 'below_w':         # §34.3z¹⁶⁴: noic_fi plus no on-time height-K element of R_K below w (below_d: below D-limit)
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)
            E.S.add_clause([-ic(m)])
            for y, Y in ys_block(E, L, m, f):
                for wv in range(n):
                    for z in range(n):
                        if le[z][wv] and rk[z] == K: E.S.add_clause([-Y, -f(m, y, wv), -r(K, z)])
        elif claim in ('side', 'side_w'):             # §34.3z¹⁶⁴: noic_fi plus no on-time side element: (m', w] ∩ R_K = ∅ (side_w: w ∉ R_K)
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)
            E.S.add_clause([-ic(m)])
            for y, Y in ys_block(E, L, m, f):
                for wv in range(n):
                    for p in feeders:
                        for z in range(n):
                            if (z == wv) if claim == 'side_w' else (le[p][z] and z != p and le[z][wv]):
                                E.S.add_clause([-Y, -f(m, y, wv), -E.v('fi', p), -r(K, z)])
        elif claim == 'feeder_post':                 # §34.3z¹⁶³: is every lower feeder diagonal post-fixed (m' ≤ F(m', m'))?
            for p in feeders: o = E.v('fp', p); E.iff_and(o, [low[p], -yle(p, p)]); bad.append(o)
        elif claim == 'noic_fi':                     # §34.3z¹⁶²: no interval cell at m although b(m) is a lower feeder
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); bad.append(o)
            E.S.add_clause([-ic(m)])
        elif claim in ('bm_eq_feeder', 'C_bm_eq_feeder'):
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
            for y, Y in ys_block(E, L, m, f):
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
    assert inR(m, K) and not inR(m, K - 1) and ('notop' in sys.argv or not inR(L.top, K + 1))
    assert all(rk[z] < K or z == m or claim.startswith('C_') or 'multi' in sys.argv for z in range(n) if inR(z, K)) and all(rk[z] <= K for z in range(n) if inR(z, K)) and ('notightK1' in sys.argv or all(rk[z] <= K - 1 for z in range(n) if inR(z, K - 1)))
    bm = b_of(L, F, m)
    if claim in A_CLAIMS:
        low = [p for p in L.covers_dn[m] if rk[p] == K - 1 and inR(p, K - 1) and le[F[p][m]][p]]; assert low or 'nofeeder' in sys.argv
        y = ystar(L, F, m)
        from gfp_top import ic as ic_py
        wv = F[m][y]; side = [z for z in range(n) if le[bm][z] and z != bm and le[z][wv] and inR(z, K)]
        tops = [z for z in range(n) if z != m and rk[z] == K]
        wq = F[m][y]
        drops = [q for q in range(n) if le[bm][q] and q != bm and le[q][wq] and le[F[bm][q]][q] and not le[bm][F[bm][q]]]
        rr = F[bm][wq]; Tq = [x for x in range(n) if inR(x, K - 1) and rk[x] == K - 1]
        def dw(x, v): return le[x][v] and x != v and le[F[x][v]][v] and not le[m][v] and all(le[x][F[x][u]] for u in range(n) if le[x][u] and u != x and le[u][v] and le[F[x][u]][u])
        idrop = (bm in low) and not ic_py(L, F, m) and not le[bm][rr]
        am = a_of(L, F, bm)
        upc = lambda x: any(le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]]) for z in range(n))
        Tq2 = [x for x in range(n) if inR(x, K - 1) and rk[x] == K - 1]
        def famviol():
            ups = lambda y: any(le[y][z] and z != y and not le[m][z] and (le[F[y][z]][y] or le[z][F[y][z]]) for z in range(n))
            for x in Tq2:
                for c in Tq2:
                    p_ = b_of(L, F, x)
                    if c == x or le[c][x] or le[x][c] or inR(x, K - 2) or inR(c, K - 2) or b_of(L, F, c) != p_ or rk[p_] != K - 2: continue
                    for u in range(n):
                        if le[x][u] and u != x and le[c][u] and not le[m][u] and le[F[x][u]][u] and not le[x][F[x][u]] and F[p_][u] == c:
                            if not any(ups(y) for y in Tq2 if not inR(y, K - 2) and b_of(L, F, y) == p_): return True
            return False
        def topfib():
            for c in Tq2:
                if inR(c, K - 2): continue
                for p in range(n):
                    if not (rk[p] == K - 2 and inR(p, K - 2) and le[p][c] and F[p][c] == p): continue
                    for v in range(n):
                        if le[c][v] and v != c and not le[m][v] and F[p][v] == c:
                            if any(le[c][y] and y != c and le[y][v] and (le[F[c][y]][y] or le[y][F[c][y]]) for y in range(n)): return True
            return False
        def fjviol(kind):
            for c in Tq2:
                if inR(c, K - 2): continue
                for p in range(n):
                    if not (rk[p] == K - 2 and inR(p, K - 2) and le[p][c] and F[p][c] == p): continue
                    S = [v for v in range(n) if le[c][v] and v != c and not le[m][v] and F[p][v] == c]
                    if not S or any(le[F[c][y]][y] or le[y][F[c][y]] for y in S): continue
                    U = S[0]
                    for v in S[1:]: U = L.join[U][v]
                    if kind == 'stable' and U in S: return True
                    if kind == 'pair' and any(not le[m][L.join[a_][b_]] and L.join[a_][b_] not in S and not le[a_][b_] and not le[b_][a_] for a_ in S for b_ in S): return True
            return False
        viol = {'stabletop': (bm in low) and not ic_py(L, F, m) and fjviol('stable'),
                'pairjump': (bm in low) and not ic_py(L, F, m) and fjviol('pair'),
                'topfibre': (bm in low) and not ic_py(L, F, m) and not topfib(),
                'famup': (bm in low) and not ic_py(L, F, m) and famviol(),
                'bcupnew': (bm in low) and not ic_py(L, F, m) and not any(not inR(x, K - 2) and inR(b_of(L, F, x), K - 2) and le[b_of(L, F, x)][x] and b_of(L, F, x) != x and upc(x) for x in Tq2),
                'bcup': (bm in low) and not ic_py(L, F, m) and not any(inR(b_of(L, F, x), K - 2) and le[b_of(L, F, x)][x] and b_of(L, F, x) != x and upc(x) for x in Tq2),
                'sibup': (bm in low) and not ic_py(L, F, m) and not any(x != bm and b_of(L, F, x) == b_of(L, F, bm) and upc(x) for x in Tq2),
                'upcell': (True if 'nofeeder' in sys.argv else bool(low) if 'nofi' in sys.argv else bm in low) and ('icok' in sys.argv or not ic_py(L, F, m)) and not any(inR(x, K - 1) and rk[x] == K - 1 and le[x][z] and z != x and not le[m][z] and (le[F[x][z]][x] or le[z][F[x][z]]) for x in range(n) for z in range(n)),
                'abovea': idrop and rk[am] <= K - 1 and not any(le[am][x] and dw(x, v) for x in Tq for v in range(n)),
                'fxq': idrop and any(le[x][rr] and not le[rr][F[x][wq]] for x in Tq),
                'ontime': idrop and rr in Tq and not any(le[x][rr] and dw(x, wq) for x in Tq),
                'latejoin': idrop and rr not in Tq and not any(L.join[x][rr] == a_of(L, F, rr) and dw(x, a_of(L, F, rr)) for x in Tq),
                'dropbelow': (bm in low) and not ic_py(L, F, m) and any(not any(inR(x, K - 1) and rk[x] == K - 1 and le[x][F[bm][q]] for x in range(n)) for q in drops),
                'dwit': (True if 'nofeeder' in sys.argv else bm in low) and not ic_py(L, F, m) and not any(inR(x, K - 1) and rk[x] == K - 1 and le[x][v] and v != x and not le[m][v] and le[F[x][v]][v]
                        and all(le[x][F[x][q]] for q in range(n) if le[x][q] and q != x and le[q][v] and le[F[x][q]][q]) for x in range(n) for v in range(n)),
                'mech': (bm in low) and not ic_py(L, F, m) and not any(inR(y, K - 1) and rk[y] == K - 1 and a_of(L, F, y) != m and rk[a_of(L, F, y)] == K for y in range(n)) and not any(inR(b_of(L, F, z), K - 1) and le[b_of(L, F, z)][z] for z in tops),
                'bdom': (bm in low) and not ic_py(L, F, m) and any(inR(z, K) and inR(x, K - 1) and rk[x] < K - 1 and F[x][z] == x and not any(inR(y, K - 1) and rk[y] == K - 1 and le[x][y] for y in range(n)) for z in tops for x in range(n)),
                'alltops': (bm in low) and not ic_py(L, F, m) and any(inR(z, K) and not any(inR(g, K - 1) and rk[g] == K - 1 and F[g][z] in (g, z) for g in range(n)) for z in tops),
                'topparent': (bm in low) and not ic_py(L, F, m) and not any((inR(b_of(L, F, z), K - 1) and rk[b_of(L, F, z)] == K - 1) or any(inR(x, K - 1) and rk[x] == K - 1 and a_of(L, F, x) == z for x in range(n)) for z in tops),
                'sibling': (bm in low) and not ic_py(L, F, m) and not any(le[F[bm][z]][bm] or le[z][F[bm][z]] for z in tops),
                'soleB': (bm in low) and not ic_py(L, F, m) and not any(inR(b_of(L, F, z), K - 1) for z in tops),
                'soleA': (bm in low) and not ic_py(L, F, m) and not any(inR(x, K - 1) and a_of(L, F, x) == z for z in tops for x in range(n)),
                'below_w': (bm in low) and not ic_py(L, F, m) and not any(le[z][wv] and rk[z] == K and inR(z, K) for z in range(n)),
                'side': (bm in low) and not ic_py(L, F, m) and not side, 'side_w': (bm in low) and not ic_py(L, F, m) and not inR(wv, K),
                'feeder_post': any(not le[p][F[p][p]] for p in low), 'noic_fi': (bm in low) and not ic_py(L, F, m), 'bm_eq_feeder': any(bm != p for p in low), 'C_bm_eq_feeder': any(bm != p for p in low),
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

RMIN = next((int(a[5:]) for a in sys.argv if a.startswith('rmin=')), 1)

if __name__ == '__main__':
    claim = sys.argv[1]; ahead = 'ahead' in sys.argv; C = collections.Counter(); best = None
    for L in lattices([a for a in sys.argv[2:] if a not in ('ahead', 'notop', 'multi', 'post', 'strictpre', 'nopostlayer', 'k2', 'nofi', 'icok', 'notightK1', 'nofeeder', 'needcfg') and not a.startswith('rmin=')]):
        if L.height < 2: continue
        hit = None
        for m in range(L.n):
            if max(1, RMIN) <= L.rank[m] < L.height:
                res = query(L, m, claim, ahead)
                if res: hit = (m, res); break
        C['counterexample' if hit else 'none'] += 1
        if hit and (best is None or L.n < best[0].n): best = (L, hit)
    print(f"claim {claim}{' ahead' if ahead else ''}: {dict(C)}" + (f"; smallest counterexample |L| = {best[0].n}, rank(m) = {best[0].rank[best[1][0]]}" if best else ''), flush=True)
    if best:
        import json; json.dump(dict(sets=best[0].S, F=best[1][1], m=best[1][0]), open(f"single_claim_{claim}{'_ahead' if ahead else ''}{''.join('_' + f for f in ('notop', 'multi', 'post', 'strictpre', 'nopostlayer', 'nofi', 'icok', 'notightK1', 'nofeeder', 'needcfg') if f in sys.argv)}{f'_rmin{RMIN}' if RMIN > 1 else ''}_min{best[0].n}.json", 'w'))
