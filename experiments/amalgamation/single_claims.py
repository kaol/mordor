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
  bonly (§34.3z²²¹, with multi nopostlayer): noic_fi + a reachable B-only fork (from the seeded root of the feeder descent)
         whose SibConfig children are all not Good: an exact counterexample to BOnlyGoodChild
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
  §34.3z²⁰⁶ orbitlt (k = 1 only): MinUpCell hypotheses, w = F(m, y*), x = F(⊥, w) ≠ w of rank 1, no LT pair (x, v) on the orbit v ↦ F(x, v) from w
  §34.3z²⁰⁶ rowlt2 (k = 1 only): no LT pair on the row of the rank-1 element of the ⊥-descent from w*
  §34.3z²⁰⁶ rowlt (k = 1 only): as orbitlt, but no LT pair (x, v) on row x = F(⊥, w*) at all
  §34.3z²⁰⁶ desclt (k = 1 only): MinUpCell hypotheses and a column fixed point y = m ⊔ F(m,y), w = F(m,y) ≱ m, with x = F(⊥,w) ≠ w of
             rank 1 and F(x,w) ≰ w ('parm': x ∥ m)
  §34.3z²⁰⁵ lt (k = 1 only): MinUpCell hypotheses and no LT pair (x ∈ R_1 of rank 1, v ≱ m, x < v, F(x,v) ≤ v, F(⊥,v) ≤ x)
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

A_CLAIMS = ('backreach', 'topgoal', 'bonly', 'rowlt2', 'rowlt', 'orbitlt', 'desclt', 'lt', 'dominant', 'a1gen', 'a1cert', 'pajump', 'minhyp', 'stabletop', 'pairjump', 'topfibre', 'famup', 'bcupnew', 'bcup', 'sibup', 'upcell', 'abovea', 'fxq', 'ontime', 'latejoin', 'dropbelow', 'dwit', 'mech', 'bdom', 'alltops', 'topparent', 'sibling', 'soleB', 'soleA', 'below_w', 'side', 'side_w', 'feeder_post', 'noic_fi', 'C_bm_eq_feeder', 'C_a_feeder_le', 'bm_eq_feeder', 'w_ge_bm', 'top_ge_bm', 'a_feeder_le', 'fmm_le', 'gfp')
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

def bonly_check(L, F, m):
    """Python re-check of 'bonly': the seeded root of the feeder descent (as in cone_probe.py), the top graph with Lean
    semantics (TopEdge = SibConfig ∨ AEdge), and a reachable fork below k with a SibConfig child, no AEdge child, and no
    Good SibConfig child."""
    n = L.n; le = L.le; h = L.rank; K = h[m]; k = K - 1; st = stages(L, F)
    inR = lambda x, j: st[x] is not None and st[x] <= j
    new = lambda x, j: inR(x, j) and not inR(x, j - 1) and h[x] == j
    fib = lambda pp, cc: [v for v in range(n) if le[cc][v] and v != cc and not le[m][v] and F[pp][v] == cc]
    node = lambda x: inR(x, h[x]) and 1 <= h[x] <= k
    sib = lambda pp, cc: inR(pp, h[pp]) and new(cc, h[pp] + 1) and le[pp][cc] and pp != cc and F[pp][cc] == pp and bool(fib(pp, cc))
    aed = lambda x, y: inR(x, h[x]) and le[x][y] and y != x and le[y][F[x][y]] and not le[m][y] and new(y, h[x] + 1)
    upat = lambda x: any(le[x][u] and u != x and not le[m][u] and (le[F[x][u]][x] or le[u][F[x][u]]) for u in range(n))
    Bf = lambda y: b_of(L, F, y); mp = Bf(m); w = F[m][ystar(L, F, m)]
    if 'BACKREACH' in sys.argv:                    # 'backreach' (§34.3z²²²): some stage-k UpAt top has no backward path to an R_1 atom
        X = [x for x in range(n) if node(x)]
        par = {y: [x for x in X if h[y] == h[x] + 1 and (sib(x, y) or aed(x, y))] for y in X}
        def back(x):
            seen = {x}; todo = [x]
            while todo:
                y = todo.pop()
                for p_ in par.get(y, []):
                    if p_ not in seen: seen.add(p_); todo.append(p_)
            return any(h[y] == 1 for y in seen)
        return any(inR(x, k) and h[x] == k and upat(x) and not back(x) for x in range(n))
    if 'atomroot' in sys.argv:                     # roots: every atom of R_1
        X = [x for x in range(n) if node(x)]
        kids = {x: [y for y in range(n) if h[y] == h[x] + 1 and (sib(x, y) or aed(x, y))] for x in X}
        seen = {x for x in X if h[x] == 1}; todo = list(seen)
        while todo:
            x = todo.pop()
            for y in kids.get(x, []):
                if y not in seen: seen.add(y); todo.append(y)
        return 'vacuity' in sys.argv or not any(h[x] == k and upat(x) for x in seen)
    r_, e, i = mp, w, 0
    for _ in range(4 * n):
        t = F[r_][e]
        if le[t][r_] or le[e][t]: z = e; break
        if le[r_][t]: e = t; continue
        q = Bf(r_); e2 = F[q][e]
        if le[e2][q]: r_, z, i = q, e, i + 1; break
        r_, e, i = q, e2, i + 1
    else: return False
    if i == 0: return False
    upper = le[z][F[r_][z]] and not le[F[r_][z]][r_]
    root = r_ if upper and node(r_) else z
    if not node(root): return False
    X = [x for x in range(n) if node(x)]
    kids = {x: [y for y in range(n) if h[y] == h[x] + 1 and (sib(x, y) or aed(x, y))] for x in X}
    good = {}
    for s_ in range(k, 0, -1):
        for x in X:
            if h[x] == s_: good[x] = upat(x) if s_ == k else any(good.get(y, False) for y in kids[x])
    seen = {root}; todo = [root]
    while todo:
        x = todo.pop()
        for y in kids.get(x, []):
            if y not in seen and node(y): seen.add(y); todo.append(y)
    if 'TOPGOAL' in sys.argv:                      # 'topgoal' (§34.3z²²¹): no stage-k UpAt top reachable from the root
        jedge = (lambda x, y: h[x] == h[y] and x != y and inR(y, h[y]) and inR(L.join[x][y], h[x])) if 'joinedge' in sys.argv else \
                (lambda x, y: h[y] <= h[x] and x != y and inR(y, h[y]) and inR(L.join[x][y], h[y]) and ('rootlift' not in sys.argv or x == root)) if 'liftedge' in sys.argv else (lambda x, y: False)
        seen = {root}; todo = [root]
        while todo:
            x = todo.pop()
            for y in kids.get(x, []) + [y for y in X if jedge(x, y)]:
                if y not in seen: seen.add(y); todo.append(y)
        return not any(h[x] == k and upat(x) for x in seen)
    vac = 'vacuity' in sys.argv                    # non-vacuity control: drop the "no Good SibConfig child" conjunct
    return any(h[x] < k and any(sib(x, y) for y in range(n)) and not any(aed(x, y) for y in range(n)) and (vac or not any(sib(x, y) and good.get(y, False) for y in range(n))) for x in seen)

def query(L, m, claim, ahead=False):
    n = L.n; le = L.le; rk = L.rank; K = rk[m]; jn = L.join; mt = L.meet; s = 1 if ahead else 0
    if K - s < 1: return None
    E = Enc(L, K + 1 - s); fle, yle, ic = helpers(E, L); r = lambda j, z: E.v('r', j - s, z)
    if 'notop' not in sys.argv: E.S.add_clause([-r(K + 1, L.top)])
    E.S.add_clause([r(K, m)]); E.S.add_clause([-r(K - 1, m)])
    for z in range(n):
        if rk[z] > K or (rk[z] == K and z != m and not claim.startswith('C_') and 'multi' not in sys.argv): E.S.add_clause([-r(K, z)])
        if rk[z] > K - 1 and 'notightK1' not in sys.argv: E.S.add_clause([-r(K - 1, z)])   # 'notightK1' (§34.3z¹⁹⁰): drop R_{K−1} tightness
        if 'alltight' in sys.argv:                      # 'alltight' (§34.3z²²¹): every lower stage tight, R_j ⊆ {h ≤ j}
            for j in range(1, K - 1):
                if rk[z] > j: E.S.add_clause([-r(j, z)])
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
        if claim == 'dominant':                      # §34.3z²⁰²: MinUpCell hypotheses + a genuine A1 configuration (p, c, u) with y = a(c) a height-k
            E.S.add_clause([-ic(m)])                       # row of R_k and F(c, u) = c ⊔ y; violation: no A1Cert anywhere and y not forbidden
            sels = []                                      # (one-directional selectors o → …; the no-A1Cert part is universal)
            for c in range(n):
                if rk[c] != K - 1: continue
                for p in L.covers_dn[c]:
                    for y in range(n):
                        if rk[y] != K - 1 or le[c][y] or le[y][c]: continue
                        for u in range(n):
                            if not (le[c][u] and u != c and not le[m][u]): continue
                            o = E.v('dsel', p, c, y, u); sels.append(o)
                            for lit in (r(K - 1, c), f(p, c, p), f(p, u, c), B(c, p), A(c, y), r(K - 1, y), f(c, u, jn[c][y])): E.S.add_clause([-o, lit])
                            for g in range(n):             # y not other-ascending
                                if le[y][g] and g != y and g != m: E.S.add_clause([-o, -A(y, g)])
                            for v in range(n):             # y stationary ⇒ no initial pair
                                if le[y][v] and v != y and not le[m][v]: E.S.add_clause([-o, -A(y, y), -fle(y, v, v)])
            if not sels: E.S.delete(); return None
            bad.extend(sels)
            for c in range(n):                             # no A1Cert anywhere
                if rk[c] != K - 1: continue
                for p in L.covers_dn[c]:
                    for u in range(n):
                        if not (le[c][u] and u != c and not le[m][u]): continue
                        nb = [-r(K - 1, c), -f(p, c, p), -f(p, u, c)]
                        for z in range(n):
                            if not (le[c][z] and z != c and le[z][u]): continue
                            E.S.add_clause(nb + [-fle(c, z, c)]); E.S.add_clause(nb + [-yle(c, z)])
                            E.S.add_clause(nb + [-fle(c, z, z)] + [f(p, e, p) for e in range(n) if le[c][e] and e != c and le[e][z]])
        elif claim == 'a1gen':                         # §34.3z²⁰¹: a model of the hypotheses with a genuine A1 configuration with a fibre column
            if 'icok' not in sys.argv: E.S.add_clause([-ic(m)])   # (and, with 'rowtypes', the ¬UpCell row types); no claim about A1Cert
            for c in range(n):
                if rk[c] != K - 1: continue
                for p in L.covers_dn[c]:
                    for u in range(n):
                        if not (le[c][u] and u != c and not le[m][u]): continue
                        na = E.v('nonasc', c); E.iff_or(na, [A(c, g) for g in range(n) if not le[c][g]])
                        if 'selfnocell' in sys.argv:         # §34.3z²⁰¹: this genuine configuration's top c carries no off-m cell at all
                            o = E.v('a1selS', p, c, u)           # (one-directional selector: o → base ∧ no cell; corrected §34.3z²⁰¹)
                            for lit in (r(K - 1, c), f(p, c, p), f(p, u, c), B(c, p), na): E.S.add_clause([-o, lit])
                            for z in range(n):
                                if le[c][z] and z != c and not le[m][z]:
                                    E.S.add_clause([-o, -fle(c, z, c)]); E.S.add_clause([-o, -yle(c, z)])
                            if 'abovepnocell' in sys.argv:   # §34.3z²⁰¹: and no height-k top c′ ≥ p of R_k carries an off-m cell
                                for c2 in range(n):
                                    if rk[c2] != K - 1 or not le[p][c2] or c2 == c: continue
                                    for z in range(n):
                                        if le[c2][z] and z != c2 and not le[m][z]:
                                            E.S.add_clause([-o, -r(K - 1, c2), -fle(c2, z, c2)]); E.S.add_clause([-o, -r(K - 1, c2), -yle(c2, z)])
                            if 'sibnocell' in sys.argv:      # §34.3z²⁰¹: and no same-source top c′ (b(c′) = p, p ⋖ c′) carries an off-m cell
                                for c2 in range(n):
                                    if rk[c2] != K - 1 or p not in L.covers_dn[c2] or c2 == c: continue
                                    for z in range(n):
                                        if le[c2][z] and z != c2 and not le[m][z]:
                                            E.S.add_clause([-o, -r(K - 1, c2), -B(c2, p), -fle(c2, z, c2)])
                                            E.S.add_clause([-o, -r(K - 1, c2), -B(c2, p), -yle(c2, z)])
                            bad.append(o)
                        else:
                            o = E.v('a1sel', p, c, u); E.iff_and(o, [r(K - 1, c), f(p, c, p), f(p, u, c), B(c, p), na]); bad.append(o)
            if not bad: E.S.delete(); return None
            if 'rowtypes' in sys.argv:
                for x in range(n):
                    if rk[x] != K - 1: continue
                    for g in range(n):
                        if le[x][g] and g != x and g != m: E.S.add_clause([-r(K - 1, x), -A(x, g)])
                    for v in range(n):
                        if le[x][v] and v != x and not le[m][v]: E.S.add_clause([-r(K - 1, x), -A(x, x), -fle(x, v, v)])
        elif claim == 'a1cert':                        # §34.3z¹⁹⁹: hypotheses (as minhyp) + some A1-shape configuration (p ⋖ c, F(p,c) = p,
            if 'icok' not in sys.argv: E.S.add_clause([-ic(m)])   # c of rank K − 1 in R_{K−1}) with a fibre column u (F(p,u) = c, m ≰ u)
            sels = []                                             # and no A1Cert anywhere
            for c in range(n):
                if rk[c] != K - 1: continue
                for p in L.covers_dn[c]:
                    for u in range(n):
                        if not (le[c][u] and u != c and not le[m][u]): continue
                        base = [r(K - 1, c), f(p, c, p), f(p, u, c)]
                        if 'genuine' in sys.argv:            # the A1 residue: p = b(c) and c non-ascending (a(c) ≱ c)
                            na = E.v('nonasc', c)
                            E.iff_or(na, [A(c, g) for g in range(n) if not le[c][g]])
                            o = E.v('a1sel', p, c, u); E.iff_and(o, base + [B(c, p), na]); sels.append(o)
                        else:
                            o = E.v('a1sel', p, c, u); E.iff_and(o, base); sels.append(o)
                        for z in range(n):
                            if not (le[c][z] and z != c and le[z][u]): continue
                            nb = [-l for l in base]
                            E.S.add_clause(nb + [-fle(c, z, c)]); E.S.add_clause(nb + [-yle(c, z)])
                            E.S.add_clause(nb + [-fle(c, z, z)] + [f(p, e, p) for e in range(n) if le[c][e] and e != c and le[e][z]])
            if not sels: E.S.delete(); return None
            bad.extend(sels)
            if 'rowtypes' in sys.argv:                   # impose the ¬UpCell row types (noUpCell_rowTypes) on the height-k rows
                for x in range(n):
                    if rk[x] != K - 1: continue
                    for g in range(n):
                        if le[x][g] and g != x and g != m: E.S.add_clause([-r(K - 1, x), -A(x, g)])
                    for v in range(n):
                        if le[x][v] and v != x and not le[m][v]: E.S.add_clause([-r(K - 1, x), -A(x, x), -fle(x, v, v)])
        elif claim == 'pajump':                        # §34.3z¹⁹⁵: hypotheses (as minhyp) + the pure A-chain a^i(⊥), i ≤ K − 1, reaches rank K
            if 'icok' not in sys.argv: E.S.add_clause([-ic(m)])
            Sc = lambda i, g: E.v('chain', i, g)
            for g in range(n): E.S.add_clause([Sc(0, g)] if g == L.bot else [-Sc(0, g)])
            for i in range(K - 1):
                for g in range(n):
                    lits = []
                    for g2 in range(n):
                        o = E.v('chainstep', i, g2, g); E.iff_and(o, [Sc(i, g2), A(g2, g)]); lits.append(o)
                    E.iff_or(Sc(i + 1, g), lits)
            for i in range(K):
                for g in range(n):
                    if rk[g] == K: bad.append(Sc(i, g))
            if not bad: E.S.delete(); return None
        elif claim == 'rowlt2':                        # §34.3z²⁰⁶ (k = 1 only): hypotheses (as minhyp), y = y*, w = F(m, y*) ≱ m, x the rank-1
            if K != 2: E.S.delete(); return None           # element of the ⊥-descent v ↦ F(⊥, v) from w (chain positions P(i, v)),
            if 'icok' not in sys.argv: E.S.add_clause([-ic(m)])   # and no LT pair (x, v) on row x
            bot_ = rk.index(0); sels = []
            if 'abot' in sys.argv: E.S.add_clause([A(bot_, bot_)])
            for w_ in range(n):
                if le[m][w_]: continue
                y_ = jn[m][w_]
                ow = E.v('r2w', w_)
                E.S.add_clause([-ow, f(m, y_, w_)])
                for z in range(n):
                    if le[z][y_]: continue
                    for g in range(n):
                        if le[z][jn[m][g]]: E.S.add_clause([-ow, -f(m, z, g)])
                P = lambda i, v: E.v('r2P', w_, i, v)
                E.S.add_clause([-ow, P(0, w_)])
                for i in range(n):
                    for v in range(n):
                        for u in range(n): E.S.add_clause([-P(i, v), -f(bot_, v, u), P(i + 1, u)])
                        for u in range(v + 1, n): E.S.add_clause([-P(i, v), -P(i, u)])   # at most one per position: P is the chain
                for x in range(n):
                    if rk[x] != 1 or not le[x][w_]: continue
                    o = E.v('r2sel', w_, x); sels.append(o)
                    E.S.add_clause([-o, ow]); E.S.add_clause([-o] + [P(i, x) for i in range(n)])
                    for v in range(n):
                        if le[x][v] and v != x and not le[m][v]:
                            E.S.add_clause([-o, -r(1, x), -fle(x, v, v), -fle(bot_, v, x)])
            if not sels: E.S.delete(); return None
            bad.extend(sels)
        elif claim in ('orbitlt', 'rowlt'):                       # §34.3z²⁰⁶ (k = 1 only): hypotheses (as minhyp), y = y* (the greatest post-fixed point of
            if K != 2: E.S.delete(); return None           # y ↦ m ⊔ F(m, y)), w = F(m, y*) ≱ m, x = F(⊥, w) ≠ w of rank 1, and no LT pair (x, v)
            if 'icok' not in sys.argv: E.S.add_clause([-ic(m)])   # on the row-x orbit v ↦ F(x, v) from w (encoded as a closed set)
            bot_ = rk.index(0); sels = []
            if 'abot' in sys.argv: E.S.add_clause([A(bot_, bot_)])
            for w_ in range(n):
                if le[m][w_]: continue
                y_ = jn[m][w_]
                for x in range(n):
                    if rk[x] != 1 or x == w_ or not le[x][w_]: continue
                    o = E.v('olsel', w_, x); sels.append(o)
                    E.S.add_clause([-o, f(m, y_, w_)]); E.S.add_clause([-o, f(bot_, w_, x)])
                    for z in range(n):                     # y is the greatest post-fixed point
                        if le[z][y_]: continue
                        for g in range(n):
                            if le[z][jn[m][g]]: E.S.add_clause([-o, -f(m, z, g)])
                    orb = lambda v: E.v('orb', w_, x, v)
                    E.S.add_clause([-o, orb(w_)])
                    for v in range(n):
                        if claim == 'orbitlt':
                            for u in range(n): E.S.add_clause([-orb(v), -f(x, v, u), orb(u)])
                        if le[x][v] and v != x and not le[m][v]:   # 'rowlt': no LT pair on row x at all
                            E.S.add_clause([-orb(v) if claim == 'orbitlt' else -o, -r(1, x), -fle(x, v, v), -fle(bot_, v, x)])
            if not sels: E.S.delete(); return None
            bad.extend(sels)
        elif claim == 'desclt':                        # §34.3z²⁰⁶ (k = 1 only): hypotheses (as minhyp) and a column fixed point y = m ⊔ F(m, y)
            if K != 2: E.S.delete(); return None           # with w = F(m, y) ≱ m whose bottom-row value x = F(⊥, w) ≠ w has rank 1
            if 'icok' not in sys.argv: E.S.add_clause([-ic(m)])   # but F(x, w) ≰ w (DescLT at v = w; with 'parm': x ∥ m only)
            bot_ = rk.index(0); sels = []
            if 'abot' in sys.argv: E.S.add_clause([A(bot_, bot_)])   # a(⊥) = ⊥ (forced by uniqueness at k = 1)
            for w_ in range(n):
                if le[m][w_]: continue
                y_ = jn[m][w_]
                for x in range(n):
                    if rk[x] != 1 or x == w_ or not le[x][w_]: continue
                    if 'parm' in sys.argv and le[x][m]: continue
                    o = E.v('dlsel', w_, x); sels.append(o)
                    for lit in (f(m, y_, w_), f(bot_, w_, x), -fle(x, w_, w_)): E.S.add_clause([-o, lit])
            if not sels: E.S.delete(); return None
            bad.extend(sels)
        elif claim == 'lt':                            # §34.3z²⁰⁵ (k = 1 only): hypotheses (as minhyp) and no LT pair: no x ∈ R_1 of rank 1 and
            if K != 2: E.S.delete(); return None
            if 'abot' in sys.argv: E.S.add_clause([A(rk.index(0), rk.index(0))])           # v ≱ m with x < v, F(x, v) ≤ v, F(⊥, v) ≤ x (Lean `row_cell_of_bot_le_one`
            o = E.v('true'); E.S.add_clause([o]); bad.append(o)   # turns an LT pair into a cell of row x in (x, v])
            if 'icok' not in sys.argv: E.S.add_clause([-ic(m)])
            bot_ = rk.index(0)
            for x in range(n):
                if rk[x] != 1: continue
                for v in range(n):
                    if le[x][v] and v != x and not le[m][v]: E.S.add_clause([-r(1, x), -fle(x, v, v), -fle(bot_, v, x)])
        elif claim == 'minhyp':                        # §34.3z¹⁹²: a model of the hypotheses only (¬IC(m); with nofeeder / notightK1 / notop
            o = E.v('true'); E.S.add_clause([o]); bad.append(o)   #  these are the MinUpCell hypotheses); 'icok' drops ¬IC(m)
            if 'icok' not in sys.argv: E.S.add_clause([-ic(m)])
        elif claim in ('stabletop', 'pairjump'):       # §34.3z¹⁸⁹ per-configuration fibre-join lemmas (see docstring)
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
        elif claim in ('bonly', 'topgoal', 'backreach'):   # §34.3z²²¹: BOnlyGoodChild at the seeded root, exact (see docstring of bonly_check)
            fis = []
            for p in feeders: o = E.v('fi', p); E.iff_and(o, [low[p], B(m, p)]); fis.append(o)
            if 'bare' not in sys.argv and 'nofi' not in sys.argv: E.S.add_clause(fis)        # 'bare' drops both; 'nofi' the feeder
            if 'bare' not in sys.argv and 'icok' not in sys.argv: E.S.add_clause([-ic(m)])   # 'icok' drops ¬IC(m)
            k = K - 1; bot_ = rk.index(0)
            if k < 2: E.S.delete(); return None
            Y = lambda yv: E.v('ystar', yv)                # y* = greatest post-fixed point of u ↦ m ⊔ F(m, u)
            E.S.add_clause([Y(yv) for yv in range(n) if le[m][yv]])
            for a_, b_ in itertools.combinations(range(n), 2): E.S.add_clause([-Y(a_), -Y(b_)])
            for yv in range(n):
                if not le[m][yv]: E.S.add_clause([-Y(yv)]); continue
                for g in range(n):
                    if jn[m][g] != yv: E.S.add_clause([-Y(yv), -f(m, yv, g)])
                for z in range(n):
                    if le[z][yv]: continue
                    for g in range(n):
                        if le[z][jn[m][g]]: E.S.add_clause([-Y(yv), -f(m, z, g)])
            node = lambda x: 1 <= rk[x] <= k
            if 'atomroot' in sys.argv or claim == 'backreach':   # roots: every atom of R_1 (no descent)
                Root = lambda x: E.v('root', x)
                for x in range(n):
                    if rk[x] == 1: E.iff_and(Root(x), [r(1, x)])
                    else: E.S.add_clause([-Root(x)])
            else:
                D = next((int(a[5:]) for a in sys.argv if a.startswith('dmul=')), 4) * n     # descent horizon ('dmul=4' matches bonly_check)
                S = lambda i, a_, e_, bb: E.v('dS', i, a_, e_, bb)   # forward-forced; soundness via at-most-one root below   # descent state (row, column, B-step taken)
                for rv in range(n):
                    for yv in range(n):
                        for ev in range(n): E.S.add_clause([-B(m, rv), -Y(yv), -f(m, yv, ev), S(0, rv, ev, 0)])
                stop = collections.defaultdict(list)           # (r, z) → derivation literals (with a B-step)
                def rge(a_, e_):                               # r ≤ F(r, e)
                    k_ = ('rge', a_, e_)
                    if k_ not in E.vars: o = E.v(*k_); E.iff_or(o, [f(a_, e_, t) for t in range(n) if le[a_][t]])
                    return E.vars[k_]
                def stp(a_, e_):                               # F(r, e) ≤ r or e ≤ F(r, e)
                    k_ = ('stp', a_, e_)
                    if k_ not in E.vars: o = E.v(*k_); E.iff_or(o, [fle(a_, e_, a_), yle(a_, e_)])
                    return E.vars[k_]
                Tq = lambda i, q, e_: E.v('dT', i, q, e_)      # after a B-step: row q = b(r), column e (before F(q, e))
                for i in range(D):
                    for a_ in range(n):
                        for e_ in range(n):
                            for bb in (0, 1):
                                st_ = S(i, a_, e_, bb)
                                if bb: o = E.v('dstop1', i, a_, e_); E.iff_and(o, [st_, stp(a_, e_)]); stop[(a_, e_)].append(o)
                                else: E.S.add_clause([-st_, -stp(a_, e_)])   # a stop with no B-step: bonly_check returns False
                                for t in range(n):
                                    if le[a_][t] and not le[t][a_] and not le[e_][t]: E.S.add_clause([-st_, -f(a_, e_, t), S(i + 1, a_, t, bb)])
                                for q in range(n): E.S.add_clause([-st_, stp(a_, e_), rge(a_, e_), -B(a_, q), Tq(i, q, e_)])
                    for q in range(n):
                        for e_ in range(n):
                            tq = Tq(i, q, e_)
                            o = E.v('dstop2', i, q, e_); E.iff_and(o, [tq, fle(q, e_, q)]); stop[(q, e_)].append(o)
                            for e2 in range(n):
                                if not le[e2][q]: E.S.add_clause([-tq, -f(q, e_, e2), S(i + 1, q, e2, 1)])
                for a_ in range(n):                            # past the horizon: bonly_check returns False (exact for dmul=4)
                    for e_ in range(n):
                        for bb in (0, 1): E.S.add_clause([-S(D, a_, e_, bb)])
                node = lambda x: 1 <= rk[x] <= k
                rootd = collections.defaultdict(list)
                for (a_, z_), lits in stop.items():
                    sv = E.v('stopv', a_, z_); E.iff_or(sv, lits)
                    for t in range(n):
                        upper = le[z_][t] and not le[t][a_]
                        if upper and node(a_):
                            o = E.v('rootA', a_, z_, t); E.iff_and(o, [sv, f(a_, z_, t), r(rk[a_], a_)]); rootd[a_].append(o)
                            o2 = E.v('rootB', a_, z_, t); E.iff_and(o2, [sv, f(a_, z_, t), -r(rk[a_], a_)]); rootd[z_].append(o2)
                        else:
                            o = E.v('rootC', a_, z_, t); E.iff_and(o, [sv, f(a_, z_, t)]); rootd[z_].append(o)
                Root = lambda x: E.v('root', x)
                for a_, b_ in itertools.combinations(range(n), 2): E.S.add_clause([-Root(a_), -Root(b_)])
                for x in range(n):
                    E.iff_or(Root(x), rootd.get(x, []))
                    if not node(x): E.S.add_clause([-Root(x)])
                    else: E.S.add_clause([-Root(x), r(rk[x], x)])
            newv = lambda y_, j: [r(j, y_), -r(j - 1, y_)] if rk[y_] == j else None
            Be, Ae = {}, {}
            for x in range(n):
                if not node(x): continue
                j = rk[x]
                for y_ in range(n):
                    if not (le[x][y_] and y_ != x and rk[y_] == j + 1): continue
                    fib = [f(x, vv, y_) for vv in range(n) if le[y_][vv] and vv != y_ and not le[m][vv]]
                    if fib:
                        fb = E.v('fibne', x, y_); E.iff_or(fb, fib)
                        o = E.v('Bedge', x, y_); E.iff_and(o, [r(j, x), r(j + 1, y_), -r(j, y_), f(x, y_, x), fb]); Be[(x, y_)] = o
                    if not le[m][y_]:
                        o = E.v('Aedge', x, y_); E.iff_and(o, [r(j, x), yle(x, y_), r(j + 1, y_), -r(j, y_)]); Ae[(x, y_)] = o
            Edge = {}
            for key in set(Be) | set(Ae):
                o = E.v('edge', *key); E.iff_or(o, [l for l in (Be.get(key), Ae.get(key)) if l]); Edge[key] = o
            if claim == 'topgoal':                         # a set C ∋ root closed under the edges with no stage-k UpAt top
                Cl = lambda x: E.v('closed', x)
                for x in range(n): E.S.add_clause([-Root(x), Cl(x)])
                for (x, y_), ed in Edge.items(): E.S.add_clause([-Cl(x), -ed, Cl(y_)])
                if 'joinedge' in sys.argv:                 # join-sibling edges x → s: h(s) = h(x), s ∈ R_j, x ∨ s ∈ R_j
                    for x in range(n):
                        if not node(x): continue
                        j = rk[x]
                        for y_ in range(n):
                            if y_ != x and rk[y_] == j: E.S.add_clause([-Cl(x), -r(j, x), -r(j, y_), -r(j, jn[x][y_]), Cl(y_)])
                if 'liftedge' in sys.argv:                 # lift edges x → s: h(s) ≤ h(x), s ∈ R_{h(s)}, x ∨ s ∈ R_{h(s)} (non-tight)
                    for x in range(n):
                        if not node(x): continue
                        for y_ in range(n):
                            if y_ != x and node(y_) and rk[y_] <= rk[x]: E.S.add_clause([-(Root(x) if 'rootlift' in sys.argv else Cl(x)), -r(rk[x], x), -r(rk[y_], y_), -r(rk[y_], jn[x][y_]), Cl(y_)])
                for x in range(n):
                    if rk[x] != k or 'vacuity' in sys.argv: continue          # 'vacuity': count models of the hypotheses
                    for z in range(n):
                        if le[x][z] and z != x and not le[m][z]: E.S.add_clause([-Cl(x), -fle(x, z, x)]); E.S.add_clause([-Cl(x), -yle(x, z)])
                o = E.v('tgbad'); E.S.add_clause([o]); bad.append(o)
            if claim == 'backreach':                       # §34.3z²²²: a stage-k UpAt top not backward-reachable from R_1's atoms
                Bk = lambda x: E.v('back', x)
                for (x, y_), ed in Edge.items(): E.S.add_clause([-Bk(y_), -ed, Bk(x)])
                for x in range(n):
                    if rk[x] == 1: E.S.add_clause([-Bk(x), -r(1, x)])
                for x in range(n):
                    if rk[x] != k: continue
                    ups = []
                    for z in range(n):
                        if le[x][z] and z != x and not le[m][z]: ups += [fle(x, z, x), yle(x, z)]
                    if not ups: continue
                    o = E.v('backsel', x); bad.append(o)
                    E.S.add_clause([-o, Bk(x)]); E.S.add_clause([-o, r(k, x)]); E.S.add_clause([-o] + ups)
            Rch = lambda x: E.v('reach', x)
            for x in range(n):
                sup = [Root(x)]
                for (y_, x2), ed in Edge.items():
                    if x2 == x: o = E.v('rsup', y_, x); E.iff_and(o, [Rch(y_), ed]); sup.append(o)
                E.S.add_clause([-Rch(x)] + sup)
            Bd = lambda x: E.v('bad', 'g', x)
            for x in range(n):
                if not node(x) and rk[x] != k: continue
                if rk[x] == k:
                    for z in range(n):
                        if le[x][z] and z != x and not le[m][z]: E.S.add_clause([-Bd(x), -fle(x, z, x)]); E.S.add_clause([-Bd(x), -yle(x, z)])
                elif rk[x] < k:
                    for (x2, s2), ed in Edge.items():
                        if x2 == x: E.S.add_clause([-Bd(x), -ed, Bd(s2)])
            for x in range(n):
                if not (1 <= rk[x] < k): continue
                kidsB = [ed for (x2, _), ed in Be.items() if x2 == x]
                if not kidsB: continue
                o = E.v('bonlysel', x); bad.append(o)
                E.S.add_clause([-o, Rch(x)]); E.S.add_clause([-o] + kidsB)
                for (x2, y_), ed in Ae.items():
                    if x2 == x: E.S.add_clause([-o, -ed])
                for (x2, y_), ed in Be.items():
                    if x2 == x and 'vacuity' not in sys.argv: E.S.add_clause([-o, -ed, Bd(y_)])
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
    F = E.decode()
    if claim in ('bonly', 'topgoal') and 'bdebug' in sys.argv:
        mdl = set(x for x in E.S.get_model() if x > 0)
        global BDBG; BDBG = sorted(k_ for k_, v_ in E.vars.items() if v_ in mdl and k_[0] in ('root', 'reach', 'bonlysel', 'stopv', 'ystar', 'Bedge', 'Aedge'))
    E.S.delete()
    st = stages(L, F); inR = lambda z, j: st[z] is not None and st[z] <= j - s
    assert inR(m, K) and not inR(m, K - 1) and ('notop' in sys.argv or not inR(L.top, K + 1))
    assert 'alltight' not in sys.argv or all(rk[z] <= j for j in range(1, K - 1) for z in range(n) if inR(z, j))
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
        def pachain():
            c_ = L.bot
            for i in range(K):
                if rk[c_] == K: return True
                c_ = a_of(L, F, c_)
            return False
        def a1nocert():
            has = 'genuine' not in sys.argv and False
            gen = lambda p_, c_: ('genuine' not in sys.argv) or (b_of(L, F, c_) == p_ and not le[c_][a_of(L, F, c_)])
            for c in range(n):
                if rk[c] != K - 1 or not inR(c, K - 1): continue
                for p in L.covers_dn[c]:
                    if F[p][c] != p: continue
                    for u in range(n):
                        if not (le[c][u] and u != c and not le[m][u] and F[p][u] == c): continue
                        if gen(p, c): has = True
                        for z in range(n):
                            if not (le[c][z] and z != c and le[z][u]): continue
                            if le[F[c][z]][c] or le[z][F[c][z]]: return False
                            if le[F[c][z]][z] and not any(le[c][e] and e != c and le[e][z] and F[p][e] == p for e in range(n)): return False
            return has
        def rowtypes_ok():
            if 'rowtypes' not in sys.argv: return True
            for x in range(n):
                if rk[x] != K - 1 or not inR(x, K - 1): continue
                ax = a_of(L, F, x)
                if le[x][ax] and ax not in (x, m): return False
                if ax == x and any(le[x][v] and v != x and not le[m][v] and le[F[x][v]][v] for v in range(n)): return False
            return True
        def selfnocell():
            for c in range(n):
                if rk[c] != K - 1 or not inR(c, K - 1) or le[c][a_of(L, F, c)]: continue
                p_ = b_of(L, F, c)
                if p_ not in L.covers_dn[c]: continue
                if any(le[c][u] and u != c and not le[m][u] and F[p_][u] == c for u in range(n)) and \
                   not any(le[c][z] and z != c and not le[m][z] and (le[F[c][z]][c] or le[z][F[c][z]]) for z in range(n)): return True
            return False
        def sibnocell():
            for c in range(n):
                if rk[c] != K - 1 or not inR(c, K - 1) or le[c][a_of(L, F, c)]: continue
                p_ = b_of(L, F, c)
                if p_ not in L.covers_dn[c] or not any(le[c][u] and u != c and not le[m][u] and F[p_][u] == c for u in range(n)): continue
                tops = [c2 for c2 in range(n) if rk[c2] == K - 1 and inR(c2, K - 1) and b_of(L, F, c2) == p_ and p_ in L.covers_dn[c2]]
                if not any(le[c2][z] and z != c2 and not le[m][z] and (le[F[c2][z]][c2] or le[z][F[c2][z]]) for c2 in tops for z in range(n)): return True
            return False
        def abovepnocell():
            for c in range(n):
                if rk[c] != K - 1 or not inR(c, K - 1) or le[c][a_of(L, F, c)]: continue
                p_ = b_of(L, F, c)
                if p_ not in L.covers_dn[c] or not any(le[c][u] and u != c and not le[m][u] and F[p_][u] == c for u in range(n)): continue
                tops = [c2 for c2 in range(n) if rk[c2] == K - 1 and inR(c2, K - 1) and le[p_][c2]]
                if not any(le[c2][z] and z != c2 and not le[m][z] and (le[F[c2][z]][c2] or le[z][F[c2][z]]) for c2 in tops for z in range(n)): return True
            return False
        def rowlt2viol():
            bot_ = rk.index(0); ys_ = ystar(L, F, m); w_ = F[m][ys_]
            if le[m][w_]: return False
            ch = [w_]
            while F[bot_][ch[-1]] not in ch: ch.append(F[bot_][ch[-1]])
            xs = [x for x in ch if rk[x] == 1]
            return any(not any(inR(x, 1) and le[x][v] and v != x and not le[m][v] and le[F[x][v]][v] and le[F[bot_][v]][x] for v in range(n)) for x in xs)
        def orbitviol(row=False):
            bot_ = rk.index(0); ys_ = ystar(L, F, m); w_ = F[m][ys_]; x = F[bot_][w_]
            if le[m][w_] or rk[x] != 1 or x == w_: return False
            orb = [w_]
            while F[x][orb[-1]] not in orb: orb.append(F[x][orb[-1]])
            if row: orb = list(range(n))
            return not any(inR(x, 1) and le[x][v] and v != x and not le[m][v] and le[F[x][v]][v] and le[F[bot_][v]][x] for v in orb)
        def dominantviol():
            if a1nocert_any() is False: return False
            for c in range(n):
                if rk[c] != K - 1 or not inR(c, K - 1): continue
                p_ = b_of(L, F, c); y = a_of(L, F, c)
                if p_ not in L.covers_dn[c] or rk[y] != K - 1 or not inR(y, K - 1) or le[c][y] or le[y][c]: continue
                for u in range(n):
                    if le[c][u] and u != c and not le[m][u] and F[p_][u] == c and F[c][u] == L.join[c][y]:
                        ay = a_of(L, F, y)
                        forb = (le[y][ay] and ay not in (y, m)) or (ay == y and any(le[y][v] and v != y and not le[m][v] and le[F[y][v]][v] for v in range(n)))
                        if not forb: return True
            return False
        def a1nocert_any():
            for c in range(n):
                if rk[c] != K - 1 or not inR(c, K - 1): continue
                for p_ in L.covers_dn[c]:
                    if F[p_][c] != p_: continue
                    for u in range(n):
                        if not (le[c][u] and u != c and not le[m][u] and F[p_][u] == c): continue
                        for z in range(n):
                            if not (le[c][z] and z != c and le[z][u]): continue
                            if le[F[c][z]][c] or le[z][F[c][z]]: return False
                            if le[F[c][z]][z] and not any(le[c][e] and e != c and le[e][z] and F[p_][e] == p_ for e in range(n)): return False
            return True
        viol = {'dominant': not ic_py(L, F, m) and dominantviol(), 'a1gen': ((abovepnocell() if 'abovepnocell' in sys.argv else sibnocell() if 'sibnocell' in sys.argv else selfnocell()) and rowtypes_ok()) if 'selfnocell' in sys.argv else True, 'a1cert': (True if 'icok' in sys.argv else not ic_py(L, F, m)) and a1nocert() and rowtypes_ok(), 'pajump': (True if 'icok' in sys.argv else not ic_py(L, F, m)) and pachain(), 'minhyp': True, 'bonly': (bonly_check(L, F, m) if claim == 'bonly' else False), 'topgoal': (bonly_check(L, F, m) if claim == 'topgoal' else False), 'backreach': (bonly_check(L, F, m) if claim == 'backreach' else False), 'orbitlt': ('icok' in sys.argv or not ic_py(L, F, m)) and orbitviol(), 'rowlt': ('icok' in sys.argv or not ic_py(L, F, m)) and orbitviol(True), 'rowlt2': ('icok' in sys.argv or not ic_py(L, F, m)) and rowlt2viol(), 'desclt': ('icok' in sys.argv or not ic_py(L, F, m)) and any(not le[m][w_] and F[m][L.join[m][w_]] == w_ and rk[F[rk.index(0)][w_]] == 1 and F[rk.index(0)][w_] != w_ and not le[F[F[rk.index(0)][w_]][w_]][w_] for w_ in range(n)), 'lt': ('icok' in sys.argv or not ic_py(L, F, m)) and not any(inR(x, 1) and rk[x] == 1 and le[x][v] and v != x and not le[m][v] and le[F[x][v]][v] and le[F[rk.index(0)][v]][x] for x in range(n) for v in range(n)), 'stabletop': (bm in low) and not ic_py(L, F, m) and fjviol('stable'),
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
    if not viol and claim in ('bonly', 'topgoal') and 'bdebug' in sys.argv:
        import json; json.dump(dict(sets=L.S, F=F, m=m, dbg=[list(map(str, k_)) for k_ in BDBG]), open(sys.argv[-1] if sys.argv[-1].endswith('.json') else 'bdebug.json', 'w')); raise SystemExit('bdebug: SAT/Python mismatch dumped')
    assert viol
    return F

RMIN = next((int(a[5:]) for a in sys.argv if a.startswith('rmin=')), 1)

if __name__ == '__main__':
    claim = sys.argv[1]; ahead = 'ahead' in sys.argv; C = collections.Counter(); best = None
    if claim == 'topgoal': sys.argv.append('TOPGOAL')
    if claim == 'backreach': sys.argv.append('BACKREACH')
    for L in lattices([a for a in sys.argv[2:] if a not in ('ahead', 'notop', 'multi', 'post', 'strictpre', 'nopostlayer', 'k2', 'nofi', 'icok', 'notightK1', 'nofeeder', 'needcfg', 'genuine', 'rowtypes', 'selfnocell', 'sibnocell', 'abovepnocell', 'abot', 'parm', 'vacuity', 'bdebug', 'alltight', 'joinedge', 'liftedge', 'rootlift', 'atomroot', 'bare', 'TOPGOAL', 'BACKREACH') and not a.endswith('.json') and not a.startswith('rmin=') and not a.startswith('dmul=')]):
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
        import json; json.dump(dict(sets=best[0].S, F=best[1][1], m=best[1][0]), open(f"single_claim_{claim}{'_ahead' if ahead else ''}{''.join('_' + f for f in ('notop', 'multi', 'post', 'strictpre', 'nopostlayer', 'nofi', 'icok', 'notightK1', 'nofeeder', 'needcfg', 'genuine', 'rowtypes', 'selfnocell', 'sibnocell', 'abovepnocell', 'abot', 'parm', 'vacuity', 'alltight', 'joinedge', 'liftedge', 'rootlift', 'atomroot', 'bare') if f in sys.argv)}{f'_rmin{RMIN}' if RMIN > 1 else ''}_min{best[0].n}.json", 'w'))
