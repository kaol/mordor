"""Is the feeder the top of a descent chain? (log §34.3z²⁵²)
SingletonLower configuration at k (without its conclusion): ⊤ ∉ R_{k+2}; R_k, R_{k+1} tight; m the unique height-(k+1)
element of R_{k+1}; m ∈ R_{k+1} \\ R_k; a feeder m' ∈ R_k, h(m') = k, m' < m, F(m', m) ≤ m'.
  feed  — no p ∈ R_{k−1} of height k − 1 with p ≤ m', p ≤ F(p, m') and m' on the row-p descent from ⊤ (SAT = feeder is not a chain top)
  any   — no descent chain at level k − 1 at all
  bgood   — B-route with q = b(m') not good (q ≰ a(q), row-q descent misses q)
  bqu     — B-route with a drop column u of the row-q descent outside R_{k+1}
  bq / bqm — B-route (q = b(m') ∈ R_{k−1}) with m' / m off the row-q descent from ⊤
  asc1 / asc2 — pure A-route with b(m') ≠ m' / with the column-m' ascent from ⊥ entering m' from an x ∉ R_{k−1} or of height ≠ k − 1
  U       — pure A-route with no x ≤ m' in R_{k−1} of height k − 1 having an upper cell m' ≤ F(x, m')
  aout    — pure A-route (b(m') ∉ R_{k−1}) with every generator x (a(x) = m', x ∈ R_{k−1}) outside ↓m'
  bm / bmh — b(m') ∉ R_{k−1} / h(b(m')) ≠ k − 1
  gen     — no x ∈ R_{k−1} of height k − 1 below m' with a(x) = m' or F(x, m') = x
  lowdesc — some such x with F(x, m') = x has m' off its row descent from ⊤
  feedlow / feedfix — no such chain with F(p, m') = p / F(p, m') = m'
  vac   — configuration only
  python3 sl_feed.py MODE k (sweep N MAX | closure K M SEED CNT) [r1nt]
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from rstages import stages
FL = {a for a in sys.argv[3:] if a in ('r1nt', 'nouniq', 'notop', 'nofeed', 'no3', 'nonew', 'no2')}   # drop: uniqueness / ⊤ ∉ R_{k+2} / F(m', m) ≤ m' / R_{k+1} tight / m ∉ R_k
MODE = sys.argv[1]; k = int(sys.argv[2]); R1NT = 'r1nt' in FL; args = [a for a in sys.argv[3:] if a not in FL]
MODES = {'feed', 'any', 'vac', 'feedlow', 'feedfix', 'feedm', 'uniq', 'uniqvac', 'gen', 'lowdesc', 'bm', 'bmh', 'aout', 'U', 'asc1', 'asc2', 'ascS', 'bq', 'bqm', 'bqu', 'bgood'}
if MODE not in MODES: raise SystemExit('unknown mode ' + MODE)
C = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; top = L.top; NO = L.height + 1; bot_ = h.index(0)
    for m in range(n):
        if h[m] != k + 1 or L.height <= k + 1: continue
        for mp in range(n):
            if h[mp] != k or not le[mp][m]: continue
            E = Enc(L, k + 2); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
            if 'notop' not in FL: add([-r(k + 2, top)])
            add([r(k + 1, m)]); add([r(k, mp)])
            if 'nonew' not in FL: add([-r(k, m)])
            if 'nofeed' not in FL: add([fle(mp, m, mp)])
            for z in range(n):
                if h[z] > k and 'no2' not in FL: add([-r(k, z)])
                if h[z] > k + 1 and 'no3' not in FL: add([-r(k + 1, z)])
                if h[z] == k + 1 and z != m and 'nouniq' not in FL: add([-r(k + 1, z)])
            if R1NT: add([r(1, z) for z in range(n) if h[z] > 1])
            def descvars(p):
                D = lambda i, z: E.v('DD', p, i, z)
                if ('DD', p, 0, top) in E.vars: return D
                for z in range(n): add([D(0, z)] if z == top else [-D(0, z)])
                for i in range(NO):
                    for z in range(n):
                        lits = []
                        for v in range(n): o = E.v('DDs', p, i, v, z); E.iff_and(o, [D(i, v), f(p, v, z)]); lits.append(o)
                        E.iff_or(D(i + 1, z), lits)
                return D
            if MODE == 'bgood':                                 # B-route with q = b(m') not good (q ≰ a(q) and the row-q descent from ⊤ misses q)
                sel = []
                for q in range(n):
                    if not le[q][mp] or q == mp: continue
                    D = descvars(q); o = E.v('bg', q); sel.append(o)
                    add([-o, E.v('B', mp, q)]); add([-o, r(k - 1, q)])
                    for i in range(NO + 1): add([-o, -D(i, q)])
                    for g in range(n):
                        if le[q][g]: add([-o, -E.v('A', q, g)])
                add(sel)
            if MODE == 'bqu':                                   # B-route with a drop column u of the row-q descent (u ≥ m', u ≠ m', F(q, u) ≱ m') and u ∉ R_{k+1}
                sel = []
                for q in range(n):
                    if not le[q][mp] or q == mp: continue
                    D = descvars(q)
                    for u in range(n):
                        if not le[mp][u] or u == mp: continue
                        o = E.v('bqu', q, u); sel.append(o)
                        add([-o, E.v('B', mp, q)]); add([-o, r(k - 1, q)]); add([-o, -r(k + 1, u)])
                        add([-o] + [D(i, u) for i in range(NO + 1)])
                        for w in range(n):
                            if le[mp][w]: add([-o, -f(q, u, w)])
                add(sel)
            if MODE in ('bq', 'bqm'):                            # B-route: q = b(m') ∈ R_{k−1}; bq: m' not on the row-q descent; bqm: m not on it
                sel = []
                for q in range(n):
                    if not le[q][mp] or q == mp: continue
                    D = descvars(q); o = E.v('bq', q); sel.append(o)
                    add([-o, E.v('B', mp, q)]); add([-o, r(k - 1, q)])
                    for i in range(NO + 1): add([-o, -D(i, mp if MODE == 'bq' else m)])
                add(sel)
            if MODE in ('asc1', 'asc2', 'ascS'):                         # pure A-route; asc1: b(m') ≠ m'; asc2: the column-m' ascent from ⊥ enters m' from some x ∉ R_{k−1} or of height ≠ k − 1
                for g in range(n): add([-E.v('B', mp, g), -r(k - 1, g)])
                if MODE == 'asc1': add([-E.v('B', mp, mp)])
                elif MODE == 'ascS':                               # some ascent element strictly below m' outside R_{k−1}
                    Au = lambda i, z: E.v('Asc', i, z)
                    for z in range(n): add([Au(0, z)] if z == bot_ else [-Au(0, z)])
                    for i in range(NO):
                        for z in range(n):
                            ls = []
                            for v in range(n): o = E.v('Ascs', i, v, z); E.iff_and(o, [Au(i, v), f(v, mp, z)]); ls.append(o)
                            E.iff_or(Au(i + 1, z), ls)
                    sel = []
                    for i in range(NO + 1):
                        for x in range(n):
                            if x == mp or not le[x][mp]: continue
                            o = E.v('sx', i, x); add([-o, Au(i, x)]); add([-o, -r(k - 1, x)]); sel.append(o)
                    add(sel)
                else:
                    Au = lambda i, z: E.v('Asc', i, z)
                    for z in range(n): add([Au(0, z)] if z == bot_ else [-Au(0, z)])
                    for i in range(NO):
                        for z in range(n):
                            ls = []
                            for v in range(n): o = E.v('Ascs', i, v, z); E.iff_and(o, [Au(i, v), f(v, mp, z)]); ls.append(o)
                            E.iff_or(Au(i + 1, z), ls)
                    sel = []
                    for i in range(NO):
                        for x in range(n):
                            if x == mp or not le[x][mp]: continue
                            o = E.v('pen', i, x); add([-o, Au(i, x)]); add([-o, f(x, mp, mp)])
                            if h[x] == k - 1: add([-o, -r(k - 1, x)])
                            sel.append(o)
                    add(sel)
            if MODE == 'U':                                     # pure A-route and no x ≤ m' in R_{k−1} of height k−1 with m' ≤ F(x, m')
                for g in range(n): add([-E.v('B', mp, g), -r(k - 1, g)])
                for x in range(n):
                    if le[x][mp] and h[x] == k - 1: add([-r(k - 1, x), -yle(x, mp)])
            if MODE == 'aout':                                  # b(m') ∉ R_{k−1} (pure A-route) and no x ≤ m' in R_{k−1} with a(x) = m'
                for g in range(n): add([-E.v('B', mp, g), -r(k - 1, g)])
                for x in range(n):
                    if le[x][mp]: add([-r(k - 1, x), -E.v('A', x, mp)])
            if MODE in ('bm', 'bmh'):                            # bm: b(m') ∉ R_{k−1}; bmh: h(b(m')) ≠ k − 1
                for g in range(n):
                    if MODE == 'bm': add([-E.v('B', mp, g), -r(k - 1, g)])
                    elif h[g] == k - 1: add([-E.v('B', mp, g)])
            if MODE in ('gen', 'lowdesc'):                       # gen: no x ≤ m' in R_{k-1}, height k−1, with a(x) = m' or F(x, m') = x
                if MODE == 'gen':                                 # lowdesc: some such x with F(x, m') = x has m' off its descent
                    for x in range(n):
                        if h[x] != k - 1 or not le[x][mp]: continue
                        add([-r(k - 1, x), -E.v('A', x, mp)]); add([-r(k - 1, x), -f(x, mp, x)])
                else:
                    sel = []
                    for x in range(n):
                        if h[x] != k - 1 or not le[x][mp]: continue
                        D = descvars(x); o = E.v('ld', x); sel.append(o)
                        add([-o, r(k - 1, x)]); add([-o, f(x, mp, x)])
                        for i in range(NO + 1): add([-o, -D(i, mp)])
                    if not sel: E.S.delete(); continue
                    add(sel)
            if MODE == 'feedm':                                  # no p with a(p) = m', nor with F(p, m') = p, m on the row-p descent and F(p, m) = m'
                for p in range(n):
                    if h[p] != k - 1 or not le[p][mp]: continue
                    D = descvars(p)
                    add([-r(k - 1, p), -E.v('A', p, mp)])
                    E.iff_or(E.v('onm', p), [D(i, m) for i in range(NO + 1)])
                    add([-r(k - 1, p), -E.v('onm', p), -f(p, mp, p), -f(p, m, mp)])
            if MODE in ('feedlow', 'feedfix'):                 # restrict the chain to F(p, m') = p [feedlow] / F(p, m') = m' [feedfix]
                for p in range(n):
                    if h[p] != k - 1 or not le[p][mp]: continue
                    D = descvars(p)
                    E.iff_or(E.v('onc', p, mp), [D(i, mp) for i in range(NO + 1)])
                    add([-r(k - 1, p), -E.v('onc', p, mp), -f(p, mp, p if MODE == 'feedlow' else mp)])
            if MODE in ('feed', 'any'):
                for p in range(n):
                    if h[p] != k - 1: continue
                    D = descvars(p)
                    for c in range(n):
                        if h[c] != k or not le[p][c] or (MODE == 'feed' and c != mp): continue
                        pge = E.v('pge', p, c); E.iff_or(pge, [f(p, c, v) for v in range(n) if le[p][v]])
                        add([-r(k - 1, p), -r(k, c), -pge] + [-D(i, c) for i in range(1)] if False else [-r(k - 1, p), -r(k, c), -pge, -E.v('onc', p, c)])
                        E.iff_or(E.v('onc', p, c), [D(i, c) for i in range(NO + 1)])
            if E.S.solve():
                F = E.decode(); st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j
                def desc(p):
                    v = top; seen = []
                    while v not in seen: seen.append(v); v = F[p][v]
                    return seen
                ok = inR(m, k + 1) and ('nonew' in FL or not inR(m, k)) and inR(mp, k) and ('nofeed' in FL or le[F[mp][m]][mp]) and ('notop' in FL or not inR(top, k + 2))
                if MODE == 'bgood':
                    from rstages import b_of, a_of
                    q = b_of(L, F, mp)
                    ok = ok and q != mp and inR(q, k - 1) and q not in desc(q) and not le[q][a_of(L, F, q)]
                elif MODE == 'bqu':
                    from rstages import b_of
                    q = b_of(L, F, mp)
                    ok = ok and q != mp and inR(q, k - 1) and any(le[mp][u] and u != mp and not le[mp][F[q][u]] and not inR(u, k + 1) for u in desc(q))
                elif MODE in ('bq', 'bqm'):
                    from rstages import b_of
                    q = b_of(L, F, mp)
                    ok = ok and q != mp and inR(q, k - 1) and (mp if MODE == 'bq' else m) not in desc(q)
                elif MODE in ('asc1', 'asc2', 'ascS'):
                    from rstages import b_of
                    bm = b_of(L, F, mp)
                    if MODE == 'asc1': ok = ok and not inR(bm, k - 1) and bm != mp
                    elif MODE == 'ascS':
                        v = bot_; seq = [v]
                        while F[v][mp] != v: v = F[v][mp]; seq.append(v)
                        ok = ok and not inR(bm, k - 1) and any(x != mp and le[x][mp] and not inR(x, k - 1) for x in seq)
                    else:
                        v = bot_; seq = [v]
                        while F[v][mp] != v: v = F[v][mp]; seq.append(v)
                        pen = seq[seq.index(mp) - 1] if mp in seq else None
                        ok = ok and not inR(bm, k - 1) and pen is not None and not (h[pen] == k - 1 and inR(pen, k - 1))
                elif MODE == 'U':
                    from rstages import b_of
                    ok = ok and not inR(b_of(L, F, mp), k - 1) and not any(le[x][mp] and h[x] == k - 1 and inR(x, k - 1) and le[mp][F[x][mp]] for x in range(n))
                elif MODE == 'aout':
                    from rstages import a_of, b_of
                    ok = ok and not inR(b_of(L, F, mp), k - 1) and not any(le[x][mp] and inR(x, k - 1) and a_of(L, F, x) == mp for x in range(n))
                elif MODE in ('bm', 'bmh'):
                    from rstages import b_of
                    bm = b_of(L, F, mp)
                    ok = ok and (not inR(bm, k - 1) if MODE == 'bm' else h[bm] != k - 1)
                elif MODE == 'gen':
                    from rstages import a_of
                    ok = ok and not any(h[x] == k - 1 and inR(x, k - 1) and le[x][mp] and (a_of(L, F, x) == mp or F[x][mp] == x) for x in range(n))
                elif MODE == 'lowdesc':
                    ok = ok and any(h[x] == k - 1 and inR(x, k - 1) and le[x][mp] and F[x][mp] == x and mp not in desc(x) for x in range(n))
                elif MODE == 'feedm':
                    from rstages import a_of
                    ok = ok and not any(h[p] == k - 1 and inR(p, k - 1) and le[p][mp] and (a_of(L, F, p) == mp or (F[p][mp] == p and m in desc(p) and F[p][m] == mp)) for p in range(n))
                elif MODE in ('feedlow', 'feedfix'):
                    ok = ok and not any(h[p] == k - 1 and inR(p, k - 1) and le[p][mp] and mp in desc(p) and F[p][mp] == (p if MODE == 'feedlow' else mp) for p in range(n))
                elif MODE != 'vac':
                    ok = ok and not any(h[p] == k - 1 and inR(p, k - 1) and h[c] == k and inR(c, k) and le[p][c] and le[p][F[p][c]] and c in desc(p)
                                        for p in range(n) for c in range(n) if MODE == 'any' or c == mp)
                assert ok, 'SAT/Python mismatch'
                C['SAT'] += 1
                if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F, m=m, mp=mp))
            else: C['UNSAT'] += 1
            E.S.delete()
print(MODE, 'k', k, ' '.join(sorted(FL)), dict(C), 'smallest', best[0] if best else None)
if best and MODE != 'vac': json.dump(best[1], open(f'slfeed_{MODE}_k{k}{"".join("_" + x for x in sorted(FL))}_min{best[0]}.json', 'w'))
