"""Is the feeder the top of a descent chain? (log §34.3z²⁵²)
SingletonLower configuration at k (without its conclusion): ⊤ ∉ R_{k+2}; R_k, R_{k+1} tight; m the unique height-(k+1)
element of R_{k+1}; m ∈ R_{k+1} \\ R_k; a feeder m' ∈ R_k, h(m') = k, m' < m, F(m', m) ≤ m'.
  feed  — no p ∈ R_{k−1} of height k − 1 with p ≤ m', p ≤ F(p, m') and m' on the row-p descent from ⊤ (SAT = feeder is not a chain top)
  any   — no descent chain at level k − 1 at all
  feedlow / feedfix — no such chain with F(p, m') = p / F(p, m') = m'
  vac   — configuration only
  python3 sl_feed.py MODE k (sweep N MAX | closure K M SEED CNT) [r1nt]
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from rstages import stages
MODE = sys.argv[1]; k = int(sys.argv[2]); R1NT = 'r1nt' in sys.argv; args = [a for a in sys.argv[3:] if a != 'r1nt']
C = collections.Counter(); best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; top = L.top; NO = L.height + 1
    for m in range(n):
        if h[m] != k + 1 or L.height <= k + 1: continue
        for mp in range(n):
            if h[mp] != k or not le[mp][m]: continue
            E = Enc(L, k + 2); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
            add([-r(k + 2, top)]); add([r(k + 1, m)]); add([-r(k, m)]); add([r(k, mp)]); add([fle(mp, m, mp)])
            for z in range(n):
                if h[z] > k: add([-r(k, z)])
                if h[z] > k + 1: add([-r(k + 1, z)])
                if h[z] == k + 1 and z != m: add([-r(k + 1, z)])
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
                ok = inR(m, k + 1) and not inR(m, k) and inR(mp, k) and le[F[mp][m]][mp] and not inR(top, k + 2)
                if MODE == 'feedm':
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
print(MODE, 'k', k, 'r1nt' if R1NT else '', dict(C), 'smallest', best[0] if best else None)
if best and MODE != 'vac': json.dump(best[1], open(f'slfeed_{MODE}_k{k}{"_r1nt" if R1NT else ""}_min{best[0]}.json', 'w'))
