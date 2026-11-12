"""Good elements and b-values (log §34.3z¹⁵⁷). z is *good* if z ∈ R_{h(z)} (entry time ≤ height).

Variants (exact search for a violation, true orbit or 'base' = arbitrary R₀ ∋ ⊥):
  V1 : m' good, t > m', c = b(t) < m'          ⇒ c good
  V2 : m' good, c = b(m') < m'                  ⇒ c good       (t = m')
  V3 : m' good, c < m', F(c, m') ≤ c            ⇒ c good       (pre-fixed in column m', not necessarily least)
  V5 : m' good, t > m', c = b(t) < m'          ⇒ every z < c is good
  python3 good_b.py V [base] (sweep P NMAX | closure K M SEED COUNT)
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from rstages import stages, b_of
from tight_probe import lattices, helpers
from feeder import base_stages
import single_local as sl

def query(L, mp, c, V, base):
    n = L.n; le = L.le; rk = L.rank; K = rk[mp]
    if base: E = Enc(L, 0); r = base_stages(E, L, K)
    else: E = Enc(L, K); r = lambda i, w: E.v('r', i, w)
    fle, yle, ic = helpers(E, L)
    E.S.add_clause([r(K, mp)])
    if V == 'V1': E.S.add_clause([E.v('B', t, c) for t in range(n) if le[mp][t] and t != mp])
    if V == 'V5': E.S.add_clause([E.v('B', t, c) for t in range(n) if le[mp][t] and t != mp])
    if V == 'V2': E.S.add_clause([E.v('B', mp, c)])
    if V == 'V3': E.S.add_clause([fle(c, mp, c)])
    if V == 'V5': E.S.add_clause([-r(rk[z], z) for z in range(n) if le[z][c] and z != c])
    else: E.S.add_clause([-r(rk[c], c)])
    if not E.S.solve(): E.S.delete(); return False
    mod = set(x for x in E.S.get_model() if x > 0); F = E.decode()
    if base:
        Rs = [[E.vars[('h', 0, w)] in mod for w in range(n)]]
        for i in range(K): Rs.append(sl.step_py(L, F, Rs[-1]))
    else:
        st = stages(L, F); Rs = [[st[w] is not None and st[w] <= i for w in range(n)] for i in range(K + 1)]
    E.S.delete(); good = lambda z: Rs[rk[z]][z]
    assert good(mp)
    if V == 'V5': assert not all(good(z) for z in range(n) if le[z][c] and z != c)
    else: assert not good(c)
    return F

if __name__ == '__main__':
    V = sys.argv[1]; base = 'base' in sys.argv; args = [a for a in sys.argv[2:] if a != 'base']
    C = collections.Counter(); best = None
    for L in lattices(args):
        hit = None
        for mp in range(L.n):
            for c in range(L.n):
                if c != mp and L.le[c][mp]:
                    res = query(L, mp, c, V, base)
                    if res: hit = (mp, c, res); break
            if hit: break
        C['violation' if hit else 'none'] += 1
        if hit and (best is None or L.n < best[0].n): best = (L, hit)
    print(f"good_b {V}{' base' if base else ''}: {dict(C)}" + (f"; smallest |L| = {best[0].n}" if best else ''), flush=True)
    if best: json.dump(dict(sets=best[0].S, F=best[1][2], mp=best[1][0], c=best[1][1]), open(f"good_b_{V}{'_base' if base else ''}_min{best[0].n}.json", 'w'))
