"""Lemma D (log §34.3z¹⁵⁷): if m' ∈ R_j and h(m') ≤ j, then every z < m' lies in R_{j−1}.

Exact search for a violation on the true orbit ('base': any down-set S₀ ∋ ⊥ as R₀). Options:
  off=d : j = h(m') + d (default 0)     base : arbitrary R₀
  bval  : Lemma D_b — z is required to be a b-value b(t) for some t (any t)
  aval  : z is required to be an a-value a(x) for some x
  python3 lemma_d.py [base] [off=d] (sweep P NMAX | closure K M SEED COUNT)
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from rstages import stages
from tight_probe import lattices
from feeder import base_stages
import single_local as sl

def query(L, mp, z, opt):
    n = L.n; j = L.rank[mp] + next((int(o[4:]) for o in opt if o.startswith('off=')), 0)
    if j < 1: return None
    if 'base' in opt: E = Enc(L, 0); r = base_stages(E, L, j)
    else: E = Enc(L, j); r = lambda i, w: E.v('r', i, w)
    E.S.add_clause([r(j, mp)]); E.S.add_clause([-r(j - 1, z)])
    if 'bval' in opt: E.S.add_clause([E.v('B', t, z) for t in range(n)])
    if 'aval' in opt: E.S.add_clause([E.v('A', x, z) for x in range(n)])
    if not E.S.solve(): E.S.delete(); return False
    mod = set(x for x in E.S.get_model() if x > 0); F = E.decode()
    if 'base' in opt:
        Rs = [[E.vars[('h', 0, w)] in mod for w in range(n)]]
        for i in range(j): Rs.append(sl.step_py(L, F, Rs[-1]))
    else:
        st = stages(L, F); Rs = [[st[w] is not None and st[w] <= i for w in range(n)] for i in range(j + 1)]
    E.S.delete(); assert Rs[j][mp] and not Rs[j - 1][z]
    return F

if __name__ == '__main__':
    opt = [a for a in sys.argv[1:] if a in ('base', 'bval', 'aval') or a.startswith('off=')]
    args = [a for a in sys.argv[1:] if a not in opt]
    C = collections.Counter(); best = None
    for L in lattices(args):
        hit = None
        for mp in range(L.n):
            for z in range(L.n):
                if z != mp and L.le[z][mp]:
                    res = query(L, mp, z, opt)
                    if res: hit = (mp, z, res); break
            if hit: break
        C['violation' if hit else 'none'] += 1
        if hit and (best is None or L.n < best[0].n): best = (L, hit)
    print(f"lemma D {' '.join(opt)}: {dict(C)}" + (f"; smallest |L| = {best[0].n}, h(m') = {best[0].rank[best[1][0]]}" if best else ''), flush=True)
    if best: json.dump(dict(sets=best[0].S, F=best[1][2], mp=best[1][0], z=best[1][1]), open(f"lemma_d{'_' + '_'.join(opt) if opt else ''}_min{best[0].n}.json", 'w'))
