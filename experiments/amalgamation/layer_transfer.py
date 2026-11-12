"""Layer-to-layer transfer of interval cells (log §34.3z¹⁵⁴).

For consecutive tight stages k − 1, k (k ≥ 2; tight = R_j has maximal height exactly j and ⊤ ∉ R_{j+1}), the cells
(m', t) with m' ∈ T_{k−1}, t > m' land in T_k (t ∈ R_k has height k). Upper cells (t ≤ F(m', t)) make t diagonal,
hence IC(t). Records: whether stage k − 1 is tight; the cell types reaching T_k; IC(t) for the targets of lower
cells; whether some target has IC; and whether TightIC at k holds without any target having IC.
  python3 layer_transfer.py SEED SECONDS
"""
import sys, random, time, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages
from gfp_top import ic

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter()
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 3 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F); n = L.n; le = L.le
        tight = lambda j: st[L.top] > j + 1 and max(L.rank[z] for z in range(n) if st[z] <= j) == j
        for k in range(2, st[L.top] - 1):
            if not tight(k): continue
            T['tight stages k ≥ 2'] += 1
            if not tight(k - 1):
                h = max(L.rank[z] for z in range(n) if st[z] <= k - 1)
                T[('stage k−1 not tight: max height of R_{k−1} − (k−1)', h - (k - 1))] += 1; continue
            P = [z for z in range(n) if st[z] <= k - 1 and L.rank[z] == k - 1]
            Tk = [z for z in range(n) if st[z] <= k and L.rank[z] == k]
            up, lo = set(), set()
            for mp in P:
                for t in Tk:
                    if not le[mp][t] or mp == t: continue
                    if le[t][F[mp][t]]: up.add(t)
                    if le[F[mp][t]][mp]: lo.add(t)
            assert up | lo, 'TightIC at k−1 must give a target'
            assert all(ic(L, F, t) and le[t][F[t][t]] for t in up)
            T[('targets: upper present', bool(up))] += 1
            lo_only = lo - up
            for t in lo_only: T[('lower-only target has IC', ic(L, F, t))] += 1
            T[('some target has IC', any(ic(L, F, t) for t in up | lo))] += 1
            if not up: T[('no upper target: some lower target has IC', any(ic(L, F, t) for t in lo))] += 1
            if not any(ic(L, F, t) for t in up | lo):
                T[('no target has IC; TightIC at k', any(ic(L, F, t) for t in Tk))] += 1
    for k, v in sorted(T.items(), key=str): print(k, v)
