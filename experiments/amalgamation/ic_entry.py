"""IC versus first-entry stage at tight stages (log §34.3z¹⁵⁴).

For every top m ∈ T_k (k ≥ 1) of a random tight stage, record (IC(m), GFP(m), m new at stage k?, m ≤ F(m,m)?),
and for stages with a single top, whether that top is new.  python3 ic_entry.py SEED SECONDS
"""
import sys, random, time, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages
from gfp_top import gfp_ok, ic

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter()
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F); n = L.n; le = L.le
        for k in range(1, st[L.top] - 1):
            R = [z for z in range(n) if st[z] <= k]
            if max(L.rank[z] for z in R) != k: continue
            Tk = [z for z in R if L.rank[z] == k]
            new = [st[m] == k for m in Tk]
            T['tight stages'] += 1; T[('some top new', any(new))] += 1
            T[('some new top has IC', any(nw and ic(L, F, m) for m, nw in zip(Tk, new)))] += 1
            if len(Tk) == 1: T[('single top: new', new[0])] += 1
            for m, nw in zip(Tk, new):
                T[('top: (IC, GFP, new, diag)', ic(L, F, m), gfp_ok(L, F, m), nw, le[m][F[m][m]])] += 1
    for k, v in sorted(T.items(), key=str): print(k, v)
