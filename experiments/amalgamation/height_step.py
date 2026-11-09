"""Localizing the height step of the orbit-height invariant (log §34.3z¹⁴⁰).

At a tight stage (max height of R_k equal to k, ⊤ ∉ R_{k+1}), with M = elements of R_k of maximal height:
  P1:  for every m ∈ M some y ∈ R_{k+1} has y > m;
  P1': for some m ∈ M some y ∈ R_{k+1} has y > m;
  P2:  R_{k+1} contains an element of height k + 1 (the step (OH) needs).
Random instances as in orbit_mech.py.  python3 height_step.py SEED SECONDS
"""
import sys, random, time, collections, json
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter(); ex = {}
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F)
        for k in range(st[L.top] - 1):
            R = [z for z in range(L.n) if st[z] <= k]; R1 = [z for z in range(L.n) if st[z] <= k + 1]
            mh = max(L.rank[z] for z in R)
            if mh != k: continue
            M = [z for z in R if L.rank[z] == mh]
            above = [any(L.le[m][y] and y != m for y in R1) for m in M]
            for nm, ok in (('P1', all(above)), ("P1'", any(above)), ('P2', max(L.rank[z] for z in R1) >= k + 1)):
                T[(nm, ok)] += 1
                if not ok and (nm not in ex or L.n < ex[nm]['n']): ex[nm] = dict(n=L.n, sets=L.S, F=F, k=k)
    print(dict(sorted(T.items(), key=str)), {k: v['n'] for k, v in ex.items()}, flush=True)
    json.dump(ex, open(f'height_step_viol_s{sys.argv[1]}.json', 'w'))
