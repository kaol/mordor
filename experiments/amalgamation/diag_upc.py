"""Diagonal elements at tight stages (log §34.3z¹⁴¹).

Diagonal UPC lemma (Lean `OrbitHeight.upc_of_le_diag`): m ≤ F(m, m), m ≠ ⊤ ⇒ some y > m has F(m, y) ≤ m or
y ≤ F(m, y), because [m, ⊤] is F-invariant and the principal cut applies inside it.
At tight stages, with M the top-height elements of R_k, record:
  'diag top'   : some m ∈ M has m ≤ F(m, m);
  'diag any'   : some m ∈ R_k (any height) with m ≤ F(m, m) has some y > m entering R_{k+1} of height ≥ k + 1;
  'UPC top'    : some m ∈ M satisfies UPC(m).
  python3 diag_upc.py SEED SECONDS
"""
import sys, random, time, collections, json
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages
from upc import upc

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); T = collections.Counter(); ex = None
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5: g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F)
        for k in range(st[L.top] - 1):
            R = [z for z in range(L.n) if st[z] <= k]
            if max(L.rank[z] for z in R) != k: continue
            M = [z for z in R if L.rank[z] == k]
            dtop = any(L.le[m][F[m][m]] for m in M)
            T[('diag top', dtop)] += 1
            T[('UPC top', any(upc(L, F, m) for m in M))] += 1
            if not dtop:
                T[('no diag top: k', min(k, 3))] += 1
                if ex is None or L.n < ex['n']: ex = dict(n=L.n, sets=L.S, F=F, k=k, stages=st)
    print(dict(sorted(T.items(), key=str)), 'smallest tight stage with no diagonal top element:', ex and ex['n'], flush=True)
    if ex: json.dump(ex, open(f'diag_none_s{sys.argv[1]}.json', 'w'))
