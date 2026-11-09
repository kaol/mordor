"""Mechanism behind R_H = L (log §34.3z¹⁴⁰).

For random monotone F on random closure-system lattices, along the R-orbit (U_k = L ∖ R_k):
  (a) MIN:   every minimal element of U_k lies in R_{k+1};
  (b) CHAIN: the longest chain inside U_{k+1} is strictly shorter than the longest chain inside U_k
             (chain length in edges; −1 for the empty set);
  (f) REACH_HEIGHT_k: R_k contains an element of height ≥ k (would give R_H ∋ ⊤);
  (g) HEIGHT_RISES: the largest height in R_{k+1} exceeds the largest height in R_k;
  (c) COHEIGHT: R_k ⊇ {z : coheight(z) ≥ H − k}... reported as: every z with longest chain z → ⊤ of length
             ≥ H − k lies in R_k.
Counts violations; saves the smallest violating instance per statement.
  python3 orbit_mech.py SEED SECONDS
"""
import sys, random, time, json, collections
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages

def chain_len(L, U):
    U = set(U); memo = {}
    def up(z):
        if z in memo: return memo[z]
        r = max([1 + up(w) for w in L.covers_up[z] if w in U] + [0]); memo[z] = r; return r
    # longest chain inside U: chains in an up-set use covers of L (an up-set is convex upward)
    return max([up(z) for z in U] + [-1])

def coheight(L):
    memo = {}
    def ch(z):
        if z in memo: return memo[z]
        r = max([1 + ch(w) for w in L.covers_up[z]] + [0]); memo[z] = r; return r
    return [ch(z) for z in range(L.n)]

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); t0 = time.time(); tally = collections.Counter(); ex = {}
    while time.time() - t0 < float(sys.argv[2]):
        L = ss.Lat(ss.closure_system(rng.choice([4, 5, 6]), rng.choice([6, 8, 10, 14]), rng))
        if L.height < 2 or L.n > 40: continue
        _, g, gens = ss.random_instance(0, 0, rng, L)
        if rng.random() < 0.5:     # sparser generators give longer orbits
            g = {p: v for p, v in g.items() if rng.random() < 0.5}
        F = ss.make_F(L, g); st = stages(L, F); H = L.height; tally['instances'] += 1
        K = st[L.top]; tally[('top stage - H', K - H)] += 1
        co = coheight(L)
        for k in range(K):
            R = {z for z in range(L.n) if st[z] <= k}; U = set(range(L.n)) - R
            R1 = {z for z in range(L.n) if st[z] <= k + 1}; U1 = set(range(L.n)) - R1
            mins = [u for u in U if not any(v in U and v != u and L.le[v][u] for v in range(L.n))]
            okA = all(u in R1 for u in mins); okB = chain_len(L, U1) < chain_len(L, U)
            okC = all(z in R for z in range(L.n) if co[z] >= H - k)
            okF = max(L.rank[z] for z in R) >= k                          # (f) R_k reaches height k
            okG = max(L.rank[z] for z in R1) > max(L.rank[z] for z in R)  # (g) the top height of R_k rises
            for nm, ok in (('MIN', okA), ('CHAIN', okB), ('COHEIGHT', okC), ('REACH_HEIGHT_k', okF), ('HEIGHT_RISES', okG)):
                tally[(nm, ok)] += 1
                if not ok and (nm not in ex or L.n < ex[nm]['n']):
                    ex[nm] = dict(n=L.n, height=H, sets=L.S, F=F, k=k, stages=st)
    print(dict(sorted(tally.items(), key=str)), flush=True)
    for nm, e in ex.items(): print(f"smallest {nm} violation: |L| = {e['n']}, height {e['height']}, stage {e['k']}", flush=True)
    json.dump(ex, open(f'orbit_mech_viol_s{sys.argv[1]}.json', 'w'))
