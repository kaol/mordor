"""Do bad pairs always have x ≤ y? (log §34.3z¹²⁵). Every run (all maximal-separator choices) of every instance:
count bad pairs with x ≰ y at non-stuck stages and at stuck stages; report the smallest instance with one.
  python3 xy_audit.py SEED N | records FILE"""
import sys, json, random, itertools
import separator_stages as ss

def scan(L, F, D, limit=20000):
    start = ss.mclose(L, {L.bot, L.top}); seen = set(); out = [0, 0, 0]; work = [0]   # [pairs, x≰y nonstuck, x≰y stuck]
    def dfs(T):
        if T in seen or work[0] > limit: return
        seen.add(T); bad = ss.bad_pairs(L, F, D, T)
        stuck = any(L.le[y][F[x][y]] for x, y in bad)
        for x, y in bad:
            out[0] += 1
            if not L.le[x][y]: out[2 if stuck else 1] += 1
        if not bad or stuck: return
        for ch in itertools.product(*[ss.max_separators(L, F[x][y], y) for x, y in bad]):
            work[0] += 1; dfs(ss.mclose(L, set(T) | set(ch)))
    dfs(start); return out

if __name__ == '__main__':
    if sys.argv[1] == 'records':
        for key, rs in json.load(open(sys.argv[2])).items():
            for r in rs: print(key, r['height'], r['n'], scan(ss.Lat(r['sets']), r['F'], r['D']))
    else:
        rng = random.Random(int(sys.argv[1])); tot = [0, 0, 0]; smallest = None
        for _ in range(int(sys.argv[2])):
            L, g, gens = ss.random_instance(rng.choice([4, 5, 6]), rng.choice([6, 10, 14]), rng)
            F = ss.make_F(L, g); D = ss.Dof(L, gens); o = scan(L, F, D)
            tot = [a + b for a, b in zip(tot, o)]
            if o[1] and (smallest is None or L.n < smallest[0]): smallest = (L.n, L.height, L.S, F, D)
        print(f"bad pairs {tot[0]}; with x ≰ y at non-stuck stages {tot[1]}, at stuck stages {tot[2]}")
        if smallest:
            print(f"smallest instance with a non-stuck bad pair x ≰ y: |L| = {smallest[0]}, height {smallest[1]}")
            json.dump(dict(sets=smallest[2], F=smallest[3], D=smallest[4]), open('xy_counterexample.json', 'w'))
