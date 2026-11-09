"""The nested-first separator rule (log §34.3z¹²⁷).

Rule: for every bad pair (x, y) choose a maximal separator s with s ≤ y when one exists (ties: lowest index);
otherwise the lowest-index maximal separator. Tested for maximum-gap descent (stuck stages exempt) on the records and
on mutations of hard instances. Variants: 'nested' as above; 'nested_rank' = among nested separators the one of
least height, else among all the one of least height; 'all' = the full process, adding every maximal separator of
every bad pair (a valid `Step`; in infinite lattices this set can be infinite).
  python3 nested_rule.py records FILE | hunt SEED SECONDS VARIANT FILES...
"""
import sys, json, random, time
import separator_stages as ss

def choose(L, F, x, y, variant):
    opts = ss.max_separators(L, F[x][y], y)
    nested = [s for s in opts if L.le[s][y]]
    pool = nested or opts
    if variant == 'nested_rank': return min(pool, key=lambda s: (L.rank[s], s))
    return min(pool)

def run(L, F, D, variant, cap=80):
    H = L.height; rk = L.rank; phi = lambda p: rk[p[1]] + H - rk[p[0]]
    T = ss.mclose(L, {L.bot, L.top}); seq = []
    for _ in range(cap):
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad):
            return all(a > b for a, b in zip(seq, seq[1:])), seq
        seq.append(max(phi(p) for p in bad))
        if variant == 'all':        # the full process: every maximal separator of every bad pair (a valid Step)
            T = ss.mclose(L, set(T) | {s for x, y in bad for s in ss.max_separators(L, F[x][y], y)})
        else:
            T = ss.mclose(L, set(T) | {choose(L, F, x, y, variant) for x, y in bad})
    return False, seq

if __name__ == '__main__':
    if sys.argv[1] == 'records':
        for key, rs in json.load(open(sys.argv[2])).items():
            for r in rs:
                L = ss.Lat(r['sets'])
                print(key, r['height'], r['n'], {v: run(L, r['F'], r['D'], v) for v in ('nested', 'nested_rank', 'all')}, flush=True)
    else:
        rng = random.Random(int(sys.argv[2])); t0 = time.time(); variant = sys.argv[4]; seeds = []
        for f in sys.argv[5:]:
            data = json.load(open(f)); recs = data['existential_maximal'] if isinstance(data, dict) else data
            seeds += [r for r in recs if r['exist_min'] >= 3]
        tested = fails = 0; distinct = set(); smallest = None
        while time.time() - t0 < float(sys.argv[3]):
            r = rng.choice(seeds); L = ss.Lat(r['sets']); n = L.n
            g = {(a, b): r['F'][a][b] for a in range(n) for b in range(n)}
            for _ in range(rng.randint(1, 4)):
                a, b = rng.randrange(n), rng.randrange(n); g[(a, b)] = rng.randrange(n) if rng.random() < 0.5 else 0
            F = ss.make_F(L, g); D = r['D']
            key = hash((tuple(L.S), tuple(map(tuple, F)), tuple(D)))
            if key in distinct: continue
            distinct.add(key)
            st = ss.exist_min(L, F, D)
            if st is None or st < 3: continue
            d, seq = run(L, F, D, variant); tested += 1
            if not d:
                fails += 1
                if smallest is None or n < smallest['n']: smallest = dict(n=n, height=L.height, seq=seq, sets=L.S, F=F, D=D)
        print(f"rule {variant}: {tested} distinct mutated hard instances, {fails} without descent", flush=True)
        if smallest:
            print(f"smallest failure: |L| = {smallest['n']}, height {smallest['height']}, M = {smallest['seq']}")
            json.dump(smallest, open(f"nested_{variant}_counterexample_s{sys.argv[2]}.json", 'w'))
