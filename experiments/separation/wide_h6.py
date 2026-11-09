"""Shortest-run descent on wide edge-height-6 lattices (log §34.3z¹²⁸).

Lattices: closure systems on 6 points with many random sets, kept when the edge-height is exactly 6, binned by size.
For each lattice: hill-climb (F, D) toward large existential minimum (exact branching), and on every accepted state
with existential minimum ≥ 3 test whether some shortest run has strictly decreasing maximum gap (shortest_audit).
Instances whose run enumeration exceeds the work limit are skipped and counted.
  python3 wide_h6.py SEED SECONDS MIN_SIZE
"""
import sys, random, time, json, collections
import separator_stages as ss
import shortest_audit as sa

def main(seed, seconds, min_size):
    rng = random.Random(seed); t0 = time.time()
    tested = collections.Counter(); hard = collections.Counter(); skipped = 0; fails = []; best = {}
    while time.time() - t0 < seconds:
        L = ss.Lat(ss.closure_system(6, rng.choice([14, 20, 28, 40]), rng))
        if L.height != 6 or L.n < min_size: continue
        n = L.n; size_bin = (n // 10) * 10
        g = {(a, b): rng.randrange(n) for a in range(n) for b in range(n) if rng.random() < 0.04}
        gens = [i for i in range(n) if i != L.top and rng.random() < 0.25] or [0]
        F = ss.make_F(L, g); D = ss.Dof(L, gens); cur = ss.exist_min(L, F, D, limit=20000)
        if cur is None: skipped += 1; continue
        for _ in range(25):
            if time.time() - t0 > seconds: break
            g2 = dict(g); gens2 = list(gens)
            for _ in range(rng.randint(1, 3)):
                if rng.random() < 0.8:
                    a, b = rng.randrange(n), rng.randrange(n)
                    if rng.random() < 0.6: g2[(a, b)] = rng.randrange(n)
                    else: g2.pop((a, b), None)
                else: gens2 = sorted(set(gens2) ^ {rng.randrange(n - 1)}) or [0]
            F2 = ss.make_F(L, g2); D2 = ss.Dof(L, gens2); st = ss.exist_min(L, F2, D2, limit=20000)
            if st is None or st < cur: continue
            g, gens, cur, F, D = g2, gens2, st, F2, D2
            if cur < 3: continue
            R = sa.runs(L, F, D, limit=60000)
            if R is None: skipped += 1; continue
            c, _, m = sa.classify(R)
            tested[size_bin] += 1
            if m >= 4: hard[size_bin] += 1
            best[size_bin] = max(best.get(size_bin, 0), m)
            if c == 'none':
                fails.append(n); json.dump(dict(sets=L.S, F=F, D=D), open(f"wide_h6_counterexample_s{seed}.json", 'w'))
                print(f"FAILURE: |L| = {n}, shortest length {m}", flush=True)
    print(f"seed {seed}: states tested by size bin {dict(sorted(tested.items()))}; with shortest length ≥ 4 "
          f"{dict(sorted(hard.items()))}; longest shortest run by bin {dict(sorted(best.items()))}; skipped (work limit) "
          f"{skipped}; failures {fails}", flush=True)

if __name__ == '__main__':
    main(int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]))
