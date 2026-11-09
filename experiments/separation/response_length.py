"""Width dependence of the response-rule run length (log §34.3z¹³¹).

The response rule (separator = F(x, y)) gives one canonical run per instance; its length is the number of steps until a
stage with no bad pair or a stuck bad pair. Hill-climb (F, D) to maximize that length on closure-system lattices of
fixed edge-height H, binned by lattice size.
  python3 response_length.py SEED SECONDS K H
"""
import sys, random, time, collections
import separator_stages as ss
from general_sep import response_run

def length(L, F, D):
    d, seq = response_run(L, F, D); return len(seq)

def main(seed, seconds, k, H):
    rng = random.Random(seed); t0 = time.time(); best = collections.defaultdict(int); count = collections.Counter()
    while time.time() - t0 < seconds:
        L = ss.Lat(ss.closure_system(k, rng.choice([6, 10, 16, 24, 32]), rng))
        if L.height != H: continue
        n = L.n; b = (n // 10) * 10
        g = {(a, c): rng.randrange(n) for a in range(n) for c in range(n) if rng.random() < 0.06}
        gens = [i for i in range(n) if i != L.top and rng.random() < 0.3] or [0]
        F = ss.make_F(L, g); D = ss.Dof(L, gens); cur = length(L, F, D)
        for _ in range(120):
            g2 = dict(g); gens2 = list(gens)
            for _ in range(rng.randint(1, 3)):
                if rng.random() < 0.8:
                    a, c = rng.randrange(n), rng.randrange(n)
                    if rng.random() < 0.6: g2[(a, c)] = rng.randrange(n)
                    else: g2.pop((a, c), None)
                else: gens2 = sorted(set(gens2) ^ {rng.randrange(n - 1)}) or [0]
            F2 = ss.make_F(L, g2); D2 = ss.Dof(L, gens2); l2 = length(L, F2, D2)
            if l2 >= cur: g, gens, F, D, cur = g2, gens2, F2, D2, l2
        count[b] += 1
        if cur > best[b]:
            best[b] = cur; print(f"H={H} |L|={n}: response-run length {cur}", flush=True)
    print(f"H={H} (closure systems on {k} points): lattices climbed per size bin {dict(sorted(count.items()))}; "
          f"longest response run per bin {dict(sorted(best.items()))}", flush=True)

if __name__ == '__main__':
    main(int(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
