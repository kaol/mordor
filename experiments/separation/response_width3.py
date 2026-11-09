"""Response-run length on height-3 linear spaces of growing width (log §34.3z¹³¹).
Linear spaces on k points (lines pairwise meeting in ≤ 1 point; height 3), hill-climbing (F, D) to maximize the
response-run length; reports the maximum per k.
  python3 response_width3.py SEED SECONDS KS
"""
import sys, random, time
import separator_stages as ss
from finite_landmarks import linear_space
from response_length import length

def climb(L, rng, iters):
    n = L.n
    g = {(a, c): rng.randrange(n) for a in range(n) for c in range(n) if rng.random() < 0.06}
    gens = [i for i in range(n) if i != L.top and rng.random() < 0.3] or [0]
    F = ss.make_F(L, g); D = ss.Dof(L, gens); cur = length(L, F, D)
    for _ in range(iters):
        g2 = dict(g); gens2 = list(gens)
        for _ in range(rng.randint(1, 3)):
            if rng.random() < 0.8:
                a, c = rng.randrange(n), rng.randrange(n)
                if rng.random() < 0.6: g2[(a, c)] = rng.randrange(n)
                else: g2.pop((a, c), None)
            else: gens2 = sorted(set(gens2) ^ {rng.randrange(n - 1)}) or [0]
        F2 = ss.make_F(L, g2); D2 = ss.Dof(L, gens2); l2 = length(L, F2, D2)
        if l2 >= cur: g, gens, cur = g2, gens2, l2
    return cur

if __name__ == '__main__':
    rng = random.Random(int(sys.argv[1])); ks = [int(x) for x in sys.argv[3].split(',')]
    per = float(sys.argv[2]) / len(ks)
    for k in ks:
        t0 = time.time(); best = 0; nmax = 0; tried = 0
        while time.time() - t0 < per:
            sets = linear_space(k, rng)
            L = ss.Lat([int(''.join('1' if i in s else '0' for i in reversed(range(k))), 2) for s in sets])
            if L.height != 3: continue
            tried += 1; best = max(best, climb(L, rng, 100)); nmax = max(nmax, L.n)
        print(f"height-3 linear spaces on {k} points (|L| ≤ {nmax}, {tried} lattices): longest response run {best}", flush=True)
