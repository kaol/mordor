"""Hill-climb for monotone F maximising the join delay of R(F) (log §34.3k).

Mutation: one cell gets a random value in its feasible interval [⋁ F(below), ⋀ F(above)] (monotonicity kept).
Objective: (join delay, number of stages); a mutation is kept if the objective does not decrease.

  python3 amalgam_search.py STEPS RESTARTS spec..."""
import sys, os, random, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from amalgam_sample import LT, sampler, analyse


def objective(L, F):
    d, a, b, s = analyse(L, F)
    if d is None: return (99, 0), (d, a, b, s)
    return (d, max(s.values())), (d, a, b, s)


def climb(L, rng, steps):
    n, leq, J, M = L.n, L.leq, L.join, L.meet
    F = sampler(L, rng, 0.3); best, info = objective(L, F)
    cells = list(itertools.product(range(n), range(n)))
    for _ in range(steps):
        x, y = rng.choice(cells)
        lo, hi = L.bot, L.top
        for (u, v), w in F.items():
            if (u, v) == (x, y): continue
            if leq[u, x] and leq[v, y]: lo = J[lo, w]
            if leq[x, u] and leq[y, v]: hi = M[hi, w]
        choices = [z for z in range(n) if leq[lo, z] and leq[z, hi]]
        old = F[(x, y)]; F[(x, y)] = rng.choice(choices)
        val, inf = objective(L, F)
        if val >= best: best, info = val, inf
        else: F[(x, y)] = old
    return best, info, dict(F)


if __name__ == '__main__':
    steps, restarts = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(7)
    for spec in sys.argv[3:]:
        Ls = LT.parse(spec); Ls = Ls if isinstance(Ls, list) else [Ls]
        for L in Ls:
            top = None
            for _ in range(restarts):
                best, info, F = climb(L, rng, steps)
                if top is None or best > top[0]: top = (best, info, F)
            (d, st), (dd, a, b, s), F = top
            print(f"{L.name} (n={L.n}): max join delay {d}{' (R not join-closed!)' if d == 99 else ''}, stages {st}", flush=True)
            if d >= 3:
                print("   a", [int(v) for v in a], "b", [int(v) for v in b], "stages", {int(k): v for k, v in s.items()},
                      "\n   F", [[int(F[(x, y)]) for y in range(L.n)] for x in range(L.n)], flush=True)
