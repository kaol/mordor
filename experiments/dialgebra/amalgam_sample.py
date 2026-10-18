"""Random-F test of the conjecture R_k ∨ R_k ⊆ R_{k+1} (join delay ≤ 1) for derived pairs (log §34.3k).

A random monotone F: cells of L × L in a linear extension; each cell gets a random element above the join of the
values already fixed below it (with probability p exactly that join, to bias towards tight F). Always feasible.
Reports, per lattice, the join-delay histogram and any F with delay ≥ 2 or with R(F) not join-closed.

  python3 amalgam_sample.py SAMPLES spec...      (specs as in gpu/lattices.py: all6, all7, B3, M4, E2, C3xC3, ...)"""
import sys, os, random, itertools, collections
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'gpu'))
import lattices as LT


def sampler(L, rng, p):
    n, leq, J = L.n, L.leq, L.join
    rank = leq.sum(0)                                                    # #elements below
    cells = sorted(itertools.product(range(n), range(n)), key=lambda c: rank[c[0]] + rank[c[1]])
    F = {}
    for (x, y) in cells:
        lo = L.bot
        for (u, v), w in F.items():
            if leq[u, x] and leq[v, y]: lo = J[lo, w]
        if rng.random() < p: F[(x, y)] = lo
        else: F[(x, y)] = rng.choice([z for z in range(n) if leq[lo, z]])
    return F


def fix(L, f, start):
    x = start
    while True:
        y = f(x)
        if y == x: return x
        x = y


def analyse(L, F):
    n, leq, J = L.n, L.leq, L.join
    a = [fix(L, lambda Y: F[(x, Y)], L.top) for x in range(n)]
    b = [fix(L, lambda X: F[(X, y)], L.bot) for y in range(n)]
    cur = {x for x in range(n) if leq[x, L.bot]}; s = {x: 0 for x in cur}; k = 0
    while True:
        gen = cur | {a[x] for x in cur} | {y for y in range(n) if b[y] in cur}
        nxt = {x for x in range(n) if any(leq[x, g] for g in gen)}; k += 1
        if nxt == cur: break
        for x in nxt - cur: s[x] = k
        cur = nxt
    d = 0
    for x, y in itertools.combinations(s, 2):
        z = int(J[x, y])
        if z not in s: return None, a, b, s
        d = max(d, s[z] - max(s[x], s[y]))
    return d, a, b, s


if __name__ == '__main__':
    N = int(sys.argv[1]); specs = sys.argv[2:]
    rng = random.Random(1)
    for spec in specs:
        Ls = LT.parse(spec); Ls = Ls if isinstance(Ls, list) else [Ls]
        for L in Ls:
            hist = collections.Counter(); bad = None
            for i in range(N):
                F = sampler(L, rng, p=(0.0, 0.3, 0.7)[i % 3])
                d, a, b, s = analyse(L, F); hist[d] += 1
                if (d is None or d >= 2) and bad is None: bad = (F, a, b, s)
            print(f"{L.name} (n={L.n}): {dict(sorted(hist.items(), key=lambda kv: (kv[0] is None, kv[0] or 0)))}", flush=True)
            if bad:
                F, a, b, s = bad
                print("   FIRST d≥2 / not closed:", "a", a, "b", b, "stages", s, "\n   leq", L.leq.astype(int).tolist(),
                      "\n   F", [[F[(x, y)] for y in range(L.n)] for x in range(L.n)], flush=True)
