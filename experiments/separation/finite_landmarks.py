"""The extremal-separator refinement on finite lattices (log §34.3z¹²⁰; brief A3, A5).

Lattices: closure systems on k points (random intersection-closed families with the full set; meet = ∩, join =
closure of ∪), so edge-height ≤ k while the width grows with the family. F(x, y) = ⋁ g(a, b) over a ≤ x, b ≤ y for a
sparse random g (monotone). D: the down-set of a random antichain avoiding ⊤.
Process (brief A3): T₀ = {⊥, ⊤}; at each stage every bad cross pair (x ∈ T ∩ D, y ∈ T ∖ D, y ≤ cl_T F(x,y)) gets an
extremal upper separator s⁺ (a maximal s ≥ F(x,y) with y ≰ s, found by greedy ascent); add them, close under ∩.
Ends: 'separated' (no bad pair: by `separating_family_witness` some cross pair of T has F(x,y) ≤ x, checked) or
'stuck' (a bad pair with y ≤ F(x,y): U⁺ empty, a witness of the second kind). Finite lattices always end; the data are
stage counts and |T| against height and width, and the aggregation cases of A4 (p = ⋁ separators: some y_α ≰ p, or
all y_α ≤ p with p ∉ D).
  python3 finite_landmarks.py [samples] [seed]"""
import random, sys, itertools, collections

def closure_system(k, m, rng):
    full = frozenset(range(k)); fam = {full}
    for _ in range(m): fam.add(frozenset(i for i in range(k) if rng.random() < 0.5))
    changed = True
    while changed:
        changed = False
        for a, b in itertools.combinations(list(fam), 2):
            if a & b not in fam: fam.add(a & b); changed = True
    return sorted(fam, key=lambda s: (len(s), sorted(s)))

def run(k, m, rng, L=None, g=None, gens=None):
    L = L or closure_system(k, m, rng); n = len(L); idx = {s: i for i, s in enumerate(L)}
    le = [[L[i] <= L[j] for j in range(n)] for i in range(n)]
    meet = lambda i, j: idx[L[i] & L[j]]
    def join(i, j):
        u = L[i] | L[j]; return min((t for t in range(n) if u <= L[t]), key=lambda t: len(L[t]))
    bot, top = 0, n - 1
    # height (edges of a longest chain)
    h = [0] * n
    for j in range(n):
        h[j] = max([h[i] + 1 for i in range(j) if le[i][j] and i != j] or [0])
    height = h[top]
    # random monotone F
    if g is None: g = {(a, b): (rng.randrange(n) if rng.random() < 0.08 else bot) for a in range(n) for b in range(n)}
    F = [[bot] * n for _ in range(n)]
    for x in range(n):
        for y in range(n):
            v = bot
            for a in range(n):
                if not le[a][x]: continue
                for b in range(n):
                    if le[b][y] and g[a, b] != bot: v = join(v, g[a, b])
            F[x][y] = v
    # random down-set
    if gens is None: gens = [i for i in range(n) if i != top and rng.random() < 0.3] or [bot]
    D = [any(le[i][gg] for gg in gens) for i in range(n)]
    def cl(T, z): 
        c = top
        for s in T:
            if le[z][s]: c = meet(c, s)
        return c
    def ascend(z, y):
        s = z
        while True:
            up = [t for t in range(n) if le[s][t] and t != s and not le[y][t]]
            if not up: return s
            s = min(up, key=lambda t: len(L[t]))
    T = {bot, top}; stages = 0; seps_all = []
    while True:
        bad = [(x, y) for x in T if D[x] for y in T if not D[y] and le[y][cl(T, F[x][y])]]
        if not bad:
            ok = any(le[F[x][y]][x] for x in T if D[x] for y in T if not D[y])
            return dict(n=n, height=height, stages=stages, T=len(T), end='separated', check=ok, seps=seps_all, g=g, gens=gens, L=L)
        if any(le[y][F[x][y]] for x, y in bad):
            return dict(n=n, height=height, stages=stages, T=len(T), end='stuck', check=True, seps=seps_all, g=g, gens=gens, L=L)
        new = {(x, y, ascend(F[x][y], y)) for x, y in bad}
        seps_all += list(new)
        T |= {s for _, _, s in new}
        changed = True
        while changed:
            changed = False
            for a, b in itertools.combinations(list(T), 2):
                c = meet(a, b)
                if c not in T: T.add(c); changed = True
        stages += 1
        aggregate = None
    return None

def linear_space(k, rng):
    """Height-3 lattice: ∅, points, lines (pairwise meeting in ≤ 1 point, ≥ 2 points each), the full set."""
    lines = []
    for _ in range(4 * k):
        sz = rng.randint(2, max(2, k // 2 + 1)); l = frozenset(rng.sample(range(k), sz))
        if all(len(l & m) <= 1 for m in lines) and l != frozenset(range(k)): lines.append(l)
    fam = {frozenset(), frozenset(range(k))} | {frozenset([i]) for i in range(k)} | set(lines)
    return sorted(fam, key=lambda s: (len(s), sorted(s)))

def climb(k, m, rng, iters, L0=None):
    r = run(k, m, rng, L=L0); best = r
    n = r['n']
    for _ in range(iters):
        g = dict(best['g']); gens = list(best['gens'])
        for _ in range(rng.randint(1, 3)):
            if rng.random() < 0.8:
                a, b = rng.randrange(n), rng.randrange(n); g[a, b] = rng.randrange(n) if rng.random() < 0.7 else 0
            else:
                c = rng.randrange(n - 1)
                gens = sorted(set(gens) ^ {c}) or [0]
        r = run(k, m, rng, L=best['L'], g=g, gens=gens)
        if r['stages'] >= best['stages']: best = r
    return best

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'climb':
    rng = random.Random(int(sys.argv[2])); out = collections.defaultdict(int)
    import time; t0 = time.time()
    while time.time() - t0 < float(sys.argv[3]):
        k = rng.choice([4, 5, 6]); m = rng.choice([6, 10, 14])
        b = climb(k, m, rng, 60)
        key = b['height']
        if b['stages'] > out[key]:
            out[key] = b['stages']
            print(f"height {key}, |L| {b['n']}: {b['stages']} stages ({b['end']}, |T| = {b['T']})", flush=True)
    print("max stages found per height:", dict(sorted(out.items())))
    raise SystemExit

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'width3':
    rng = random.Random(int(sys.argv[2])); ks = [int(x) for x in sys.argv[3].split(',')]
    for k in ks:
        best = 0; bn = 0
        for _ in range(int(sys.argv[4])):
            L0 = linear_space(k, rng)
            b = climb(k, 0, rng, 80, L0=L0)
            if b['stages'] > best: best, bn = b['stages'], b['n']
        print(f"height-3 linear spaces on {k} points (|L| up to {bn}): max stages {best}", flush=True)
    raise SystemExit

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 300; rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)
    rows = collections.defaultdict(list); agg = collections.Counter()
    for _ in range(N):
        k = rng.choice([3, 4, 5]); m = rng.choice([4, 8, 12, 16])
        r = run(k, m, rng)
        assert r['check']
        rows[(r['height'], r['end'])].append(r)
        if r['seps']:
            # A4 aggregation on the recorded separators: p = join of all separators
            # (computed on the subsets: closure of the union, i.e. the least closed superset)
            agg['with separators'] += 1
    print(f"{N} random instances (closure systems on 3–5 points)")
    for key in sorted(rows):
        rs = rows[key]
        print(f"  height {key[0]}, end {key[1]:9s}: {len(rs):4d} instances; |L| {min(r['n'] for r in rs)}–{max(r['n'] for r in rs)}; "
              f"stages max {max(r['stages'] for r in rs)}, mean {sum(r['stages'] for r in rs) / len(rs):.2f}; "
              f"|T| max {max(r['T'] for r in rs)}")
    by_n = collections.defaultdict(list)
    for rs in rows.values():
        for r in rs: by_n[(r['height'], r['n'] // 10)].append(r['stages'])
    print("max stages by (height, |L| decile):", {f"h{h},|L|~{10 * d}": max(v) for (h, d), v in sorted(by_n.items())})
