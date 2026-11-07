"""Extremal-separator refinement: fast search, replayable traces, greedy vs existential (log §34.3z¹²¹).

Lattices: closure systems on k points (bitmask sets, meet = ∩, join = least closed superset of ∪); edge-height ≤ k.
F(x, y) = ⋁ g(a, b) over a ≤ x, b ≤ y (monotone), computed by a DP over lower covers; g sparse random.
D: down-set of a random antichain avoiding ⊤.
Process (SeparatorStages.Run): T₀ = {⊥, ⊤}; bad pair = cross pair (x ∈ T ∩ D, y ∈ T ∖ D) with y ≤ cl_T F(x, y);
a bad pair with y ≤ F(x, y) is *stuck* (stop); otherwise every bad pair gets a maximal separator, then meet-closure.
'greedy': separator by ascent through the lowest-indexed upper cover not above y.
'exist': exact minimum number of stages over all choices of maximal separators (branching; small instances only).
Modes:
  climb SEED SECONDS K OUT.json   hill-climb (F, D) on closure systems on K points to maximize greedy stages at the
                                   maximal height; every new record is saved with its full trace to OUT.json
  climbx SEED SECONDS K OUT.json  the same, maximizing the existential minimum (exact branching; small lattices)
  compare SEED N                  greedy vs existential minimum vs universal maximum on N small instances
"""
import random, sys, json, time, itertools

class Lat:
    def __init__(s, sets):
        s.S = sets; s.n = len(sets); idx = {x: i for i, x in enumerate(sets)}; s.idx = idx
        n = s.n
        s.le = [[(sets[i] & ~sets[j]) == 0 for j in range(n)] for i in range(n)]
        s.up = [sum(1 << j for j in range(n) if s.le[i][j]) for i in range(n)]
        s.meet = [[idx[sets[i] & sets[j]] for j in range(n)] for i in range(n)]
        def jn(i, j):
            u = sets[i] | sets[j]
            return min((t for t in range(n) if (u & ~sets[t]) == 0), key=lambda t: bin(sets[t]).count('1'))
        s.join = [[jn(i, j) for j in range(n)] for i in range(n)]
        s.bot = 0; s.top = n - 1
        s.covers_up = [[j for j in range(n) if j != i and s.le[i][j] and not any(
            k not in (i, j) and s.le[i][k] and s.le[k][j] for k in range(n))] for i in range(n)]
        s.covers_dn = [[i for i in range(n) if j in s.covers_up[i]] for j in range(n)]
        h = [0] * n
        for j in range(n): h[j] = max([h[i] + 1 for i in s.covers_dn[j]] or [0])
        s.rank = h; s.height = h[s.top]

def closure_system(k, m, rng):
    full = (1 << k) - 1; fam = {full}
    for _ in range(m): fam.add(rng.getrandbits(k))
    ch = True
    while ch:
        ch = False
        for a, b in itertools.combinations(list(fam), 2):
            if a & b not in fam: fam.add(a & b); ch = True
    return sorted(fam, key=lambda x: (bin(x).count('1'), x))

def make_F(L, g):
    n = L.n; F = [[0] * n for _ in range(n)]
    for x in range(n):                     # indices are sorted by size, so lower covers come first
        for y in range(n):
            v = g.get((x, y), 0)
            for x2 in L.covers_dn[x]: v = L.join[v][F[x2][y]]
            for y2 in L.covers_dn[y]: v = L.join[v][F[x][y2]]
            F[x][y] = v
    return F

def max_separators(L, z, y):
    """All maximal s ≥ z with y ≰ s."""
    if L.le[y][z]: return []
    res, seen, stack = set(), {z}, [z]
    while stack:
        s = stack.pop(); ups = [t for t in L.covers_up[s] if not L.le[y][t]]
        if not ups: res.add(s)
        for t in ups:
            if t not in seen: seen.add(t); stack.append(t)
    return sorted(res)

def greedy_sep(L, z, y):
    s = z
    while True:
        ups = [t for t in L.covers_up[s] if not L.le[y][t]]
        if not ups: return s
        s = min(ups)

def mclose(L, T):
    T = set(T); frontier = list(T)
    while frontier:
        new = []
        for a in frontier:
            for b in list(T):
                c = L.meet[a][b]
                if c not in T: T.add(c); new.append(c)
        frontier = new
    return frozenset(T)

def cl(L, T, z):
    c = L.top
    for s in T:
        if L.le[z][s]: c = L.meet[c][s]
    return c

def bad_pairs(L, F, D, T):
    return [(x, y) for x in T if D[x] for y in T if not D[y] and L.le[y][cl(L, T, F[x][y])]]

def greedy_run(L, F, D, cap=200):
    T = mclose(L, {L.bot, L.top}); trace = []
    for st in range(cap):
        bad = bad_pairs(L, F, D, T)
        if not bad: return st, 'separated', trace, T
        stuck = [(x, y) for x, y in bad if L.le[y][F[x][y]]]
        if stuck: trace.append(dict(T=sorted(T), bad=bad, stuck=stuck)); return st, 'stuck', trace, T
        seps = {(x, y): greedy_sep(L, F[x][y], y) for x, y in bad}
        trace.append(dict(T=sorted(T), bad=bad, seps=[[x, y, s] for (x, y), s in seps.items()]))
        T = mclose(L, set(T) | set(seps.values()))
    return cap, 'cap', trace, T

def exist_min(L, F, D, limit=4000, want='min'):
    """Minimum ('min') or maximum ('max', universal reading) number of stages over all separator choices (BFS on
    families); None if the branching exceeds limit."""
    start = mclose(L, {L.bot, L.top}); layer = {start}; st = 0; work = 0
    while True:
        nxt = set()
        for T in layer:
            bad = bad_pairs(L, F, D, T)
            if not bad or any(L.le[y][F[x][y]] for x, y in bad):
                if want == 'min': return st
                continue
            opts = [max_separators(L, F[x][y], y) for x, y in bad]
            combos = 1
            for o in opts: combos *= len(o)
            work += combos
            if work > limit: return None
            for ch in itertools.product(*opts): nxt.add(mclose(L, set(T) | set(ch)))
        if not nxt: return st
        layer = nxt; st += 1

def random_instance(k, m, rng, L=None):
    L = L or Lat(closure_system(k, m, rng)); n = L.n
    g = {(a, b): rng.randrange(n) for a in range(n) for b in range(n) if rng.random() < 0.06}
    gens = [i for i in range(n) if i != L.top and rng.random() < 0.25] or [0]
    return L, g, gens

def Dof(L, gens): return [any(L.le[i][g0] for g0 in gens) for i in range(L.n)]

def climb(seed, seconds, k, out):
    rng = random.Random(seed); t0 = time.time(); best_by_h = {}; records = []
    while time.time() - t0 < seconds:
        L, g, gens = random_instance(k, rng.choice([8, 12, 16, 24]), rng)
        if L.height < k - 1: continue
        F = make_F(L, g); D = Dof(L, gens); cur = greedy_run(L, F, D)[0]
        for _ in range(150):
            g2 = dict(g); gens2 = list(gens)
            for _ in range(rng.randint(1, 3)):
                if rng.random() < 0.8:
                    a, b = rng.randrange(L.n), rng.randrange(L.n)
                    if rng.random() < 0.6: g2[(a, b)] = rng.randrange(L.n)
                    else: g2.pop((a, b), None)
                else: gens2 = sorted(set(gens2) ^ {rng.randrange(L.n - 1)}) or [0]
            F2 = make_F(L, g2); D2 = Dof(L, gens2); st = greedy_run(L, F2, D2)[0]
            if st >= cur: g, gens, cur, F, D = g2, gens2, st, F2, D2
        h = L.height
        if cur > best_by_h.get(h, -1):
            best_by_h[h] = cur
            st, end, trace, T = greedy_run(L, F, D)
            ex = exist_min(L, F, D)
            rec = dict(height=h, n=L.n, k=k, sets=L.S, F=F, D=D, stages=st, end=end, exist_min=ex, trace=trace)
            records.append(rec)
            print(f"height {h}, |L| {L.n}: greedy {st} stages ({end}), existential minimum {ex}", flush=True)
            json.dump(records, open(out, 'w'))
    print("best greedy stages by height:", dict(sorted(best_by_h.items())), flush=True)

def climbx(seed, seconds, k, out):
    """Hill-climb maximizing the existential minimum (the reading that matters for Cut)."""
    rng = random.Random(seed); t0 = time.time(); best_by_h = {}; records = []
    while time.time() - t0 < seconds:
        L, g, gens = random_instance(k, rng.choice([6, 10, 14]), rng)
        if L.height < k - 1: continue
        F = make_F(L, g); D = Dof(L, gens); cur = exist_min(L, F, D)
        if cur is None: continue
        for _ in range(60):
            if time.time() - t0 > seconds: break
            g2 = dict(g); gens2 = list(gens)
            for _ in range(rng.randint(1, 3)):
                if rng.random() < 0.8:
                    a, b = rng.randrange(L.n), rng.randrange(L.n)
                    if rng.random() < 0.6: g2[(a, b)] = rng.randrange(L.n)
                    else: g2.pop((a, b), None)
                else: gens2 = sorted(set(gens2) ^ {rng.randrange(L.n - 1)}) or [0]
            F2 = make_F(L, g2); D2 = Dof(L, gens2); st = exist_min(L, F2, D2)
            if st is not None and st >= cur: g, gens, cur, F, D = g2, gens2, st, F2, D2
        h = L.height
        if cur > best_by_h.get(h, -1):
            best_by_h[h] = cur
            st, end, trace, T = greedy_run(L, F, D)
            rec = dict(height=h, n=L.n, k=k, sets=L.S, F=F, D=D, stages=st, end=end, exist_min=cur, trace=trace)
            records.append(rec)
            print(f"height {h}, |L| {L.n}: existential minimum {cur} (greedy {st}, {end})", flush=True)
            json.dump(records, open(out, 'w'))
    print("best existential minimum by height:", dict(sorted(best_by_h.items())), flush=True)

def compare(seed, N):
    rng = random.Random(seed); tot = diff = dmax = skipped = 0; worst = worst_u = 0
    for _ in range(N):
        L, g, gens = random_instance(rng.choice([4, 5]), rng.choice([6, 10]), rng)
        F = make_F(L, g); D = Dof(L, gens)
        gr = greedy_run(L, F, D)[0]; ex = exist_min(L, F, D); ux = exist_min(L, F, D, want='max')
        if ex is None or ux is None: skipped += 1; continue
        tot += 1
        assert ex <= gr <= ux
        if gr != ex: diff += 1; worst = max(worst, gr - ex)
        if ux != gr: dmax += 1; worst_u = max(worst_u, ux - gr)
    print(f"{tot} instances compared ({skipped} skipped: branching > limit): existential min < greedy in {diff} "
          f"(max gap {worst}); universal max > greedy in {dmax} (max gap {worst_u})")

if __name__ == '__main__':
    if sys.argv[1] == 'climb': climb(int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
    elif sys.argv[1] == 'climbx': climbx(int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), sys.argv[5])
    elif sys.argv[1] == 'compare': compare(int(sys.argv[2]), int(sys.argv[3]))
