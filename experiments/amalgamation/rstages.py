"""R-stage amalgamation depth (log §34.3z¹⁴⁰, Programme C).

Definitions as in lean/Mordor/Orbit.lean and Reach.lean, for a monotone F on a finite lattice:
  a(x) = gfp_y F(x, y),  b(y) = lfp_x F(x, y),  R_0 = ↓⊥,  R_{k+1} = ↓(R_k ∪ a(R_k) ∪ b⁻¹(R_k)).
st(z) = least k with z ∈ R_k. The join excess of a pair is st(x ∨ y) − max(st x, st y). On a finite lattice R
reaches L (Cut), so st is total. Hill-climbing over F (generator tables, least monotone extension) on a fixed
lattice maximizes the excess of some pair with st(x), st(y) ≤ M.
  python3 rstages.py (mn N | pencil K | closure K MM SEED) M SECONDS SEED
"""
import sys, random, time, json
sys.path.insert(0, '../separation')
import separator_stages as ss

def a_of(L, F, x):
    y = L.top
    while True:
        y2 = F[x][y]
        if y2 == y: return y
        y = y2

def b_of(L, F, y):
    x = L.bot
    while True:
        x2 = F[x][y]
        if x2 == x: return x
        x = x2

def stages(L, F, cap=1000):
    n = L.n; A = [a_of(L, F, x) for x in range(n)]; B = [b_of(L, F, y) for y in range(n)]
    st = [None] * n; cur = {z for z in range(n) if L.le[z][L.bot]}
    for z in cur: st[z] = 0
    k = 0
    while k < cap:
        gen = set(cur) | {A[x] for x in cur} | {y for y in range(n) if B[y] in cur}
        nxt = {z for z in range(n) if any(L.le[z][g] for g in gen)}
        if nxt == cur: break
        k += 1
        for z in nxt - cur: st[z] = k
        cur = nxt
    return st

def best_excess(L, st, M):
    best = (-1, None)
    for x in range(L.n):
        for y in range(L.n):
            if st[x] is None or st[y] is None or st[x] > M or st[y] > M: continue
            j = L.join[x][y]
            if st[j] is None: return (10 ** 6, (x, y))
            e = st[j] - max(st[x], st[y])
            if e > best[0]: best = (e, (x, y))
    return best

def climb(L, M, secs, rng):
    n = L.n; g = {}; F = ss.make_F(L, g); cur = best_excess(L, stages(L, F), M)[0]; best = (cur, dict(g)); t0 = time.time()
    while time.time() - t0 < secs:
        g2 = dict(g)
        for _ in range(rng.randint(1, 3)):
            p = (rng.randrange(n), rng.randrange(n))
            if rng.random() < 0.3: g2.pop(p, None)
            else: g2[p] = rng.randrange(n)
        F2 = ss.make_F(L, g2); v = best_excess(L, stages(L, F2), M)[0]
        if v >= cur or rng.random() < 0.02:
            g, cur = g2, v
            if v > best[0]: best = (v, dict(g2))
    return best

def lattice(args):
    if args[0] == 'mn':
        N = int(args[1]); return ss.Lat([0] + [1 << i for i in range(N)] + [(1 << N) - 1]), args[2:]
    if args[0] == 'pencil':
        sys.path.insert(0, '../separation'); import pencil_family
        return pencil_family.family(int(args[1]))[0], args[2:]
    k, m, sd = int(args[1]), int(args[2]), int(args[3])
    return ss.Lat(ss.closure_system(k, m, random.Random(sd))), args[4:]

if __name__ == '__main__':
    L, rest = lattice(sys.argv[1:]); M, secs, seed = int(rest[0]), float(rest[1]), int(rest[2])
    v, g = climb(L, M, secs, random.Random(seed)); F = ss.make_F(L, g); st = stages(L, F)
    print(f"{sys.argv[1:-3]}: |L| = {L.n}, height {L.height}, max join excess over pairs with stages ≤ {M}: {v}; "
          f"stages of elements {st}", flush=True)

def ideal_orbit(L, F, K):
    """r_0 = ⊥, r_{k+1} = r ⊔ a r ⊔ ⋁{y | b y ≤ r} (Lean `Orbit.rk`, `kstep`)."""
    A = [a_of(L, F, x) for x in range(L.n)]; B = [b_of(L, F, y) for y in range(L.n)]; r = [L.bot]
    for _ in range(K):
        c = r[-1]; v = L.join[c][A[c]]
        for y in range(L.n):
            if L.le[B[y]][c]: v = L.join[v][y]
        r.append(v)
    return r
