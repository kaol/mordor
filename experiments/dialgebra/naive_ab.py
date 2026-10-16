"""Round 24 (§32.5, negative): dialgebras of (a,b) and (b,a) built from the derived pair do not encode m = n."""
# Do the CL objects sit in dialgebra form?  For every F on small lattices (exhaustive on C4/B2, heat-bath samples
# on N5/M3/B3): dialgebras of (b,a) and (a,b), their least/greatest elements, Lambek iso-ness, vs m, n, CL.
import os, sys, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'gpu'))
import numpy as np, torch, lattices as lt, engine
def Fs(L, exhaustive):
    dev = torch.device('cpu')
    if exhaustive:
        P = engine.Plan(L, dev, census=True, mcmc=True)
        Rw = torch.zeros(1, 0, dtype=torch.int32)
        for k in range(L.n): Rw = engine.census_level(P, Rw, k)
        return engine.leaves_to_F(P, Rw).numpy()
    P = engine.Plan(L, dev, census=False, mcmc=True); g = torch.Generator(); g.manual_seed(5)
    S = engine.mcmc_init(P, 20000)
    for _ in range(200): S = engine.sweep(P, S, g)
    return S[:, :L.n * L.n].reshape(-1, L.n, L.n).numpy()
def extremes(L, D):
    lo = [x for x in D if all(L.leq[x, y] for y in D)]; hi = [x for x in D if all(L.leq[y, x] for y in D)]
    return (lo[0] if lo else None), (hi[0] if hi else None)
for spec, ex in [('C4', True), ('B2', True), ('N5', False), ('M3', False), ('B3', False)]:
    L = lt.parse(spec); n = L.n; c = collections.Counter()
    for F in Fs(L, ex):
        F = np.asarray(F)
        a, b = [0]*n, [0]*n
        for x in range(n):
            y = L.top
            for _ in range(n): y = F[x, y]
            a[x] = y
            z = L.bot
            for _ in range(n): z = F[z, x]
            b[x] = z
        m = L.bot; nn = L.top
        for _ in range(n): m = a[m]; nn = b[nn]
        meqn = m == nn; c['F'] += 1; c['meqn'] += meqn
        for name, (f, g) in (('ba', (b, a)), ('ab', (a, b))):
            D = [x for x in range(n) if L.leq[f[x], g[x]]]
            lo, hi = extremes(L, D)
            c[f'{name}:least=m'] += (lo == m); c[f'{name}:greatest=n'] += (hi == nn)
            c[f'{name}:least_exists'] += lo is not None; c[f'{name}:greatest_exists'] += hi is not None
            iso0 = lo is not None and f[lo] == g[lo]; iso1 = hi is not None and f[hi] == g[hi]
            c[f'{name}:iso0==meqn'] += (iso0 == meqn); c[f'{name}:iso1==meqn'] += (iso1 == meqn)
            c[f'{name}:D==[m,n]'] += set(D) == {x for x in range(n) if L.leq[m, x] and L.leq[x, nn]}
    print(spec, dict(sorted(c.items())), flush=True)
