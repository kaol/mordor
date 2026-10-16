"""Round 24 (§32.3–32.4): the dual predictor iso(δ1) ⟺ g(A1) ∈ Im f (f join-preserving), and D5 through an
anti-automorphism: (f,g) ↦ (ρgρ, ρfρ) sends initial dialgebras to final ones."""
import os, sys, collections, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'gpu'))
import lattices as lt
def anti_automorphism(L):
    n = L.n
    for p in itertools.permutations(range(n)):
        if all(L.leq[x, y] == L.leq[p[y], p[x]] for x in range(n) for y in range(n)): return p
for spec in ['C4', 'M3', 'N5', 'B2']:
    L = lt.parse(spec); n, le = L.n, L.leq; Mon = [tuple(r) for r in L.mon]
    joinpres = lambda f: all(f[L.join[x, y]] == L.join[f[x], f[y]] for x in range(n) for y in range(n))
    c = collections.Counter(); per = 0
    rho = anti_automorphism(L)
    def ext(f, g):
        D = [x for x in range(n) if le[f[x], g[x]]]
        lo = [x for x in D if all(le[x, y] for y in D)]; hi = [x for x in D if all(le[y, x] for y in D)]
        return (lo[0] if lo else None), (hi[0] if hi else None)
    for f in Mon:
        for g in Mon:
            A0, A1 = ext(f, g)
            if A1 is not None:
                c['final'] += 1; iso1 = f[A1] == g[A1]; c['iso1'] += iso1
                if joinpres(f): c['jp'] += 1; c['dual_pred_ok_jp'] += (iso1 == (g[A1] in set(f)))
            if A0 is not None: c['init'] += 1; c['iso0'] += f[A0] == g[A0]
            # D5 through the anti-automorphism rho: (f,g) -> (rho g rho, rho f rho) sends initial to final
            fd = tuple(rho[g[rho.index(x)]] for x in range(n)); gd = tuple(rho[f[rho.index(x)]] for x in range(n))
            B0, B1 = ext(fd, gd)
            per += (A0 is None) == (B1 is None) and (A0 is None or rho[A0] == B1)
    print(spec, dict(c), f"D5 via anti-automorphism maps initial(f,g) to final(dual pair): {per}/{len(Mon)**2}", flush=True)
