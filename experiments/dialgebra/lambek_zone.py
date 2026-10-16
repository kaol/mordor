"""Round 24 (§32.2–32.3): dialgebras in a lattice as a thin category. Reproduces the log's Lambek census (§12.2, §15.3),
checks the transposition μ^{f,g} = μ(g*∘f) for meet-preserving g, and the failure-zone predictor iso(δ0) ⟺ f(A0) ∈ Im g."""
# Dialgebras in a lattice viewed as a thin category: (f,g)-dialgebra = x with f(x) <= g(x).
# Reproduce the log's census (§12.2, §15.3) and test the predictor  iso(δ0)  <=>  f(A0) ∈ Im g.
import os, sys, collections
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'gpu'))
import numpy as np, lattices as lt
def analyse(L):
    n, le = L.n, L.leq; Mon = [tuple(r) for r in L.mon]
    meetpres = lambda g: all(g[L.meet[x, y]] == L.meet[g[x], g[y]] for x in range(n) for y in range(n))
    joinpres = lambda f: all(f[L.join[x, y]] == L.join[f[x], f[y]] for x in range(n) for y in range(n))
    st = collections.Counter()
    for f in Mon:
        for g in Mon:
            st['pairs'] += 1
            D = [x for x in range(n) if le[f[x], g[x]]]
            least = [x for x in D if all(le[x, y] for y in D)]
            if not D: st['empty'] += 1
            if not least: continue
            A0 = least[0]; st['init'] += 1
            iso = f[A0] == g[A0]; st['iso'] += iso
            pred = f[A0] in set(g)
            mp = meetpres(g)
            st['meetpres_g'] += mp
            st['pred_ok'] += (iso == pred)
            if mp: st['pred_ok_meetpres'] += (iso == pred); st['init_meetpres'] += 1
            if not mp and iso != pred: st['pred_fail_nonmp'] += 1
            # adjunction reduction: if g preserves all meets (incl. g(top)=top), A0 = mu(g* . f)
            if mp and g[L.top] == L.top:
                gs = [min((y for y in range(n) if le[x, g[y]]), key=lambda y: sum(le[:, y])) for x in range(n)]
                h = [gs[f[x]] for x in range(n)]; z = L.bot
                for _ in range(n + 1): z = h[z]
                st['adj_cases'] += 1; st['adj_ok'] += (z == A0)
    return st
for spec in ['C3', 'C4', 'M3', 'N5', 'B2']:
    s = analyse(lt.parse(spec))
    print(spec, dict(pairs=s['pairs'], init_exists=s['init'], iso=s['iso'], iso_rate=round(s['iso'] / max(s['init'], 1), 4),
          predictor_exact=f"{s['pred_ok']}/{s['init']}", when_g_meetpres=f"{s['pred_ok_meetpres']}/{s['init_meetpres']}",
          fails_only_nonmeetpres=s['pred_fail_nonmp'] == s['init'] - s['pred_ok'],
          adjoint_reduction=f"{s['adj_ok']}/{s['adj_cases']}"), flush=True)
