"""Round 24 (§32.6): principal cuts as (F', ↓)-dialgebras L → O(L), transposed along sup ⊣ ↓ to κ-algebras;
μκ = ⊤; the comparison square sup∘Θ ≤ κ∘sup is lax and sometimes strict."""
# Principal cut d  <=>  (F', ↓)-dialgebra  F'(d) = ↓a(d) ∪ b⁻¹(↓d) ⊆ ↓d   <=>  κ(d) ≤ d,  κ(d) = a(d) ∨ ⋁{y : b(y) ≤ d}
# (sup ⊣ ↓ transposition). Least principal cut = μκ = r̂ (round 23); full Cut Lemma: μΘ in 𝒪(L), Θ(D) = ↓⊥ ∪ ↓a(D) ∪ b⁻¹(D).
import os, sys, collections, functools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'gpu'))
import numpy as np, torch, lattices as lt, engine
for spec in ['N5', 'B3', 'E2', 'M3']:
    L = lt.parse(spec); n, le = L.n, L.leq
    P = engine.Plan(L, torch.device('cpu'), census=False, mcmc=True); g = torch.Generator(); g.manual_seed(9)
    S = engine.mcmc_init(P, 4000)
    for _ in range(150): S = engine.sweep(P, S, g)
    Fs = S[:, :n * n].reshape(-1, n, n); f = engine.observe(P, Fs)
    A, B = f['a'].numpy(), f['b'].numpy(); c = collections.Counter()
    J = lambda xs: functools.reduce(lambda u, v: L.join[u, v], xs, L.bot)
    down = lambda S: {z for z in range(n) if any(le[z, s] for s in S)}
    for a, b in zip(A, B):
        kappa = [L.join[a[d], J([y for y in range(n) if le[b[y], d]])] for d in range(n)]
        for d in range(n):
            dial = (down({a[d]}) | {y for y in range(n) if le[b[y], d]}) <= down({d})
            c['transpose_ok'] += dial == le[kappa[d], d]; c['cells'] += 1
        z = L.bot
        for _ in range(n + 1): z = kappa[z]
        c['mu_kappa_top'] += z == L.top
        R = {L.bot}
        for _ in range(n + 1): R = down(R | {a[x] for x in R} | {y for y in range(n) if b[y] in R})
        c['R_full'] += len(R) == n; c['F'] += 1
        # lax square: sup Θ(D) ≤ κ(sup D) on every down-set D, strict somewhere?
        strict = False
        for mask in range(1, 1 << n):
            D = {x for x in range(n) if mask >> x & 1}
            if down(D) != D: continue
            th = down({L.bot} | {a[x] for x in D} | {y for y in range(n) if b[y] in D})
            lhs, rhs = J(th), kappa[J(D)]
            assert le[lhs, rhs]
            strict |= lhs != rhs
        c['square_strict_somewhere'] += strict
    print(spec, dict(c), flush=True)
