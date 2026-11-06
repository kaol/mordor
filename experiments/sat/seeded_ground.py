"""Lattice ground search seeded with the mixed-pivot configuration (log §34.3z¹¹⁸; brief Package C taken to totality).

lattice_ground.LGround (frontier F-terms + lattice terms, every axiom family as ground instances), plus constants
g0, g1, q (extra ground terms) with the configuration as unit/short clauses:
  g0, g1, q ∈ D, maximal among all terms (D(x) ∧ g ≤ x ⇒ x ≤ g, for every term, present and future), pairwise
  incomparable; orbits u_i(1) = F(g_i, ⊤) ∉ D, u_i(2) = F(g_i, u_i(1)) ∈ D; two-cycle u_0(2) ≤ g1, u_1(2) ≤ g0;
  pivot c = u_0(1) ⊓ u_1(1) ∈ D, c ≰ g0, g1, c ≤ q; Alternative I: F(m_T, c) ≤ m_T for some T ⊆ {0,1} nonempty
  (m_{01} = g0 ⊓ g1).
No WLOG unit (order duality does not preserve the seed). UNSAT means: no bounded lattice of edge-height ≤ H with a
monotone witness-free F contains this configuration (every clause is true there under the intended interpretation).
'noseed' is the same search without the configuration (and without WLOG), as baseline.
  python3 seeded_ground.py H maxterms per_round J seed|noseed [seconds] [I|II]
(I / II: add F(q, u_0(1)), F(q, u_1(1)), F(q, u_0(1) ⊔ u_1(1)) and force all three into D / out of D.)"""
import sys, time, resource
import lattice_ground as lg


class SGround(lg.LGround):
    def add_term(self, st, dep):
        i = super().add_term(st, dep)
        for gm in getattr(self, 'maxc', []):
            if gm != i: self.S.add_clause([-self.d(i), -self.le(gm, i), self.le(i, gm)])
        return i


def seed(G):
    S = G.S; cl = S.add_clause
    g0 = G.add_term(None, 0); g1 = G.add_term(None, 0); q = G.add_term(None, 0)
    G.maxc = []
    for a in (g0, g1, q):
        cl([G.d(a)])
        for x in range(len(G.terms)):
            if x != a: cl([-G.d(x), -G.le(a, x), G.le(x, a)])
    G.maxc = [g0, g1, q]
    for a, b in ((g0, g1), (g1, g0), (q, g0), (g0, q), (q, g1), (g1, q)): cl([-G.le(a, b)])
    u = {}
    for i, g in enumerate((g0, g1)):
        u[i, 1] = G.add_term((g, 1), 1); u[i, 2] = G.add_term((g, u[i, 1]), 2)
        cl([-G.d(u[i, 1])]); cl([G.d(u[i, 2])])
    cl([G.le(u[0, 2], g1)]); cl([G.le(u[1, 2], g0)])
    c = G.add_lat('m', u[0, 1], u[1, 1])
    cl([G.d(c)]); cl([-G.le(c, g0)]); cl([-G.le(c, g1)]); cl([G.le(c, q)])
    m01 = G.add_lat('m', g0, g1)
    fc = [G.add_term((r, c), 3) for r in (g0, g1, m01)]
    cl([G.le(fc[0], g0), G.le(fc[1], g1), G.le(fc[2], m01)])
    if getattr(G, 'branch', None):                     # cross cells F(q, x_i), F(q, y), outputs forced into one branch
        y = G.add_lat('j', u[0, 1], u[1, 1])
        for x in (u[0, 1], u[1, 1], y):
            z = G.add_term((q, x), 3); cl([G.d(z)] if G.branch == 'I' else [-G.d(z)])


def run(H, maxterms, per_round, J, mode, seconds=None, branch=None):
    G = SGround(H, True, False, False, None, 'front', False, None); G.lat_keys = set(); G.branch = branch
    G.add_term((0, 1), 1)                                           # F(⊥, ⊤), no WLOG unit
    if mode == 'seed': seed(G)
    t0 = time.time(); rnd = 0
    while True:
        rnd += 1; M = G.solve(); nF = len(G.F); nL = len(G.latt)
        stat = f"{len(G.terms)} terms ({nF} F, {nL} lattice)"
        if M is None:
            print(f"H={H} {mode}: UNSAT with {stat} after {rnd} rounds, {time.time() - t0:.1f}s", flush=True); return True, G
        if len(G.terms) >= maxterms or (seconds and time.time() - t0 > seconds):
            print(f"H={H} {mode}: inconclusive, SAT at {stat}, {rnd} rounds, {time.time() - t0:.0f}s", flush=True); return False, G
        a = G.expand(M, per_round); b = G.expand_lat(M, J)
        if rnd % 50 == 0:
            print(f"  H={H} {mode} round {rnd}: {stat}, {time.time() - t0:.0f}s, "
                  f"RSS {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6:.2f} GB", flush=True)
        if not a and not b: print("closed partial model"); return False, G


if __name__ == '__main__':
    H, cap, pr, J = (int(x) for x in sys.argv[1:5])
    run(H, cap, pr, J, sys.argv[5], float(sys.argv[6]) if len(sys.argv) > 6 else None,
        sys.argv[7] if len(sys.argv) > 7 else None)
