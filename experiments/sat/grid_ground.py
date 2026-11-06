"""Lattice ground refutation of the cut theory at edge-height ≤ H, with grid-capture clauses (log §34.3z¹¹⁶).

Extends lattice_ground.LGround by a derived clause family, one instance per pair of rows g₁, g₂ (terms) and orbit
lengths N₁, N₂. Orbits uᵢ(n) = F(gᵢ, ·)ⁿ(⊤) are F-terms; grid columns W(a, b) = u₁(a) ⊓ u₂(b) are meet terms. Instance (k = 2; the k-row form with iterated meets is analogous):
    ¬D(g₁) ∨ ¬D(g₂) ∨ ¬D(u₁(N₁)) ∨ ¬D(u₂(N₂)) ∨ ⋁_{a ≤ N₁, b ≤ N₂} x_ab,   x_ab → D(W(a,b)) ∧ W(a,b) ≰ g₁ ∧ W(a,b) ≰ g₂.
Soundness: Lean `InfCapture.uncaptured_column_upto` (no chain condition): in every lattice with a monotone F and a
witness-free cut, interpreting the terms by F, ⊓ makes the instance true. The x_ab are definitional fresh variables.
Without grid clauses this is lattice_ground.run. UNSAT proves the Cut Lemma for bounded lattices of edge-height ≤ H.
  python3 grid_ground.py H maxterms per_round J P [seconds]     (P = grid instances per round; P = 0 is the baseline;
                                                                 P = -1: one instance on the maximal D-classes of each model, k ≤ 3, N = H)"""
import sys, time, resource
import numpy as np
import lattice_ground as lg


class GGround(lg.LGround):
    def orbit(self, g, N):
        u = [1]
        for n in range(N):
            st = (g, u[-1])
            u.append(self.F[st] if st in self.F else self.add_term(st, max(self.depth[g], self.depth[u[-1]]) + 1))
        return u

    def meet(self, s, t):
        if s == 1: return t
        if t == 1: return s
        for (kind, a, b, z) in self.latt:
            if kind == 'm' and {a, b} == {s, t}: return z
        return self.add_lat('m', s, t)

    def add_grid(self, g1, g2, N1, N2):
        u1 = self.orbit(g1, N1); u2 = self.orbit(g2, N2)
        xs = []
        for a in range(N1 + 1):
            for b in range(N2 + 1):
                if a == 0 and b == 0: continue
                w = self.meet(u1[a], u2[b]); x = self.var(); xs.append(x)
                self.S.add_clause([-x, self.d(w)]); self.S.add_clause([-x, -self.le(w, g1)]); self.S.add_clause([-x, -self.le(w, g2)])
        self.S.add_clause([-self.d(g1), -self.d(g2), -self.d(u1[N1]), -self.d(u2[N2])] + xs)
        self.grids += 1

    def add_gridk(self, gs, N):
        """k-row instance (k = len(gs) ≤ 3), every orbit of length N: columns are iterated meets."""
        us = [self.orbit(g, N) for g in gs]; xs = []
        import itertools
        for t in itertools.product(range(N + 1), repeat=len(gs)):
            if not any(t): continue
            w = 1
            for u, a in zip(us, t): w = self.meet(w, u[a])
            x = self.var(); xs.append(x); self.S.add_clause([-x, self.d(w)])
            for g in gs: self.S.add_clause([-x, -self.le(w, g)])
        self.S.add_clause([-self.d(g) for g in gs] + [-self.d(u[N]) for u in us] + xs)
        self.grids += 1

    def expand_max(self, M):
        n = len(self.terms); L = self.L; D = np.array([self.d(i) in M for i in range(n)])
        rep = np.argmax(L & L.T, axis=1); Dc = sorted({int(r) for r in rep if D[r]})
        mx = tuple(c for c in Dc if not any(L[c, e] and not L[e, c] for e in Dc))
        if len(mx) > 3 or mx in self.grid_keys: return 0
        self.grid_keys.add(mx); self.add_gridk(list(mx), self.H); return 1

    def expand_grid(self, M, P):
        if P < 0: return self.expand_max(M)
        if P == 0: return 0
        n = len(self.terms); L = self.L; D = np.array([self.d(i) in M for i in range(n)])
        rep = np.argmax(L & L.T, axis=1); reps = sorted({int(r) for r in rep if D[r] and r != 0})
        def entry(g):                       # model entry time of the orbit of g (only along present F-terms)
            u = 1
            for n_ in range(1, self.H + 1):
                st = (g, u)
                if st not in self.F: return self.H
                u = self.F[st]
                if D[u]: return n_
            return self.H
        cands = []
        for i, a in enumerate(reps):
            for b in reps[i + 1:]:
                if L[a, b] or L[b, a]: continue
                Na, Nb = entry(a), entry(b)
                if (a, b, Na, Nb) in self.grid_keys: continue
                cands.append((self.depth[a] + self.depth[b] + Na + Nb, a, b, Na, Nb))
        cands.sort()
        for _, a, b, Na, Nb in cands[:P]:
            self.grid_keys.add((a, b, Na, Nb)); self.add_grid(a, b, Na, Nb)
        return len(cands[:P])


def run(H, maxterms, per_round, J, P, seconds=None):
    G = GGround(H, True, False, False, None, 'front', False, None); G.lat_keys = set(); G.grid_keys = set(); G.grids = 0
    cc = G.add_term((0, 1), 1); G.S.add_clause([-G.d(cc)])          # WLOG F(⊥,⊤) ∉ D (Lean cut_of_wlog)
    t0 = time.time(); rnd = 0
    while True:
        rnd += 1
        M = G.solve()
        nF = len(G.F); nL = len(G.latt)
        stat = f"{len(G.terms)} terms ({nF} F, {nL} lattice, {G.grids} grid instances)"
        if M is None:
            print(f"H={H} P={P}: UNSAT with {stat} after {rnd} rounds, {time.time() - t0:.1f}s", flush=True); return True, G
        if len(G.terms) >= maxterms or (seconds and time.time() - t0 > seconds):
            print(f"H={H} P={P}: inconclusive, SAT at {stat}, {rnd} rounds, {time.time() - t0:.0f}s", flush=True); return False, G
        a = G.expand(M, per_round); b = G.expand_lat(M, J); c = G.expand_grid(M, P)
        if rnd % 25 == 0:
            print(f"  H={H} P={P} round {rnd}: {stat}, {time.time() - t0:.0f}s, "
                  f"RSS {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6:.2f} GB", flush=True)
        if not a and not b and not c:
            print("closed partial model"); return False, G


if __name__ == '__main__':
    H, cap, pr, J, P = (int(x) for x in sys.argv[1:6])
    run(H, cap, pr, J, P, float(sys.argv[6]) if len(sys.argv) > 6 else None)
