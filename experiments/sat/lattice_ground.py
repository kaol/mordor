"""Ground refutation of the cut theory over LATTICES of edge-height ≤ H (log §34.3z⁷²).

Extends cut_ground.Ground with meet and join terms: z = s ⊓ t carries z ≤ s, z ≤ t and, for every other term w,
w ≤ s ∧ w ≤ t ⇒ w ≤ z (dually for joins). These are ground instances of the lattice axioms, so UNSAT proves the Cut
Lemma on every bounded LATTICE of edge-height ≤ H (enough for CL; the poset theory of cut_ground is stronger).
Each round adds frontier F-terms (as `run_height.py … front`) and up to J lattice terms: joins of incomparable
D-classes and meets of incomparable outside classes of the current model.
  python3 lattice_ground.py H maxterms per_round J [forget=B]"""
import sys, time, resource
import numpy as np
import cut_ground as c


class LGround(c.Ground):
    def __init__(self, *a, **k):
        self.latt = []
        super().__init__(*a, **k)

    def add_term(self, st, dep):
        i = super().add_term(st, dep)
        for (kind, s, t, z) in getattr(self, 'latt', []):
            if z == i: continue
            if kind == 'm': self.S.add_clause([-self.le(i, s), -self.le(i, t), self.le(i, z)])
            else: self.S.add_clause([-self.le(s, i), -self.le(t, i), self.le(z, i)])
        return i

    def add_lat(self, kind, s, t):
        z = self.add_term(None, max(self.depth[s], self.depth[t]) + 1)
        S = self.S
        if kind == 'm':
            S.add_clause([self.le(z, s)]); S.add_clause([self.le(z, t)])
            for w in range(len(self.terms)):
                if w != z: S.add_clause([-self.le(w, s), -self.le(w, t), self.le(w, z)])
        else:
            S.add_clause([self.le(s, z)]); S.add_clause([self.le(t, z)])
            for w in range(len(self.terms)):
                if w != z: S.add_clause([-self.le(s, w), -self.le(t, w), self.le(z, w)])
        self.latt.append((kind, s, t, z)); self.lat_keys.add((kind, s, t))
        return z

    def expand_lat(self, M, J):
        if J <= 0: return 0
        n = len(self.terms); L = self.L; D = np.array([self.d(i) in M for i in range(n)])
        rep = np.argmax(L & L.T, axis=1)
        reps = sorted(set(rep.tolist()))
        cands = []
        for a_i, a in enumerate(reps):
            for b in reps[a_i + 1:]:
                if L[a, b] or L[b, a] or D[a] != D[b]: continue
                kind = 'j' if D[a] else 'm'
                if (kind, a, b) in self.lat_keys: continue
                cands.append((self.depth[a] + self.depth[b], kind, a, b))
        cands.sort()
        for _, kind, a, b in cands[:J]: self.add_lat(kind, a, b)
        return len(cands[:J])


def run(H, maxterms, per_round, J, forget=None):
    G = LGround(H, True, False, False, None, 'front', False, forget); G.lat_keys = set()
    cc = G.add_term((0, 1), 1); G.S.add_clause([-G.d(cc)])          # WLOG F(⊥,⊤) ∉ D
    t0 = time.time(); rnd = 0
    while True:
        rnd += 1
        M = G.solve()
        nF = len(G.F); nL = len(G.latt)
        if M is None:
            print(f"H={H} lattice: UNSAT with {len(G.terms)} terms ({nF} F-terms, {nL} lattice terms) after {rnd} rounds, "
                  f"{time.time() - t0:.1f}s", flush=True)
            return True, G
        if len(G.terms) >= maxterms:
            print(f"H={H} lattice: inconclusive, SAT at {len(G.terms)} terms ({nF} F, {nL} lattice), {time.time() - t0:.0f}s", flush=True)
            return False, G
        a = G.expand(M, per_round); b = G.expand_lat(M, J)
        if rnd % 25 == 0:
            print(f"  H={H} round {rnd}: {len(G.terms)} terms ({nF} F, {nL} lattice), {time.time() - t0:.0f}s, "
                  f"RSS {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6:.2f} GB", flush=True)
        if not a and not b:
            print("closed partial model"); return False, G


if __name__ == '__main__':
    H = int(sys.argv[1]); cap = int(sys.argv[2]); pr = int(sys.argv[3]); J = int(sys.argv[4])
    fg = next((int(float(o.split('=')[1])) for o in sys.argv[5:] if o.startswith('forget=')), None)
    run(H, cap, pr, J, fg)
