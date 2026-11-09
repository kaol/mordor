"""Ground refutation with extremal-separator Skolem constants (log §34.3z¹²⁹).

lattice_ground.LGround plus, for chosen cross pairs (x, y) of terms, two new constants:
  upper s:  D(x) ∧ ¬D(y) ⇒ F(x, y) ≤ s, y ≰ s, and for every term t: s ≤ t ⇒ t ≤ s ∨ y ≤ t   (maximal, ACC)
  lower r:  D(x) ∧ ¬D(y) ⇒ r ≤ F(x, y), r ≰ x, and for every term t: t ≤ r ⇒ r ≤ t ∨ t ≤ x   (minimal, DCC)
Soundness: in a witness-free chain-finite structure every cross pair has such separators
(`ExtremalSeparators.exists_upper_separator`, `exists_lower_separator`), so interpreting the constants by them
satisfies every clause; the maximality/minimality clauses are ground instances over the terms present (extended to
every new term). The WLOG unit F(⊥, ⊤) ∉ D stays sound (the added clauses hold in every counterexample).
Each round: frontier F-terms and lattice terms as in lattice_ground, plus separator constants for up to K new cross
pairs of the model (shallowest first).
  python3 sep_ground.py H maxterms per_round J K [seconds] [wlog|nowlog]
"""
import sys, time, resource
import numpy as np
import lattice_ground as lg


class XGround(lg.LGround):
    def add_term(self, st, dep):
        i = super().add_term(st, dep)
        for (kind, s, x, y, fxy) in getattr(self, 'seps', []):
            if i == s: continue
            self._sep_clause(kind, s, x, y, i)
        return i

    def _sep_clause(self, kind, s, x, y, t):
        cl = self.S.add_clause
        if kind == 'up':   # s ≤ t ⇒ t ≤ s ∨ y ≤ t
            cl([-self.d(x), self.d(y), -self.le(s, t), self.le(t, s), self.le(y, t)])
        else:              # t ≤ r ⇒ r ≤ t ∨ t ≤ x
            cl([-self.d(x), self.d(y), -self.le(t, s), self.le(s, t), self.le(t, x)])

    def add_seps(self, x, y):
        if (x, y) in self.F: fxy = self.F[(x, y)]
        else: fxy = self.add_term((x, y), max(self.depth[x], self.depth[y]) + 1)
        cl = self.S.add_clause; out = []
        for kind in ('up', 'lo'):
            s = self.add_term(None, max(self.depth[x], self.depth[y]) + 1)
            if kind == 'up':
                cl([-self.d(x), self.d(y), self.le(fxy, s)]); cl([-self.d(x), self.d(y), -self.le(y, s)])
            else:
                cl([-self.d(x), self.d(y), self.le(s, fxy)]); cl([-self.d(x), self.d(y), -self.le(s, x)])
            for t in range(len(self.terms)):
                if t != s: self._sep_clause(kind, s, x, y, t)
            self.seps.append((kind, s, x, y, fxy)); out.append(s)
        self.sep_pairs.add((x, y))
        return out

    def expand_seps(self, M, K):
        if K <= 0: return 0
        L = self.L; n = L.shape[0]; D = [self.d(i) in M for i in range(n)]     # terms present in the model
        rep = np.argmax(L & L.T, axis=1)
        seen = {(int(rep[a]), int(rep[b])) for (a, b) in self.sep_pairs if a < n and b < n}
        cand = sorted((self.depth[x] + self.depth[y], x, y) for x in range(n) for y in range(n)
                      if D[x] and not D[y] and (int(rep[x]), int(rep[y])) not in seen)
        k = 0
        for _, x, y in cand:
            if k >= K: break
            key = (int(rep[x]), int(rep[y]))
            if key in seen: continue
            seen.add(key); self.add_seps(x, y); k += 1
        return k


def run(H, maxterms, per_round, J, K, seconds=None, wlog=True):
    G = XGround(H, True, False, False, None, 'front', False, None); G.lat_keys = set(); G.seps = []; G.sep_pairs = set()
    cc = G.add_term((0, 1), 1)
    if wlog: G.S.add_clause([-G.d(cc)])
    t0 = time.time(); rnd = 0
    while True:
        rnd += 1; M = G.solve()
        stat = f"{len(G.terms)} terms ({len(G.F)} F, {len(G.latt)} lattice, {len(G.seps)} separator constants)"
        if M is None:
            print(f"H={H} K={K}: UNSAT with {stat} after {rnd} rounds, {time.time() - t0:.1f}s", flush=True); return True, G
        if len(G.terms) >= maxterms or (seconds and time.time() - t0 > seconds):
            print(f"H={H} K={K}: inconclusive, SAT at {stat}, {rnd} rounds, {time.time() - t0:.0f}s", flush=True); return False, G
        a = G.expand(M, per_round); b = G.expand_lat(M, J); c = G.expand_seps(M, K)
        if rnd % 25 == 0:
            print(f"  H={H} K={K} round {rnd}: {stat}, {time.time() - t0:.0f}s, "
                  f"RSS {resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1e6:.2f} GB", flush=True)
        if not a and not b and not c: print("closed partial model"); return False, G


if __name__ == '__main__':
    H, cap, pr, J, K = (int(x) for x in sys.argv[1:6])
    sec = float(sys.argv[6]) if len(sys.argv) > 6 else None
    run(H, cap, pr, J, K, sec, (sys.argv[7] if len(sys.argv) > 7 else 'wlog') == 'wlog')
