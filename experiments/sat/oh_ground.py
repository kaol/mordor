"""Model-guided ground refutation of the orbit-height theory OH_H (log §34.3z¹⁵⁹).

Universal theory, poset version (`lean/Mordor/GroundOH.lean`, structure `OHCx`): a bounded poset with no strict
chain of H + 2 elements (atoms g(t, k) = chainTo t k, k = 1..H+1), a monotone F, and sets M_k (k = 0..H) with
  t ≤ ⊥ → t ∈ M_0;   M_k ⊆ M_{k+1};   s ≤ t ∈ M_k → s ∈ M_k;
  x ∈ M_k ∧ F(x, y) ≤ x → y ∈ M_{k+1}   (b(y) ≤ x);      x ∈ M_k ∧ y ≤ F(x, y) → y ∈ M_{k+1}   (y ≤ a(x));
  ⊤ ∉ M_H.
In a complete lattice of edge-height ≤ H, M_k := R_k satisfies all of it, so UNSAT over any finite set of F-terms built
from ⊥, ⊤ proves ⊤ ∈ R_H (`OHAt H`). Terms are added from models: pairs x, y with M_k(x), ¬M_{k+1}(y), shallowest
first. Every clause carries a provenance tag (for `oh_lean.py`).
With 'ih' (lower heights proved): for each diagonal term F(c, c) also
  diag : F(c, c) ≤ c ∧ c ≠ ⊤ ∧ ¬chainTo c (k+1) → c ∈ M_k            (OrbitHeight.diagGood_of_lower)
  post : m ≤ F(m, m) ∧ m ≠ ⊥ ∧ m ∈ M_j ∧ chainTo m j → ⊤ ∈ M_H         (OrbitHeight.top_mem_of_good_post)
and diagonal terms are added first.
'fit': add the tightest candidate first (fewest model values between the monotonicity bounds), as cut_ground.py.
  python3 oh_ground.py H [CAP] [BATCH] [ih] [fit] [dump PREFIX]     (dump: PREFIX.cnf and PREFIX.pkl on UNSAT)
"""
import sys, time, itertools, pickle
import numpy as np
from pysat.solvers import Cadical153

class OH:
    def __init__(self, H, ih=False):
        self.ih = ih; self.H = H; self.S = Cadical153(); self.nv = 0; self.v = {}; self.terms = [None, None]; self.depth = [0, 0]
        self.F = {}; self.clauses = []; self.tags = []
        self._new_term(0); self._new_term(1)
        self.add([-self.le(1, 0)], ('topbot',)); self.add([-self.M(H, 1)], ('top',))
    def var(self, key):
        if key not in self.v: self.nv += 1; self.v[key] = self.nv
        return self.v[key]
    def le(self, i, j): return self.var(('le', i, j))
    def M(self, k, t): return self.var(('M', k, t))
    def g(self, t, k): return self.var(('g', t, k))
    def add(self, c, tag):
        self.S.add_clause(c); self.clauses.append(c); self.tags.append(tag)
    def _new_term(self, t):
        H = self.H; n = len(self.terms)
        self.add([self.le(t, t)], ('refl', t))
        if t != 0: self.add([self.le(0, t)], ('bot', t))
        if t != 1: self.add([self.le(t, 1)], ('topr', t))
        self.add([-self.le(t, 0), self.M(0, t)], ('base', t))
        self.add([-self.g(t, H + 1)], ('rankmax', t))
        for k in range(H): self.add([-self.M(k, t), self.M(k + 1, t)], ('incr', k, t))
        for s in range(n):
            if s == t: continue
            for (i, j) in ((s, t), (t, s)):
                self.add([-self.le(i, j), self.le(j, i), self.g(j, 1)], ('rank0', i, j))
                for k in range(1, H + 1):
                    self.add([-self.le(i, j), self.le(j, i), -self.g(i, k), self.g(j, k + 1)], ('rank', i, j, k))
                for k in range(H + 1): self.add([-self.le(i, j), -self.M(k, j), self.M(k, i)], ('down', k, i, j))
        # transitivity is added lazily (violations of the current model), see run()
    def add_F(self, x, y):
        if (x, y) in self.F: return self.F[(x, y)]
        t = len(self.terms); self.terms.append((x, y)); self.depth.append(1 + max(self.depth[x], self.depth[y]))
        self.F[(x, y)] = t; self._new_term(t)
        for (x2, y2), t2 in self.F.items():
            if t2 == t: continue
            self.add([-self.le(x, x2), -self.le(y, y2), self.le(t, t2)], ('mono', t, t2))
            self.add([-self.le(x2, x), -self.le(y2, y), self.le(t2, t)], ('mono', t2, t))
        if self.ih and x == y:
            c = x
            for k in range(self.H):
                self.add([-self.le(t, c), self.le(1, c), self.g(c, k + 1), self.M(k, c)], ('diag', k, t))
            for j in range(1, self.H + 1):
                self.add([-self.le(c, t), self.le(c, 0), -self.M(j, c), -self.g(c, j), self.M(self.H, 1)], ('post', j, t))
        for k in range(self.H):
            self.add([-self.M(k, x), -self.le(t, x), self.M(k + 1, y)], ('brule', k, t))
            self.add([-self.M(k, x), -self.le(y, t), self.M(k + 1, y)], ('arule', k, t))
        return t
    def model(self):
        m = set(l for l in self.S.get_model() if l > 0)
        return lambda key: self.v.get(key) in m

def run(H, cap=400, batch=4, verbose=True, ih=False, fit=False):
    G = OH(H, ih); t0 = time.time(); rounds = 0
    G.add_F(0, 1)
    if ih: G.add_F(0, 0); G.add_F(1, 1)
    while True:
        rounds += 1
        if not G.S.solve():
            if verbose: print(f"H={H}: UNSAT with {len(G.terms)} terms ({len(G.F)} F-terms), {len(G.clauses)} clauses, {rounds} rounds, {time.time()-t0:.1f}s", flush=True)
            return True, G
        if len(G.terms) >= cap:
            if verbose: print(f"H={H}: SAT at cap {cap} terms (inconclusive), {time.time()-t0:.1f}s", flush=True)
            return False, G
        val = G.model(); n = len(G.terms)
        Lm = np.zeros((n, n), dtype=bool)
        for (key, var) in G.v.items():
            if key[0] == 'le' and key[1] < n and key[2] < n: Lm[key[1], key[2]] = val(key)
        viol = np.argwhere((Lm.astype(np.int32) @ Lm.astype(np.int32) > 0) & ~Lm)
        if len(viol):
            for i, l in viol[:20000].tolist():
                js = np.flatnonzero(Lm[i] & Lm[:, l])
                j = int(js[0]); G.add([-G.le(i, j), -G.le(j, l), G.le(i, l)], ('trans', i, j, l))
            rounds -= 1; continue
        Mm = np.zeros((H + 1, n), dtype=bool)
        for (key, var) in G.v.items():
            if key[0] == 'M' and key[2] < n: Mm[key[1], key[2]] = val(key)
        rel = np.zeros((n, n), dtype=bool)
        for k in range(H): rel |= np.outer(Mm[k], ~Mm[k + 1])
        dep = np.array(G.depth)
        xs, ys = np.nonzero(rel)
        cand = [(1 + max(dep[x], dep[y]), int(x), int(y)) for x, y in zip(xs.tolist(), ys.tolist()) if (x, y) not in G.F]
        if verbose and rounds % 5 == 0:
            print(f"  round {rounds}: {n} terms, {len(G.clauses)} clauses, {len(cand)} candidates, {time.time()-t0:.0f}s", flush=True)
        if not cand and not ih:
            if verbose: print(f"H={H}: SAT with no new candidate terms ({len(G.terms)} terms)", flush=True)
            return False, G
        if fit and cand:                                # tightest first: fewest model values compatible with monotonicity
            Ft = list(G.F.items()); fx = np.array([k[0] for k, _ in Ft]); fy = np.array([k[1] for k, _ in Ft])
            ft = np.array([t for _, t in Ft])
            scored = []
            for d0, x, y in cand:
                lo = ft[Lm[fx, x] & Lm[fy, y]]; hi = ft[Lm[x, fx] & Lm[y, fy]]
                ok = np.ones(n, dtype=bool)
                if len(lo): ok &= Lm[lo].all(0)            # z ≥ every lower F-value
                if len(hi): ok &= Lm[:, hi].all(1)         # z ≤ every upper F-value
                scored.append((int(ok.sum()), d0, x, y))
            scored.sort(); cand = [(d0, x, y) for _, d0, x, y in scored]
        else: cand.sort()
        new = [(x, y) for _, x, y in cand[:batch]]
        if ih:                                          # one diagonal term per round: the shallowest term without one
            zs = [z for z in range(n) if (z, z) not in G.F and z != 1]
            if zs: z = min(zs, key=lambda z: (G.depth[z], z)); new.append((z, z))
        for x, y in new: G.add_F(x, y)

if __name__ == '__main__':
    H = int(sys.argv[1]); cap = int(sys.argv[2]) if len(sys.argv) > 2 else 400; batch = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    ok, G = run(H, cap, batch, ih='ih' in sys.argv, fit='fit' in sys.argv)
    if ok and 'dump' in sys.argv:
        pre = sys.argv[sys.argv.index('dump') + 1]
        with open(pre + '.cnf', 'w') as fh:
            fh.write(f"p cnf {G.nv} {len(G.clauses)}\n")
            for c in G.clauses: fh.write(" ".join(map(str, c)) + " 0\n")
        pickle.dump(dict(H=H, terms=G.terms, clauses=G.clauses, tags=G.tags, nv=G.nv), open(pre + '.pkl', 'wb'))
        print('dumped', pre)
