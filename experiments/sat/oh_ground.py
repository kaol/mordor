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
Diagonal terms never arise as ordinary candidates (M_k ⊆ M_{k+1}); with 'lazyd=N' up to N are created per round,
model-triggered: for terms c ≠ ⊤ that are good in the model (M_j(c) ∧ chainTo c j, j ≥ 1: the post route) or that are
the y of a relevant pair (the diag route), shallowest first. 'eagerd' restores the old one-per-round rule.
With 'rigid' (the case left by OrbitHeight.top_mem_reduction): a(⊥) = ⊥, b(⊤) = ⊤, no interior diagonal fixed point,
instantiated on terms of the matching shape:
  rigA : y ≤ F(⊥, y) → y ≤ ⊥;   rigB : F(x, ⊤) ≤ x → ⊤ ≤ x;   rigD : F(c, c) ≤ c ∧ c ≤ F(c, c) → c ≤ ⊥ ∨ ⊤ ≤ c.
'kleene=K': for the K best relevant pairs (x, y) add the whole column chain of y (⊥, F(⊥,y), …, H+1 steps ↑ b(y))
and row chain of x (⊤, F(x,⊤), …, ↓ a(x)) — the orbit needs Kleene depth ~H per stage; 'konly': no single terms.
'seed=1': start from the boundary orbits u_i = F(u_{i−1}, ⊤), d_j = F(⊥, d_{j−1}); 'seed=2': also all F(p, q) over them.
'fit': add the tightest candidate first (fewest model values between the monotonicity bounds), as cut_ground.py.
  python3 oh_ground.py H [CAP] [BATCH] [rigid] [ih] [lazyd=N|eagerd] [fit] [dump PREFIX]     (dump: PREFIX.cnf and PREFIX.pkl on UNSAT)
"""
import sys, time, itertools, pickle
import numpy as np
KEEP = 'dump' in sys.argv
LAZYALL = 'lazyall' in sys.argv
SEED = next((int(a[5:]) for a in sys.argv if a.startswith('seed=')), 0)
KLEENE = next((int(a[7:]) for a in sys.argv if a.startswith('kleene=')), 0)
KLEENE_ONLY = 'konly' in sys.argv
FIRABLE = 'firable' in sys.argv
PRIO = next((int(a[5:]) for a in sys.argv if a.startswith('prio=')), 0)          # keep clauses (for the certificate) only when dumping
from pysat.solvers import Cadical153

class OH:
    def __init__(self, H, ih=False, rigid=False):
        self.ih = ih; self.rigid = rigid; self.H = H; self.S = Cadical153(); self.nv = 0; self.v = {}; self.terms = [None, None]; self.depth = [0, 0]
        self.F = {}; self.clauses = []; self.tags = []; self.ncl = 0; self.keep = KEEP
        self._new_term(0); self._new_term(1)
        self.add([-self.le(1, 0)], ('topbot',)); self.add([-self.M(H, 1)], ('top',))
    def var(self, key):
        if key not in self.v: self.nv += 1; self.v[key] = self.nv
        return self.v[key]
    def le(self, i, j): return self.var(('le', i, j))
    def M(self, k, t): return self.var(('M', k, t))
    def g(self, t, k): return self.var(('g', t, k))
    def add(self, c, tag):
        self.S.add_clause(c); self.ncl += 1
        if self.keep: self.clauses.append(c); self.tags.append(tag)
    def _new_term(self, t):
        H = self.H; n = len(self.terms)
        self.add([self.le(t, t)], ('refl', t))
        if t != 0: self.add([self.le(0, t)], ('bot', t))
        if t != 1: self.add([self.le(t, 1)], ('topr', t))
        self.add([-self.le(t, 0), self.M(0, t)], ('base', t))
        self.add([-self.g(t, H + 1)], ('rankmax', t))
        for k in range(H): self.add([-self.M(k, t), self.M(k + 1, t)], ('incr', k, t))
        for s in range(n):
            if s == t or LAZYALL: continue
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
            if t2 == t or LAZYALL: continue
            self.add([-self.le(x, x2), -self.le(y, y2), self.le(t, t2)], ('mono', t, t2))
            self.add([-self.le(x2, x), -self.le(y2, y), self.le(t2, t)], ('mono', t2, t))
        if self.rigid:
            if x == 0: self.add([-self.le(y, t), self.le(y, 0)], ('rigA', t))
            if y == 1: self.add([-self.le(t, x), self.le(1, x)], ('rigB', t))
            if x == y: self.add([-self.le(t, x), -self.le(x, t), self.le(x, 0), self.le(1, x)], ('rigD', t))
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

def run(H, cap=400, batch=4, verbose=True, ih=False, fit=False, rigid=False, lazyd=0, eagerd=False):
    G = OH(H, ih, rigid); t0 = time.time(); rounds = 0
    G.add_F(0, 1)
    if SEED:                                            # boundary orbits u_i, d_j and all F(p, q) over them
        B = [0, 1]; u = 0; d = 1
        for _ in range(H):
            u = G.add_F(u, 1); d = G.add_F(0, d); B += [u, d]
        B = sorted(set(B))
        if SEED >= 2:
            for p_ in B:
                for q_ in B: G.add_F(p_, q_)
    if eagerd: G.add_F(0, 0); G.add_F(1, 1)
    while True:
        rounds += 1
        if not G.S.solve():
            if verbose: print(f"H={H}: UNSAT with {len(G.terms)} terms ({len(G.F)} F-terms), {G.ncl} clauses, {rounds} rounds, {time.time()-t0:.1f}s", flush=True)
            return True, G
        if len(G.terms) >= cap:
            if verbose: print(f"H={H}: SAT at cap {cap} terms (inconclusive), {time.time()-t0:.1f}s", flush=True)
            return False, G
        val = G.model(); n = len(G.terms)
        Lm = np.zeros((n, n), dtype=bool)
        for (key, var) in G.v.items():
            if key[0] == 'le' and key[1] < n and key[2] < n: Lm[key[1], key[2]] = val(key)
        viol = np.argwhere((Lm.astype(np.int32) @ Lm.astype(np.int32) > 0) & ~Lm)
        if LAZYALL:                                     # lazy down-closure, chain and monotonicity families
            Mm0 = np.zeros((H + 1, n), dtype=bool); Gm0 = np.zeros((H + 2, n), dtype=bool)
            for (key, var) in G.v.items():
                if key[0] == 'M' and key[2] < n: Mm0[key[1], key[2]] = val(key)
                elif key[0] == 'g' and key[1] < n: Gm0[key[2], key[1]] = val(key)
            added = 0
            for k in range(H + 1):
                for s_, t_ in np.argwhere(Lm & Mm0[k][None, :] & ~Mm0[k][:, None]).tolist():
                    G.add([-G.le(s_, t_), -G.M(k, t_), G.M(k, s_)], ('down', k, s_, t_)); added += 1
            lt = Lm & ~Lm.T
            for i, j in np.argwhere(lt & ~Gm0[1][None, :]).tolist():
                G.add([-G.le(i, j), G.le(j, i), G.g(j, 1)], ('rank0', i, j)); added += 1
            for k in range(1, H + 1):
                for i, j in np.argwhere(lt & Gm0[k][:, None] & ~Gm0[k + 1][None, :]).tolist():
                    G.add([-G.le(i, j), G.le(j, i), -G.g(i, k), G.g(j, k + 1)], ('rank', i, j, k)); added += 1
            if G.F:
                Ft = list(G.F.items()); fx = np.array([q[0] for q, _ in Ft]); fy = np.array([q[1] for q, _ in Ft])
                ft = np.array([t_ for _, t_ in Ft])
                bad = Lm[np.ix_(fx, fx)] & Lm[np.ix_(fy, fy)] & ~Lm[np.ix_(ft, ft)]
                for a_, b_ in np.argwhere(bad).tolist():
                    t1, t2 = int(ft[a_]), int(ft[b_])
                    G.add([-G.le(int(fx[a_]), int(fx[b_])), -G.le(int(fy[a_]), int(fy[b_])), G.le(t1, t2)], ('mono', t1, t2)); added += 1
            if added:
                for i, l in viol[:20000].tolist():
                    js = np.flatnonzero(Lm[i] & Lm[:, l]); j = int(js[0])
                    G.add([-G.le(i, j), -G.le(j, l), G.le(i, l)], ('trans', i, j, l))
                rounds -= 1; continue
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
        Gm2 = np.zeros((H + 2, n), dtype=bool)
        for (key, var) in G.v.items():
            if key[0] == 'g' and key[1] < n: Gm2[key[2], key[1]] = val(key)
        mrank = Gm2[1:].sum(0)                          # model rank (longest chain below)
        kmax = np.full((n, n), -1)
        for k in range(H): kmax[np.outer(Mm[k], ~Mm[k + 1])] = k
        xs, ys = np.nonzero(rel)
        def key(x, y):
            d0 = 1 + max(dep[x], dep[y])
            if PRIO == 1: return (d0, -int(kmax[x, y]))            # relevant at the latest stage first
            if PRIO == 2: return (d0, -int(mrank[y]))              # highest y first
            if PRIO == 3: return (d0, -int(kmax[x, y]), -int(mrank[y]))
            if PRIO == 4: return (-int(kmax[x, y]), d0)            # stage before depth
            return (d0,)
        cand = [key(x, y) + (int(x), int(y)) for x, y in zip(xs.tolist(), ys.tolist()) if (x, y) not in G.F]
        if verbose and rounds % 5 == 0:
            print(f"  round {rounds}: {n} terms, {G.ncl} clauses, {len(cand)} candidates, {time.time()-t0:.0f}s", flush=True)
        if not cand and not lazyd and not eagerd:
            if verbose: print(f"H={H}: SAT with no new candidate terms ({len(G.terms)} terms)", flush=True)
            return False, G
        if FIRABLE and cand and G.F:                    # keep pairs whose new term could still fire a rule
            Ft = list(G.F.items()); fx = np.array([q[0] for q, _ in Ft]); fy = np.array([q[1] for q, _ in Ft])
            ft = np.array([t_ for _, t_ in Ft]); keep = []
            cand.sort()
            for c in cand[:3000]:
                x, y = c[-2], c[-1]
                lo = ft[Lm[fx, x] & Lm[fy, y]]; hi = ft[Lm[x, fx] & Lm[y, fy]]
                ok = np.ones(n, dtype=bool)
                if len(lo): ok &= Lm[lo].all(0)
                if len(hi): ok &= Lm[:, hi].all(1)
                if (ok & Lm[:, x]).any() or (ok & Lm[y, :]).any(): keep.append(c)
            cand = keep or cand[:3000]
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
        new = [(c[-2], c[-1]) for c in cand[:batch]]
        if eagerd:                                      # old rule: the shallowest term without a diagonal term
            zs = [z for z in range(n) if (z, z) not in G.F and z != 1]
            if zs: z = min(zs, key=lambda z: (G.depth[z], z)); new.append((z, z))
        if lazyd:                                       # model-triggered diagonal terms
            Gm = np.zeros((H + 2, n), dtype=bool)
            for (key, var) in G.v.items():
                if key[0] == 'g' and key[1] < n: Gm[key[2], key[1]] = val(key)
            good = np.zeros(n, dtype=bool)
            for j in range(1, H + 1): good |= Mm[j] & Gm[j]
            ys = set(ys.tolist()) if len(ys) else set()
            trig = [z for z in range(2, n) if (z, z) not in G.F and not Lm[z, 0] and not Lm[1, z] and (good[z] or z in ys)]
            trig.sort(key=lambda z: (G.depth[z], z))
            new += [(z, z) for z in trig[:lazyd]]
        if KLEENE:                                      # whole Kleene chains: column y (→ b(y)) and row x (→ a(x))
            chains = []
            for x, y in new[:KLEENE]:
                c = 0
                for _ in range(H + 1): c = G.add_F(c, y)
                e = 1
                for _ in range(H + 1): e = G.add_F(x, e)
            new = new[KLEENE:] if KLEENE_ONLY is False else []
        for x, y in new: G.add_F(x, y)

if __name__ == '__main__':
    H = int(sys.argv[1]); cap = int(sys.argv[2]) if len(sys.argv) > 2 else 400; batch = int(sys.argv[3]) if len(sys.argv) > 3 else 4
    lz = next((int(a[6:]) for a in sys.argv if a.startswith('lazyd=')), 0)
    ok, G = run(H, cap, batch, ih='ih' in sys.argv, fit='fit' in sys.argv, rigid='rigid' in sys.argv, lazyd=lz,
                eagerd='eagerd' in sys.argv)
    if ok and 'dump' in sys.argv:
        pre = sys.argv[sys.argv.index('dump') + 1]
        with open(pre + '.cnf', 'w') as fh:
            fh.write(f"p cnf {G.nv} {len(G.clauses)}\n")
            for c in G.clauses: fh.write(" ".join(map(str, c)) + " 0\n")
        pickle.dump(dict(H=H, terms=G.terms, clauses=G.clauses, tags=G.tags, nv=G.nv), open(pre + '.pkl', 'wb'))
        print('dumped', pre)
