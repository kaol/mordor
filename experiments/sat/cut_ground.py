"""Model-guided ground refutation of the cut theory C_H^≤ (log §31.5, §34.3f).

Universal theory, poset version: a bounded poset with no chain of H+2 elements, a monotone F, a down-set D with
⊥ ∈ D, ⊤ ∉ D, and no witness: for x ∈ D, y ∉ D, F(x,y) ≰ x and y ≰ F(x,y). If it is unsatisfiable, the Cut Lemma
holds on every complete lattice of edge-height ≤ H (lattices are posets; the theory never uses ∨, ∧).

Ground instances over a finite set of F-terms built from ⊥, ⊤ (soundness: every clause is an instance of a true
axiom, so UNSAT is a proof). The order is a Boolean matrix le(s,t); reflexivity and bounds are added eagerly,
transitivity lazily (violations of the current model become clauses); the height bound is a rank function
r : terms → {0..H}, strictly increasing along <. After each transitively closed model, new terms F(x,y) are added
for model pairs x ∈ D, y ∉ D (shallowest first). Ends with UNSAT (a proof) or at the term cap (inconclusive).

  python3 cut_ground.py 3        # expected: UNSAT (the Lean proof Height3.lean uses 7 F-terms)
  python3 cut_ground.py 4 400"""
import sys, itertools, time
import numpy as np
from pysat.solvers import Cadical153


class Ground:
    def __init__(self, H, nowitness=True, ih=False, lazy_rank=False, stream=None, room=False, lazy_ih=False):
        self.H = H; self.nv = 0; self.terms = []; self.depth = []; self.nowitness = nowitness; self.lazy_ih = lazy_ih
        self.ih = ih; self.diag = set(); self.lazy_rank = lazy_rank; self.room = room
        self.clauses = []; self.nclauses = 0; self.S = Cadical153(); self.stream = open(stream, 'w') if stream else None
        _add = self.S.add_clause
        def add(c):
            self.nclauses += 1
            if self.stream: self.stream.write(" ".join(map(str, c)) + " 0\n")
            else: self.clauses.append(list(c))
            _add(c)
        self.S.add_clause = add
        self.F = {}; self.le_ = {}; self.d_ = {}; self.g_ = {}; self.fterms = []
        self.add_term(None, 0); self.add_term(None, 0)                     # 0 = ⊥, 1 = ⊤
        self.S.add_clause([-self.le(1, 0)]); self.S.add_clause([self.d(0)]); self.S.add_clause([-self.d(1)])

    def var(self):
        self.nv += 1; return self.nv

    def le(self, i, j):
        if (i, j) not in self.le_: self.le_[(i, j)] = self.var()
        return self.le_[(i, j)]

    def d(self, i):
        if i not in self.d_: self.d_[i] = self.var()
        return self.d_[i]

    def g(self, i, k):                                                     # rank(i) ≥ k
        if k == 0: return None
        if (i, k) not in self.g_: self.g_[(i, k)] = self.var()
        return self.g_[(i, k)]

    def add_term(self, st, dep):
        i = len(self.terms); self.terms.append(st); self.depth.append(dep)
        S, H = self.S, self.H
        S.add_clause([self.le(i, i)]); S.add_clause([self.le(0, i)]); S.add_clause([self.le(i, 1)])
        if not self.lazy_rank: S.add_clause([-self.g(i, H + 1)])
        for j in range(i + 1):
            for (p, q) in ((i, j), (j, i)):
                S.add_clause([-self.le(p, q), -self.d(q), self.d(p)])          # D is a down-set
                for k in (range(H + 1) if not self.lazy_rank else ()):          # p < q ⇒ rank(p) < rank(q)
                    gp = self.g(p, k)
                    S.add_clause([-self.le(p, q), self.le(q, p)] + ([-gp] if gp else []) + [self.g(q, k + 1)])
        if st is not None:
            s, t = st; self.F[st] = i
            if self.nowitness and s != t:
                S.add_clause([-self.d(s), self.d(t), -self.le(i, s)])          # no witness F(x,y) ≤ x
                S.add_clause([-self.d(s), self.d(t), -self.le(t, i)])          # no witness y ≤ F(x,y)
            for (p, (s2, t2)) in [(self.F[q], q) for q in self.fterms] + [(i, st)]:
                for (a, (x1, y1), b, (x2, y2)) in ((i, st, p, (s2, t2)), (p, (s2, t2), i, st)):
                    S.add_clause([-self.le(x1, x2), -self.le(y1, y2), self.le(a, b)])   # F monotone
            self.fterms.append(st)
        return i

    def add_ih(self, i):
        """Height induction (sound if the Cut Lemma holds at height H - 1): with δ = F(i, i),
        (A) i ∈ D, i ≤ δ ⇒ i = ⊥   ([i, ⊤] would be an F-stable cut of smaller height);
        (B) i ∉ D, δ ≤ i ⇒ i = ⊤   ([⊥, i] likewise)."""
        if not self.ih or i in self.diag or (i, i) in self.F: return
        dg = self.add_term((i, i), self.depth[i] + 1); self.diag.add(dg)
        self.S.add_clause([-self.d(i), -self.le(i, dg), self.le(i, 0)])
        self.S.add_clause([self.d(i), -self.le(dg, i), self.le(1, i)])

    def solve(self):
        while True:
            if not self.S.solve(): return None
            model = self.S.get_model(); M = set(l for l in model if l > 0)
            n = len(self.terms)
            L = np.zeros((n, n), dtype=bool)
            for (i, j), v in self.le_.items():
                if i < n and j < n and model[v - 1] > 0: L[i, j] = True
            # violations i ≤ j ≤ k, i ≰ k: (L·L) ∧ ¬L, with one middle j per (i, k)
            Li = L.astype(np.int32)
            bad = np.argwhere(((Li @ Li) > 0) & ~L)
            for i, k in bad[:40000]:
                j = int(np.argmax(L[i] & L[:, k]))
                self.S.add_clause([-self.le(int(i), j), -self.le(j, int(k)), self.le(int(i), int(k))])
            if len(bad): continue
            if self.lazy_rank and self.chains(L): continue
            if self.lazy_ih and self.ih_violations(L, M): continue
            self.L = L
            return M

    def ih_violations(self, L, M, cap=2000):
        """Lazy height induction without new terms (sound given the Cut Lemma at height H - 1, §34.3g):
        (A) x ∈ D, x ≠ ⊥, s, t ≤ x ≤ F(s,t) is impossible, since then x ≤ F(x,x) and [x, ⊤] is a smaller counterexample;
        (B) x ∉ D, x ≠ ⊤, x ≤ s, t and F(s,t) ≤ x likewise ([⊥, x])."""
        n = len(self.terms); D = np.array([self.d(i) in M for i in range(n)])
        added = 0
        for (s, t), a in self.F.items():
            if added >= cap: break
            A = np.nonzero(D & L[s] & L[t] & L[:, a] & ~L[:, 0])[0]           # s ≤ x, t ≤ x, x ≤ a, x ∈ D, x ≰ ⊥
            for x in A[:4]:
                x = int(x); self.S.add_clause([-self.d(x), self.le(x, 0), -self.le(s, x), -self.le(t, x), -self.le(x, a)])
                added += 1
            B = np.nonzero(~D & L[:, s] & L[:, t] & L[a] & ~L[1])[0]          # x ≤ s, x ≤ t, a ≤ x, x ∉ D, ⊤ ≰ x
            for x in B[:4]:
                x = int(x); self.S.add_clause([self.d(x), self.le(1, x), -self.le(x, s), -self.le(x, t), -self.le(a, x)])
                added += 1
        return added

    def chains(self, L, cap=400):
        """Lazy height bound: for model chains of more than H + 1 elements add the clause 'some step of this chain is
        not strict' (an instance of: no chain of H + 2 elements)."""
        n = len(L); S = L & ~L.T
        order = np.argsort(S.sum(0), kind='stable')
        length = np.ones(n, dtype=int); pred = -np.ones(n, dtype=int)
        for q in order:
            ps = np.nonzero(S[:, q])[0]
            if len(ps): p = ps[np.argmax(length[ps])]; length[q] = length[p] + 1; pred[q] = p
        added = 0
        for q in np.argsort(-length)[:cap]:
            if length[q] <= self.H + 1: break
            ch = [int(q)]
            while pred[ch[-1]] >= 0: ch.append(int(pred[ch[-1]]))
            ch = ch[::-1][-(self.H + 2):]
            c = []
            for a, b in zip(ch, ch[1:]): c += [-self.le(a, b), self.le(b, a)]
            self.S.add_clause(c); added += 1
        return added

    def fit(self, M, cand):
        """Tightness of each candidate F(x,y) in the current model: the number of existing elements z that F(x,y)
        could equal (above every F(s,t) with s ≤ x, t ≤ y; below every F(s,t) with x ≤ s, y ≤ t; z ≰ x; y ≰ z), plus 1
        if a fresh element fits under the height bound. 0 means the term refutes the model."""
        n = len(self.terms); L = self.L; X = np.array([c[1] for c in cand]); Y = np.array([c[2] for c in cand])
        ST = np.array([(s, t, a) for (s, t), a in self.F.items()]); s_, t_, a_ = ST[:, 0], ST[:, 1], ST[:, 2]
        lo = (L[s_][:, X] & L[t_][:, Y]).T.astype(np.float32)                    # cand × m
        hi = (L[X][:, s_] & L[Y][:, t_]).astype(np.float32)
        nab = (~L[a_]).astype(np.float32); nbe = (~L[:, a_].T).astype(np.float32)  # m × n: a ≰ z, z ≰ b
        ok = ((lo @ nab) == 0) & ((hi @ nbe) == 0) & ~L[:, X].T & ~L[Y]          # cand × n
        S = L & ~L.T; up = np.zeros(n, int); dn = np.zeros(n, int)               # longest chains below / above
        order = np.argsort(S.sum(0), kind='stable')
        for q in order:
            ps = np.nonzero(S[:, q])[0]
            if len(ps): up[q] = up[ps].max() + 1
        for q in order[::-1]:
            ps = np.nonzero(S[q])[0]
            if len(ps): dn[q] = dn[ps].max() + 1
        lo_b, hi_b = lo.astype(bool), hi.astype(bool)
        fresh = [(up[a_[lo_b[i]]].max(initial=0) + 1) + (dn[a_[hi_b[i]]].max(initial=0) + 1) <= self.H
                 for i in range(len(cand))]
        return ok.sum(1) + np.array(fresh, dtype=int)

    def expand(self, M, cap):
        n = len(self.terms); D = [self.d(i) in M for i in range(n)]
        if self.room == 'fit':
            cand = [(0, x, y) for x in range(n) for y in range(n)
                    if D[x] and not D[y] and (x, y) not in self.F and x not in self.diag and y not in self.diag]
            if not cand: return 0
            fs = self.fit(M, cand)
            cand = sorted(((int(fs[i]), self.depth[x] + self.depth[y], x, y) for i, (_, x, y) in enumerate(cand)))
            for _, _, x, y in cand[:cap]:
                self.add_ih(self.add_term((x, y), max(self.depth[x], self.depth[y]) + 1))
            return len(cand[:cap])
        if self.room:                                                  # model rank (from the rank variables)
            rk = [sum(1 for k in range(1, self.H + 1) if self.g_.get((i, k)) in M) for i in range(n)]
            key = lambda x, y: (self.depth[x] + self.depth[y], rk[y] - rk[x])
        else:
            key = lambda x, y: self.depth[x] + self.depth[y]
        cand = [(key(x, y), x, y) for x in range(n) for y in range(n)
                if D[x] and not D[y] and (x, y) not in self.F and x not in self.diag and y not in self.diag]
        cand.sort()
        for _, x, y in cand[:cap]:
            self.add_ih(self.add_term((x, y), max(self.depth[x], self.depth[y]) + 1))
        return len(cand[:cap])


def run(H, maxterms=300, per_round=40, nowitness=True, ih=False, lazy_rank=False, stream=None, wlog=False, room=False,
        lazy_ih=False):
    G = Ground(H, nowitness, ih, lazy_rank, stream, room, lazy_ih); c = G.add_term((0, 1), 1); G.add_ih(c); t0 = time.time(); rnd = 0
    if wlog: G.S.add_clause([-G.d(c)])         # WLOG F(⊥,⊤) ∉ D: the cut theory is self-dual (§33.3, §22.1)
    while True:
        rnd += 1
        M = G.solve()
        if M is None:
            print(f"H={H}: UNSAT with {len(G.terms)} terms (max depth {max(G.depth)}) after {rnd} rounds, "
                  f"{time.time() - t0:.1f}s: the Cut Lemma holds at edge-height ≤ {H}", flush=True)
            return True, G
        if len(G.terms) >= maxterms:
            print(f"H={H}: inconclusive, still SAT at {len(G.terms)} terms after {rnd} rounds", flush=True)
            return False, G
        added = G.expand(M, per_round)
        if rnd % 25 == 0:
            print(f"  H={H} round {rnd}: {len(G.terms)} terms, {G.nv} vars, {time.time() - t0:.0f}s", flush=True)
        if not added:
            print(f"H={H}: SAT model closed under the term rule ({len(G.terms)} terms): a finite partial model "
                  f"with no witness among its F-terms", flush=True)
            return False, G


if __name__ == '__main__':
    H = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    run(H, cap)


def write_dimacs(G, path):
    if G.stream:
        G.stream.close()
        with open(path, 'w') as fh, open(G.stream.name) as body:
            fh.write(f"p cnf {G.nv} {G.nclauses}\n")
            for line in body: fh.write(line)
        return
    with open(path, 'w') as fh:
        fh.write(f"p cnf {G.nv} {len(G.clauses)}\n")
        for c in G.clauses: fh.write(" ".join(map(str, c)) + " 0\n")
