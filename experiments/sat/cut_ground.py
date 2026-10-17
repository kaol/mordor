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
    def __init__(self, H, nowitness=True):
        self.H = H; self.nv = 0; self.terms = []; self.depth = []; self.nowitness = nowitness
        self.clauses = []; self.S = Cadical153()
        _add = self.S.add_clause
        def add(c): self.clauses.append(list(c)); _add(c)
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
        S.add_clause([-self.g(i, H + 1)])
        for j in range(i + 1):
            for (p, q) in ((i, j), (j, i)):
                S.add_clause([-self.le(p, q), -self.d(q), self.d(p)])          # D is a down-set
                for k in range(H + 1):                                          # p < q ⇒ rank(p) < rank(q)
                    gp = self.g(p, k)
                    S.add_clause([-self.le(p, q), self.le(q, p)] + ([-gp] if gp else []) + [self.g(q, k + 1)])
        if st is not None:
            s, t = st; self.F[st] = i
            if self.nowitness:
                S.add_clause([-self.d(s), self.d(t), -self.le(i, s)])          # no witness F(x,y) ≤ x
                S.add_clause([-self.d(s), self.d(t), -self.le(t, i)])          # no witness y ≤ F(x,y)
            for (p, (s2, t2)) in [(self.F[q], q) for q in self.fterms] + [(i, st)]:
                for (a, (x1, y1), b, (x2, y2)) in ((i, st, p, (s2, t2)), (p, (s2, t2), i, st)):
                    S.add_clause([-self.le(x1, x2), -self.le(y1, y2), self.le(a, b)])   # F monotone
            self.fterms.append(st)
        return i

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
            if not len(bad): return M
            for i, k in bad[:40000]:
                j = int(np.argmax(L[i] & L[:, k]))
                self.S.add_clause([-self.le(int(i), j), -self.le(j, int(k)), self.le(int(i), int(k))])

    def expand(self, M, cap):
        n = len(self.terms); D = [self.d(i) in M for i in range(n)]
        cand = [(self.depth[x] + self.depth[y], x, y) for x in range(n) for y in range(n)
                if D[x] and not D[y] and (x, y) not in self.F]
        cand.sort()
        for _, x, y in cand[:cap]:
            self.add_term((x, y), max(self.depth[x], self.depth[y]) + 1)
        return len(cand[:cap])


def run(H, maxterms=300, per_round=40, nowitness=True):
    G = Ground(H, nowitness); G.add_term((0, 1), 1); t0 = time.time(); rnd = 0
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
        if not added:
            print(f"H={H}: SAT model closed under the term rule ({len(G.terms)} terms): a finite partial model "
                  f"with no witness among its F-terms", flush=True)
            return False, G


if __name__ == '__main__':
    H = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    run(H, cap)


def write_dimacs(G, path):
    with open(path, 'w') as fh:
        fh.write(f"p cnf {G.nv} {len(G.clauses)}\n")
        for c in G.clauses: fh.write(" ".join(map(str, c)) + " 0\n")
