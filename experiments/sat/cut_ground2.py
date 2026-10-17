"""Lazy ground refutation of the cut theory C_H^≤ (log §34.3g), for larger H than cut_ground.py.

Same theory and soundness argument as cut_ground.py, but every axiom family except reflexivity, bounds and
no-witness is added lazily: after each model the violated instances of transitivity, monotonicity of F, the
down-set property, and "no chain of H+2 elements" (a clause over the H+1 consecutive strict steps of a model
chain) become clauses. Only the order matrix and D-membership are variables. UNSAT is a proof.

  python3 cut_ground2.py 5 [maxterms]"""
import sys, time
import numpy as np
from pysat.solvers import Cadical153


class Lazy:
    def __init__(self, H):
        self.H = H; self.nv = 0; self.S = Cadical153(); self.terms = []; self.depth = []; self.F = {}
        self.le_ = {}; self.d_ = {}; self.clauses = []
        self.add_term(None, 0); self.add_term(None, 0)
        self.cl([-self.le(1, 0)]); self.cl([self.d(0)]); self.cl([-self.d(1)])

    def cl(self, c): self.clauses.append(c); self.S.add_clause(c)

    def le(self, i, j):
        if (i, j) not in self.le_: self.nv += 1; self.le_[(i, j)] = self.nv
        return self.le_[(i, j)]

    def d(self, i):
        if i not in self.d_: self.nv += 1; self.d_[i] = self.nv
        return self.d_[i]

    def add_term(self, st, dep):
        i = len(self.terms); self.terms.append(st); self.depth.append(dep)
        self.cl([self.le(i, i)]); self.cl([self.le(0, i)]); self.cl([self.le(i, 1)]); self.d(i)
        if st is not None:
            s, t = st; self.F[st] = i
            self.cl([-self.d(s), self.d(t), -self.le(i, s)]); self.cl([-self.d(s), self.d(t), -self.le(t, i)])
        return i

    def model(self):
        m = self.S.get_model(); n = len(self.terms)
        L = np.zeros((n, n), dtype=bool)
        for (i, j), v in self.le_.items():
            if m[v - 1] > 0: L[i, j] = True
        Dm = np.array([m[self.d_[i] - 1] > 0 for i in range(n)])
        return L, Dm

    def repair(self, L, Dm, cap=30000):
        n = len(self.terms); added = 0
        Li = L.astype(np.int32)
        bad = np.argwhere(((Li @ Li) > 0) & ~L)                                # transitivity
        for i, k in bad[:cap]:
            j = int(np.argmax(L[i] & L[:, k])); self.cl([-self.le(int(i), j), -self.le(j, int(k)), self.le(int(i), int(k))]); added += 1
        if added: return added
        bad = np.argwhere(L & Dm[None, :] & ~Dm[:, None])                      # down-set: p ≤ q ∈ D ⇒ p ∈ D
        for p, q in bad[:cap]:
            self.cl([-self.le(int(p), int(q)), -self.d(int(q)), self.d(int(p))]); added += 1
        if added: return added
        ft = list(self.F.items())
        if ft:
            X = np.array([s for (s, t), a in ft]); Y = np.array([t for (s, t), a in ft]); A = np.array([a for _, a in ft])
            bad = np.argwhere(L[np.ix_(X, X)] & L[np.ix_(Y, Y)] & ~L[np.ix_(A, A)])   # F monotone
            for u, w in bad[:cap]:
                self.cl([-self.le(int(X[u]), int(X[w])), -self.le(int(Y[u]), int(Y[w])), self.le(int(A[u]), int(A[w]))]); added += 1
        if added: return added
        S = L & ~L.T                                                            # strict order (transitive now)
        below = S.sum(0); order = np.argsort(below, kind='stable')
        length = np.ones(n, dtype=int); pred = -np.ones(n, dtype=int)
        for q in order:
            ps = np.nonzero(S[:, q])[0]
            if len(ps):
                p = ps[np.argmax(length[ps])]; length[q] = length[p] + 1; pred[q] = p
        for q in np.argsort(-length)[:200]:
            if length[q] <= self.H + 1: break
            chain = [int(q)]
            while pred[chain[-1]] >= 0: chain.append(int(pred[chain[-1]]))
            chain = chain[::-1][-(self.H + 2):]
            c = []
            for a, b in zip(chain, chain[1:]): c += [-self.le(a, b), self.le(b, a)]
            self.cl(c); added += 1
        return added

    def solve(self):
        while True:
            if not self.S.solve(): return None
            L, Dm = self.model()
            if not self.repair(L, Dm): return L, Dm

    def expand(self, Dm, cap):
        n = len(self.terms)
        cand = sorted((self.depth[x] + self.depth[y], x, y) for x in range(n) for y in range(n)
                      if Dm[x] and not Dm[y] and (x, y) not in self.F)
        for _, x, y in cand[:cap]: self.add_term((x, y), max(self.depth[x], self.depth[y]) + 1)
        return len(cand[:cap])


def run(H, maxterms=3000, per_round=60, log=print):
    G = Lazy(H); G.add_term((0, 1), 1); t0 = time.time(); rnd = 0
    while True:
        rnd += 1; r = G.solve()
        if r is None:
            log(f"H={H}: UNSAT with {len(G.terms)} terms (max depth {max(G.depth)}), {len(G.clauses)} clauses, "
                f"{rnd} rounds, {time.time() - t0:.1f}s")
            return True, G
        if len(G.terms) >= maxterms:
            log(f"H={H}: inconclusive at {len(G.terms)} terms, {rnd} rounds, {time.time() - t0:.1f}s"); return False, G
        if not G.expand(r[1], per_round):
            log(f"H={H}: model closed under the term rule ({len(G.terms)} terms)"); return False, G
        if rnd % 5 == 0: log(f"  round {rnd}: {len(G.terms)} terms, {len(G.clauses)} clauses, {time.time() - t0:.0f}s")


def write_dimacs(G, path):
    with open(path, 'w') as fh:
        fh.write(f"p cnf {G.nv} {len(G.clauses)}\n")
        for c in G.clauses: fh.write(" ".join(map(str, c)) + " 0\n")


if __name__ == '__main__':
    run(int(sys.argv[1]) if len(sys.argv) > 1 else 5, int(sys.argv[2]) if len(sys.argv) > 2 else 3000)
