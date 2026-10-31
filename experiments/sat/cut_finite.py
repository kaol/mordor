"""Finite models of the cut theory C_H^≤ (log §34.3g): search for a bounded poset of n elements with no chain of
H + 2 elements, a monotone F, a down-set D with ⊥ ∈ D, ⊤ ∉ D and no witness (x ∈ D, y ∉ D, F(x,y) ≤ x or
y ≤ F(x,y)). An UNSAT answer for every n says nothing beyond n; a model shows that the poset theory C_H^≤ is
consistent, so the ground refutation of cut_ground.py cannot terminate at that H (lattice axioms are needed).

Encoding: elements 0 = ⊥ < … < n-1 = ⊤ numbered by a linear extension (le(i,j) ⇒ i ≤ j); F one-hot f(i,j,k)
with u(i,j,k) ⟺ F(i,j) ≤ k; rank variables g(i,k) ⟺ rank(i) ≥ k as in cut_ground.py; WLOG F(⊥,⊤) ∉ D by
self-duality (§33.3). --lattice adds binary joins and meets (one-hot, with their universal properties).

  python3 cut_finite.py H n_min n_max [--lattice] [--box]
--box asserts no-witness only for x < y (the box Cut Lemma, §34.3z¹⁵): a model is a finite box counterexample."""
import sys, itertools, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc, EncType


class Finite:
    def __init__(self, n, H, lattice=False, wlog=True, nowit=(True, True), boundary=False, box=False):
        self.n, self.H = n, H; self.nv = 0; self.vars = {}; self.S = Cadical153(); self.ncl = 0
        R = range(n); add = self.add
        le, f, u, g, d = self.le, self.f, self.u, self.g, self.d
        for i in R:
            add([le(i, i)]); add([le(0, i)]); add([le(i, n - 1)])
            for j in R:
                if j < i: add([-le(i, j)])                                   # linear extension
        for i, j, k in itertools.product(R, R, R):
            if i < j < k: add([-le(i, j), -le(j, k), le(i, k)])
        for i, j in itertools.product(R, R):                                 # rank: p < q ⇒ r(p) < r(q)
            if i < j:
                for k in range(H + 1):
                    add([-le(i, j)] + ([-g(i, k)] if k else []) + ([g(j, k + 1)] if k < H else []))
        for i, j in itertools.product(R, R):                                 # F total function
            lits = [f(i, j, k) for k in R]; add(lits)
            for cl in CardEnc.atmost(lits, 1, top_id=self.nv, encoding=EncType.seqcounter).clauses:
                self.nv = max(self.nv, max(abs(x) for x in cl)); add(cl)
            for k in R:                                                      # u(i,j,k) ⟺ ∃m f(i,j,m) ∧ m ≤ k
                for m in R:
                    add([-f(i, j, m), -le(m, k), u(i, j, k)]); add([-f(i, j, m), le(m, k), -u(i, j, k)])
        for i, j, i2, j2 in itertools.product(R, R, R, R):                   # F monotone (generating steps)
            if (i, j) != (i2, j2) and i <= i2 and j <= j2 and (i == i2 or j == j2):
                for k in R:
                    add([-le(i, i2), -le(j, j2), -u(i2, j2, k), u(i, j, k)])
        for i, j in itertools.product(R, R):                                 # D down-set
            if i < j: add([-le(i, j), -d(j), d(i)])
        add([d(0)]); add([-d(n - 1)])
        if boundary:                                                         # no witness on the boundary lines only
            mx, mu = self.boundary_vars()
        for x, y in itertools.product(R, R):                                 # no witness
            guards = [[-d(x), d(y)] + ([-le(x, y)] if box else [])] if not boundary else [[-mx[x], d(y)], [-mu[y], -d(x)]]
            for gd in guards:
                if nowit[0]: add(gd + [-u(x, y, x)])
                if nowit[1]:
                    for m in R: add(gd + [-f(x, y, m), -le(y, m)])
        if wlog:
            for m in R: add([-f(0, n - 1, m), -d(m)])
        if lattice: self.lattice()

    def boundary_vars(self):
        """mx[x] ⟺ x maximal in D; mu[y] ⟺ y minimal in U = complement of D (Boundary Witness Conjecture, §34.3m)."""
        n, R, le, d, add = self.n, range(self.n), self.le, self.d, self.add
        mx, mu = {}, {}
        for x in R:
            mx[x] = self.var(('mx', x)); mu[x] = self.var(('mu', x))
            above = []; below = []
            for z in R:
                if z == x: continue
                ta = self.var(('ta', x, z)); add([-ta, le(x, z)]); add([-ta, d(z)]); add([ta, -le(x, z), -d(z)]); above.append(ta)
                tb = self.var(('tb', x, z)); add([-tb, le(z, x)]); add([-tb, -d(z)]); add([tb, -le(z, x), d(z)]); below.append(tb)
            add([-mx[x], d(x)]); add([-mu[x], -d(x)])
            for t in above: add([-mx[x], -t])
            for t in below: add([-mu[x], -t])
            add([-d(x)] + above + [mx[x]]); add([d(x)] + below + [mu[x]])
        return mx, mu

    def var(self, key):
        if key not in self.vars: self.nv += 1; self.vars[key] = self.nv
        return self.vars[key]

    def le(self, i, j): return self.var(('le', i, j))
    def f(self, i, j, k): return self.var(('f', i, j, k))
    def u(self, i, j, k): return self.var(('u', i, j, k))
    def g(self, i, k): return self.var(('g', i, k))
    def d(self, i): return self.var(('d', i))

    def add(self, c):
        self.ncl += 1; self.S.add_clause(c)

    def lattice(self):
        """Every pair has a least upper bound and a greatest lower bound."""
        n, R, le, add = self.n, range(self.n), self.le, self.add
        for (op, a, b) in (('j', 1, 0), ('m', 0, 1)):
            for i, j in itertools.product(R, R):
                if i >= j: continue
                lits = [self.var((op, i, j, k)) for k in R]; add(lits)
                for k in R:
                    v = self.var((op, i, j, k))
                    # k is a bound of i, j; every bound l of i, j is beyond k
                    up = (lambda x, y: le(x, y)) if op == 'j' else (lambda x, y: le(y, x))
                    add([-v, up(i, k)]); add([-v, up(j, k)])
                    for l in R: add([-v, -up(i, l), -up(j, l), up(k, l)])

    def model(self):
        if not self.S.solve(): return None
        M = set(l for l in self.S.get_model() if l > 0); n = self.n; R = range(n)
        le = [[self.le(i, j) in M for j in R] for i in R]
        F = [[next(k for k in R if self.f(i, j, k) in M) for j in R] for i in R]
        D = [i for i in R if self.d(i) in M]
        return le, F, D


def check(le, F, D):
    """Independent check of a model (pure Python)."""
    n = len(le); R = range(n)
    assert all(le[i][i] for i in R)
    assert all(not (le[i][j] and le[j][i]) or i == j for i in R for j in R)
    assert all(not (le[i][j] and le[j][k]) or le[i][k] for i in R for j in R for k in R)
    assert all(le[0][i] and le[i][n - 1] for i in R)
    assert all(not (le[i][i2] and le[j][j2]) or le[F[i][j]][F[i2][j2]] for i in R for j in R for i2 in R for j2 in R)
    Ds = set(D); assert 0 in Ds and n - 1 not in Ds
    assert all(not (le[i][j] and j in Ds) or i in Ds for i in R for j in R)
    for x in Ds:
        for y in set(R) - Ds:
            assert not le[F[x][y]][x] and not le[y][F[x][y]], (x, y)
    h = [0] * n                                                              # longest chain ending at i
    for j in R: h[j] = max([h[i] + 1 for i in R if i < j and le[i][j]], default=0)
    return max(h)


if __name__ == '__main__':
    H, lo, hi = map(int, sys.argv[1:4]); lat = '--lattice' in sys.argv; box = '--box' in sys.argv
    for n in range(lo, hi + 1):
        t = time.time(); P = Finite(n, H, lattice=lat, box=box); r = P.model()
        print(f"H={H} n={n}{' lattice' if lat else ''}{' box' if box else ''}: {'UNSAT' if r is None else 'MODEL'} "
              f"({P.nv} vars, {P.ncl} clauses, {time.time() - t:.1f}s)", flush=True)
        if r is not None:
            le, F, D = r; print("  height", check(le, F, D)); print("  le", le); print("  F", F); print("  D", D)
            break
