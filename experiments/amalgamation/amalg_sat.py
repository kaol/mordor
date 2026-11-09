"""Exact search for slow joins in the R-stages (log §34.3z¹⁴⁰, Programme C).

Fixed finite lattice L. Variables: F (one-hot, monotone), A_x = a(x) = gfp_y F(x, ·), B_y = b(y) = lfp_x F(·, y),
r[k][z] (z ∈ R_k, Lean `Orbit.Rk`). Encoding:
  A_x: F(x, A_x) = A_x and every post-fixed y (y ≤ F(x, y)) satisfies y ≤ A_x;
  B_y: F(B_y, y) = B_y and every pre-fixed x (F(x, y) ≤ x) satisfies B_y ≤ x;
  r[0][z] ⟺ z = ⊥;  r[k+1][z] ⟺ ∃ g ≥ z: r[k][g] ∨ (∃ x: r[k][x] ∧ A_x = g) ∨ r[k][B_g].
Query: ∃ x, y with r[m][x], r[m][y] and ¬ r[m+e][x ∨ y]  (join excess > e at stage m).
Every model is decoded and re-simulated with rstages.stages.
  python3 amalg_sat.py (mn N | pencil K | chain N | closure K MM SEED) M EMAX
"""
import sys, itertools
from pysat.solvers import Cadical153
sys.path.insert(0, '../separation')
import separator_stages as ss
from rstages import stages, lattice

class Enc:
    def __init__(self, L, K):
        self.L = L; self.n = n = L.n; self.vars = {}; self.nv = 0; self.S = Cadical153(); le = L.le
        f = lambda x, y, v: self.v('f', x, y, v)
        for x in range(n):
            for y in range(n):
                lits = [f(x, y, v) for v in range(n)]; self.S.add_clause(lits)
                for p, q in itertools.combinations(lits, 2): self.S.add_clause([-p, -q])
        for x in range(n):
            for x2 in L.covers_up[x]:
                for y in range(n):
                    for v in range(n): self.S.add_clause([-f(x, y, v)] + [f(x2, y, w) for w in range(n) if le[v][w]])
        for y in range(n):
            for y2 in L.covers_up[y]:
                for x in range(n):
                    for v in range(n): self.S.add_clause([-f(x, y, v)] + [f(x, y2, w) for w in range(n) if le[v][w]])
        A = lambda x, g: self.v('A', x, g); B = lambda y, g: self.v('B', y, g)
        for x in range(n):
            lits = [A(x, g) for g in range(n)]; self.S.add_clause(lits)
            for p, q in itertools.combinations(lits, 2): self.S.add_clause([-p, -q])
            for g in range(n):
                self.S.add_clause([-A(x, g), f(x, g, g)])                       # fixed point
                for y in range(n):                                             # post-fixed y ≤ A_x
                    if le[y][g]: continue
                    # y ≤ F(x, y) → ¬A(x, g)
                    for v in range(n):
                        if le[y][v]: self.S.add_clause([-A(x, g), -f(x, y, v)])
        for y in range(n):
            lits = [B(y, g) for g in range(n)]; self.S.add_clause(lits)
            for p, q in itertools.combinations(lits, 2): self.S.add_clause([-p, -q])
            for g in range(n):
                self.S.add_clause([-B(y, g), f(g, y, g)])
                for x in range(n):                                             # pre-fixed x ≥ B_y
                    if le[g][x]: continue
                    for v in range(n):
                        if le[v][x]: self.S.add_clause([-B(y, g), -f(x, y, v)])
        r = lambda k, z: self.v('r', k, z)
        for z in range(n): self.S.add_clause([r(0, z)] if z == L.bot else [-r(0, z)])
        for k in range(K):
            gen = {}
            for g in range(n):
                lits = [r(k, g)]
                for x in range(n):
                    w = self.v('ra', k, x, g); self.iff_and(w, [r(k, x), A(x, g)]); lits.append(w)
                for h in range(n):
                    w = self.v('rb', k, g, h); self.iff_and(w, [B(g, h), r(k, h)]); lits.append(w)
                gv = self.v('gen', k, g); self.iff_or(gv, lits); gen[g] = gv
            for z in range(n): self.iff_or(r(k + 1, z), [gen[g] for g in range(n) if le[z][g]])
    def v(self, *key):
        if key not in self.vars: self.nv += 1; self.vars[key] = self.nv
        return self.vars[key]
    def iff_or(self, o, lits):
        for l in lits: self.S.add_clause([o, -l])
        self.S.add_clause([-o] + list(lits))
    def iff_and(self, o, lits):
        for l in lits: self.S.add_clause([-o, l])
        self.S.add_clause([o] + [-l for l in lits])
    def decode(self):
        m = set(x for x in self.S.get_model() if x > 0); n = self.n
        return [[next(v for v in range(n) if self.vars[('f', x, y, v)] in m) for y in range(n)] for x in range(n)]

def slow_join(L, M, e):
    E = Enc(L, M + e); n = L.n; sel = []
    for x in range(n):
        for y in range(x, n):
            j = L.join[x][y]; s = E.v('sel', x, y); sel.append(s)
            E.S.add_clause([-s, E.v('r', M, x)]); E.S.add_clause([-s, E.v('r', M, y)]); E.S.add_clause([-s, -E.v('r', M + e, j)])
    E.S.add_clause(sel)
    if not E.S.solve(): return None
    F = E.decode(); st = stages(L, F)
    pairs = [(x, y) for x in range(n) for y in range(n) if st[x] <= M and st[y] <= M and st[L.join[x][y]] > M + e]
    assert pairs, "model does not reproduce"
    return F, st, pairs[0]

if __name__ == '__main__':
    if sys.argv[1] == 'chain':
        L = ss.Lat([(1 << i) - 1 for i in range(int(sys.argv[2]))]); rest = sys.argv[3:]
    else:
        L, rest = lattice(sys.argv[1:])
    M, EMAX = int(rest[0]), int(rest[1])
    for e in range(1, EMAX + 1):
        r = slow_join(L, M, e)
        if r is None:
            print(f"{sys.argv[1:-2]}: |L| = {L.n}, height {L.height}: every join of two R_{M} elements is in R_{M + e} (UNSAT)", flush=True); break
        F, st, (x, y) = r
        print(f"{sys.argv[1:-2]}: |L| = {L.n}, height {L.height}: x, y ∈ R_{M} with x ∨ y ∉ R_{M + e} "
              f"(stages {st[x]}, {st[y]}, join {st[L.join[x][y]]})", flush=True)
