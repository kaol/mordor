"""Falsification of the intermediate lemmas of §34.3z¹²⁴ on all lattices with ≤ 5 elements (z3).

Lattices: C3, C4, B2, C5, M3, N5, 1⊕B2, B2⊕1 (every lattice with ≤ 5 elements), every cut D (⊥ ∈ D, ⊤ ∉ D).
F: monotone, values free.
(A) Envelope, cellwise. E(x, y) = ⋁_{h ∈ H, h ≤ x} ⋀_{c ∈ C, y ≤ c} F(h, c). Is there a cell (x, y), x ∈ D, y ∉ D,
    where E has a witness while F has none on any cell read there ((h, c), h ∈ H ∩ D, c ∈ C ∖ D, h ≤ x, y ≤ c) nor
    at (x, y)? Anchors: (A1) the brief's H_D, C_U (infinite cones: only ⊥, ⊤ in a finite lattice);
    (A2) every anchor pair H ⊆ D with ⊥ ∈ H, C ⊆ Dᶜ with ⊤ ∈ C.
    (A global form, "F witness-free ⇒ E witness-free", is vacuous here: finite lattices always have witnesses.)
(B) Interval invariance. A crossing interval [w, v] (w ∈ D, v ∉ D, w < v) whose inner cross cells
    (x ∈ [w, v] ∩ D, y ∈ [w, v] ∖ D) are witness-free: must F map [w, v] × [w, v] into [w, v]?
Reports the smallest lattice (by size) where each property fails.
"""
import itertools
from z3 import *

def lattice(name, n, covers):
    le = [[i == j for j in range(n)] for i in range(n)]
    for a, b in covers: le[a][b] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if le[i][k] and le[k][j]: le[i][j] = True
    def meet(a, b): return max((c for c in range(n) if le[c][a] and le[c][b]), key=lambda c: sum(le[d][c] for d in range(n)))
    def join(a, b): return min((c for c in range(n) if le[a][c] and le[b][c]), key=lambda c: sum(le[d][c] for d in range(n)))
    return dict(name=name, n=n, le=le, meet=meet, join=join)

LATS = [lattice('C3', 3, [(0, 1), (1, 2)]), lattice('C4', 4, [(0, 1), (1, 2), (2, 3)]),
        lattice('B2', 4, [(0, 1), (0, 2), (1, 3), (2, 3)]), lattice('C5', 5, [(0, 1), (1, 2), (2, 3), (3, 4)]),
        lattice('M3', 5, [(0, 1), (0, 2), (0, 3), (1, 4), (2, 4), (3, 4)]),
        lattice('N5', 5, [(0, 1), (1, 2), (0, 3), (2, 4), (3, 4)]),
        lattice('1+B2', 5, [(0, 1), (1, 2), (1, 3), (2, 4), (3, 4)]),
        lattice('B2+1', 5, [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)])]

def cuts(L):
    n, le = L['n'], L['le']
    for bits in itertools.product((0, 1), repeat=n):
        D = [bool(b) for b in bits]
        if not D[0] or D[n - 1]: continue
        if all(D[a] for a in range(n) for b in range(n) if le[a][b] and D[b]): yield D

def solver(L):
    n, le = L['n'], L['le']; s = Solver()
    F = [[Int(f"F{x}_{y}") for y in range(n)] for x in range(n)]
    LE = Function('LE', IntSort(), IntSort(), BoolSort())
    for a in range(n):
        for b in range(n): s.add(LE(a, b) == le[a][b])
    for x in range(n):
        for y in range(n): s.add(F[x][y] >= 0, F[x][y] < n)
    for x, x2, y, y2 in itertools.product(range(n), repeat=4):
        if le[x][x2] and le[y][y2]: s.add(LE(F[x][y], F[x2][y2]))
    return s, F, LE

def wit(LE, F, x, y): return Or(LE(F[x][y], x), LE(y, F[x][y]))

def env_term(L, F, H, C, x, y):
    """E(x, y) as a z3 Int, via exact meet/join tables over the value domain."""
    n = L['n']; meetT = [[L['meet'](a, b) for b in range(n)] for a in range(n)]; joinT = [[L['join'](a, b) for b in range(n)] for a in range(n)]
    def zmeet(a, b): return Sum([If(And(a == i, b == j), meetT[i][j], 0) for i in range(n) for j in range(n)])
    def zjoin(a, b): return Sum([If(And(a == i, b == j), joinT[i][j], 0) for i in range(n) for j in range(n)])
    acc = IntVal(0)
    for h in H:
        if not L['le'][h][x]: continue
        inner = IntVal(n - 1)
        for c in C:
            if L['le'][y][c]: inner = zmeet(inner, F[h][c])
        acc = zjoin(acc, inner)
    return acc

def test_A(L, mode):
    n, le = L['n'], L['le']
    for D in cuts(L):
        Hs = [[0]] if mode == 'A1' else [[0] + list(c) for k in range(0, n) for c in itertools.combinations([i for i in range(1, n) if D[i]], k)]
        Cs = [[n - 1]] if mode == 'A1' else [[n - 1] + list(c) for k in range(0, n) for c in itertools.combinations([i for i in range(n - 1) if not D[i]], k)]
        for H in Hs:
            for C in Cs:
                for x in range(n):
                    if not D[x]: continue
                    for y in range(n):
                        if D[y]: continue
                        s, F, LE = solver(L)
                        e = env_term(L, F, H, C, x, y)
                        s.add(Or(LE(e, x), LE(y, e)))
                        s.add(Not(wit(LE, F, x, y)))
                        for h in H:
                            for c in C:
                                if le[h][x] and le[y][c] and D[h] and not D[c]: s.add(Not(wit(LE, F, h, c)))
                        if s.check() == sat:
                            m = s.model(); Fv = [[m.eval(F[a][b]).as_long() for b in range(n)] for a in range(n)]
                            return dict(D=[i for i in range(n) if D[i]], H=H, C=C, cell=(x, y), F=Fv)
    return None

def test_B(L):
    n, le = L['n'], L['le']
    for D in cuts(L):
        for w in range(n):
            for v in range(n):
                if not (D[w] and not D[v] and le[w][v] and w != v): continue
                I = [z for z in range(n) if le[w][z] and le[z][v]]
                s, F, LE = solver(L)
                for x in I:
                    for y in I:
                        if D[x] and not D[y]: s.add(Not(wit(LE, F, x, y)))
                s.add(Or([Not(And(LE(w, F[x][y]), LE(F[x][y], v))) for x in I for y in I]))
                if s.check() == sat:
                    m = s.model()
                    bad = [(x, y, m.eval(F[x][y]).as_long()) for x in I for y in I
                           if not (le[w][m.eval(F[x][y]).as_long()] and le[m.eval(F[x][y]).as_long()][v])]
                    return dict(D=[i for i in range(n) if D[i]], interval=(w, v), escaping_cell=bad[0])
    return None

if __name__ == '__main__':
    for test in ('A1', 'A2', 'B'):
        found = None
        for L in LATS:
            r = test_B(L) if test == 'B' else test_A(L, test)
            print(f"({test}) {L['name']}: {'counterexample ' + str(r) if r else 'holds'}", flush=True)
            if r and not found: found = L['name']
        print(f"({test}) smallest failing lattice: {found}\n", flush=True)
