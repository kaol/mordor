"""The combinatorial core of the finitely generated Cut Lemma (log §34.3m).

Generators P = {1..k} of D and Q = {1..l} of U. Cells (A, B), A ⊆ P and B ⊆ Q nonempty, stand for z = F(⋀A, ⋁B).
A cell is labelled D with a set α ⊆ P (the generators above z: nonempty, α ⊉ A since z ≰ ⋀A), or U with β ⊆ Q
(nonempty, β ⊉ B since ⋁B ≰ z). Monotonicity: (A, B) ≤ (A', B') iff A ⊇ A' and B ⊆ B' (then z ≤ z'); a D-label at
the larger cell transfers α down, a U-label at the smaller transfers β up. A labelling is a cut counterexample
seen through the generators; UNSAT proves the Cut Lemma for k×l-generated cuts in every lattice.

  python3 labelling.py KMAX LMAX"""
import sys, itertools, time
from pysat.solvers import Cadical153


def subsets(n): return [frozenset(c) for r in range(1, n + 1) for c in itertools.combinations(range(n), r)]


def solve(k, l):
    As, Bs = subsets(k), subsets(l); cells = [(A, B) for A in As for B in Bs]
    v = {}; nv = [0]
    def var(key):
        if key not in v: nv[0] += 1; v[key] = nv[0]
        return v[key]
    S = Cadical153()
    for c in cells:
        A, B = c; d = var(('D', c))
        a = [var(('a', c, i)) for i in range(k)]; b = [var(('b', c, j)) for j in range(l)]
        S.add_clause([-d] + a); S.add_clause([-d] + [-a[i] for i in A])
        S.add_clause([d] + b); S.add_clause([d] + [-b[j] for j in B])
        for x in a: S.add_clause([-x, d])
        for x in b: S.add_clause([-x, -d])
    cellset = set(cells)
    for (A, B) in cells:                                            # covering pairs c ⋖ c2 suffice (transitivity)
        ups = [(A - {i}, B) for i in A if len(A) > 1] + [(A, B | {j}) for j in range(l) if j not in B]
        for c2 in ups:
            c = (A, B)
            for i in range(k): S.add_clause([-var(('a', c2, i)), var(('a', c, i))])
            for j in range(l): S.add_clause([-var(('b', c, j)), var(('b', c2, j))])
    r = S.solve()
    return r, (S.get_model() if r else None), v


if __name__ == '__main__':
    K, L = int(sys.argv[1]), int(sys.argv[2])
    for k in range(1, K + 1):
        for l in range(1, L + 1):
            t = time.time(); r, _, _ = solve(k, l)
            print(f"k={k} l={l}: {'LABELLING EXISTS' if r else 'no labelling (UNSAT)'}  {time.time()-t:.1f}s", flush=True)
