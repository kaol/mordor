"""k × ∞ cuts, reduced form, general k (§34.3z¹¹).  As kinf.py, with rows the meets m_A = ⋀_{i∈A} p_i of an antichain
p_1..p_k (free meet-semilattice: m_A ≤ m_B iff A ⊇ B; each m_A is the glb of its parts in the poset), E extra elements of
D (each below some p_i), U the complement with a top, no lattice law on U.  z3: does a monotone witness-free
F : rows × U → poset exist?  UNSAT = the reduced k × ∞ statement holds at this size.

  python3 kinf_k.py K NU NE"""
import sys, itertools
import z3

K, NU, NE = map(int, sys.argv[1:4])
rows = [frozenset(A) for n in range(1, K + 1) for A in itertools.combinations(range(K), n)]
R = len(rows); E = list(range(R, R + NE)); U = list(range(R + NE, R + NE + NU)); TOP = U[-1]
X = list(range(R)) + E + U; D = list(range(R)) + E
P = [rows.index(frozenset([i])) for i in range(K)]
le = [[z3.Bool(f"le_{i}_{j}") for j in X] for i in X]
s = z3.Solver()
for i in X:
    s.add(le[i][i], le[i][TOP])
    for j in X:
        if i != j: s.add(z3.Not(z3.And(le[i][j], le[j][i])))
        for k in X: s.add(z3.Implies(z3.And(le[i][j], le[j][k]), le[i][k]))
for a, A in enumerate(rows):
    for b, B in enumerate(rows):
        s.add(le[a][b] if A >= B else z3.Not(le[a][b]))
for e in E: s.add(z3.Or([le[e][p] for p in P]))
for u in U:
    for d in D: s.add(z3.Not(le[u][d]))
    s.add(z3.Not(z3.Or([le[u][p] for p in P])))
for a, A in enumerate(rows):                                 # m_A is the glb of {p_i : i ∈ A}
    if len(A) > 1:
        for x in X: s.add(z3.Implies(z3.And([le[x][P[i]] for i in A]), le[x][a]))
F = {(m, u): z3.Int(f"F_{m}_{u}") for m in range(R) for u in U}
for v in F.values(): s.add(v >= 0, v < len(X))
def LE(e1, e2): return z3.Or([z3.And(e1 == i, e2 == j, le[i][j]) for i in X for j in X])
for (m, u), v in F.items():
    for (m2, u2), v2 in F.items():
        if (m, u) != (m2, u2): s.add(z3.Implies(z3.And(le[m][m2], le[u][u2]), LE(v, v2)))
    s.add(z3.Not(LE(v, z3.IntVal(m))), z3.Not(LE(z3.IntVal(u), v)))
print(K, NU, NE, s.check(), flush=True)
