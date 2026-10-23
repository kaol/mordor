"""k × ∞ cuts (D = ↓{p, q} finitely generated, Dᶜ arbitrary), reduced form: is the poset structure enough? (§34.3z¹¹)

After `Skeleton.compress` the rows of a counterexample are r = p ⊓ q, p, q.  This asks z3 for a finite partial order
on {r, p, q} ∪ E ∪ U (E: extra elements of D, each below p or q; U: the complement, with a top ⊤) and a monotone
F : {r, p, q} × U → poset with no witness (F(m, u) ≰ m, u ≰ F(m, u)), subject to the lattice laws selected below.
SAT means those laws do not suffice and a proof of the k = 2 case must use more of the lattice.

  python3 kinf.py NU NE [laws]     laws ⊆ {joinU, joinPQ, joinMU, meetUP}  (default: all)"""
import sys, itertools
import z3

NU, NE = int(sys.argv[1]), int(sys.argv[2])
LAWS = set(sys.argv[3].split(',')) if len(sys.argv) > 3 else {'joinU', 'joinPQ', 'joinMU', 'meetUP'}
r, p, q = 0, 1, 2
E = list(range(3, 3 + NE)); U = list(range(3 + NE, 3 + NE + NU)); TOP = U[-1]
X = [r, p, q] + E + U; N = len(X); D = [r, p, q] + E
le = [[z3.Bool(f"le_{i}_{j}") for j in X] for i in X]
s = z3.Solver()
for i in X:
    s.add(le[i][i])
    for j in X:
        if i != j: s.add(z3.Not(z3.And(le[i][j], le[j][i])))
        for k in X: s.add(z3.Implies(z3.And(le[i][j], le[j][k]), le[i][k]))
    s.add(le[i][TOP])
s.add(le[r][p], le[r][q], z3.Not(le[p][q]), z3.Not(le[q][p]), z3.Not(le[p][r]), z3.Not(le[q][r]))
for e in E: s.add(z3.Or(le[e][p], le[e][q]))
for u in U:
    s.add(z3.Not(le[u][p]), z3.Not(le[u][q]))           # D = ↓{p, q}: U is exactly what is not below p or q
    for d in D: s.add(z3.Not(le[u][d]))

def lub(a, b, within):
    """a ⊔ b exists and lies in `within`"""
    return z3.Or([z3.And(le[a][c], le[b][c], *[z3.Implies(z3.And(le[a][x], le[b][x]), le[c][x]) for x in X])
                  for c in within])
def glb(a, b, within):
    return z3.Or([z3.And(le[c][a], le[c][b], *[z3.Implies(z3.And(le[x][a], le[x][b]), le[x][c]) for x in X])
                  for c in within])
if 'joinU' in LAWS:
    for a, b in itertools.combinations(U, 2): s.add(lub(a, b, U))
if 'joinPQ' in LAWS: s.add(lub(p, q, U))
if 'joinMU' in LAWS:
    for a in D:
        for b in U: s.add(lub(a, b, U))
if 'meetUP' in LAWS:                                      # u ⊓ p, u ⊓ q exist (in D)
    for u in U:
        for m in (p, q): s.add(glb(u, m, D))
# r = p ⊓ q
if "noglb" not in LAWS: s.add(glb(p, q, [r]))
F = {(m, u): z3.Int(f"F_{m}_{u}") for m in (r, p, q) for u in U}
for v in F.values(): s.add(v >= 0, v < N)
def LE(a_expr, b_expr):
    return z3.Or([z3.And(a_expr == i, b_expr == j, le[i][j]) for i in X for j in X])
VIOL = []
for (m, u), v in F.items():
    for (m2, u2), v2 in F.items():
        if (m, u) != (m2, u2):
            s.add(z3.Implies(z3.And(le[m][m2], le[u][u2]), LE(v, v2)))
    if f"noW1{'rpq'[m]}" not in LAWS: s.add(z3.Not(LE(v, z3.IntVal(m))))
    if f"noW2{'rpq'[m]}" not in LAWS:
        w2 = z3.Not(LE(z3.IntVal(u), v)) if 'weakW2' not in LAWS else (v != u)   # weakW2: only no U-fixed point
        if 'floorW2' in LAWS:   # near-models: W2 waived at minimal columns of U (a truncated infinite descent)
            w2 = z3.Implies(z3.Or([le[u2][u] for u2 in U if u2 != u]), w2)
        if 'oneviol' in LAWS: VIOL.append(z3.If(w2, 0, 1))
        else: s.add(w2)
if 'oneviol' in LAWS: s.add(z3.Sum(VIOL) == 1)
isD = lambda v: z3.Or([v == d for d in D])
if 'ends' in LAWS:   # descent endpoints that DCC guarantees: t ∈ T_m ∩ S_m for m = p, q
    for m in (p, q):
        s.add(z3.Or([z3.And(isD(F[(m, u)]), LE(F[(m, u)], z3.IntVal(u))) for u in U]))
r_ = s.check()
print(NU, NE, sorted(LAWS), r_, flush=True)
if r_ == z3.sat:
    M = s.model(); name = {r: 'r', p: 'p', q: 'q', **{e: f"e{i}" for i, e in enumerate(E)},
                           **{u: (f"u{i}" if u != TOP else '⊤') for i, u in enumerate(U)}}
    print(' order:', [(name[i], name[j]) for i in X for j in X if i != j and z3.is_true(M[le[i][j]])
                      and not any(k not in (i, j) and z3.is_true(M[le[i][k]]) and z3.is_true(M[le[k][j]]) for k in X)])
    print(' F:', {f"{name[m]},{name[u]}": name[M[v].as_long()] for (m, u), v in F.items()})
