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
ORB = {(m, u): z3.Bool(f"orb_{m}_{u}") for m in (r, p, q) for u in U}   # superset of the f_m-orbit of ⊤
for m in (r, p, q):
    s.add(ORB[(m, TOP)])
    for u in U:
        for v in U: s.add(z3.Implies(z3.And(ORB[(m, u)], F[(m, u)] == v), ORB[(m, v)]))
for (m, u), v in F.items():
    for (m2, u2), v2 in F.items():
        if (m, u) != (m2, u2):
            s.add(z3.Implies(z3.And(le[m][m2], le[u][u2]), LE(v, v2)))
    if f"noW1{'rpq'[m]}" not in LAWS: s.add(z3.Not(LE(v, z3.IntVal(m))))
    if f"noW2{'rpq'[m]}" not in LAWS:
        w2 = z3.Not(LE(z3.IntVal(u), v)) if 'weakW2' not in LAWS else (v != u)   # weakW2: only no U-fixed point
        if 'W2topOnly' in LAWS and u != TOP: w2 = z3.BoolVal(True)
        pol = next((x.split('=')[1] for x in LAWS if x.startswith(f"pol{'rpq'[m]}=")), None)
        if pol == 'top' and u != TOP: w2 = z3.BoolVal(True)
        if pol == 'orb' and u != TOP: w2 = z3.Implies(ORB[(m, u)], w2)
        if pol == 'orbpq' and u != TOP: w2 = z3.Implies(z3.Or(ORB[(p, u)], ORB[(q, u)]), w2)
        if 'W2orb' in LAWS and u != TOP:
            w2 = z3.Implies(ORB[(m, u)], w2)
        if 'W2lvl2' in LAWS and u != TOP:   # W2 only at ⊤, F(m, ⊤), F(m', F(m, ⊤)) (when those are columns)
            lvl1 = [F[(m2, TOP)] == u for m2 in (r, p, q)]
            lvl2 = [z3.And(F[(m2, TOP)] == u1, F[(m3, u1)] == u) for m2 in (r, p, q) for m3 in (r, p, q) for u1 in U]
            w2 = z3.Implies(z3.Or(lvl1 + lvl2), w2)
        if 'W2lvl1' in LAWS and u != TOP:   # W2 only at ⊤ and at the columns F(m, ⊤)
            w2 = z3.Implies(z3.Or([F[(m2, TOP)] == u for m2 in (r, p, q)]), w2)
        if 'floorW2' in LAWS:   # near-models: W2 waived at minimal columns of U (a truncated infinite descent)
            w2 = z3.Implies(z3.Or([le[u2][u] for u2 in U if u2 != u]), w2)
        if 'oneviol' in LAWS: VIOL.append(z3.If(w2, 0, 1))
        else: s.add(w2)
if 'oneviol' in LAWS: s.add(z3.Sum(VIOL) == 1)
isD = lambda v: z3.Or([v == d for d in D])
if 'ends' in LAWS:   # descent endpoints that DCC guarantees: t ∈ T_m ∩ S_m for m = p, q
    for m in (p, q):
        s.add(z3.Or([z3.And(isD(F[(m, u)]), LE(F[(m, u)], z3.IntVal(u))) for u in U]))
isQ = lambda v: LE(v, z3.IntVal(q)); isP = lambda v: LE(v, z3.IntVal(p))
if 'lemmas' in LAWS:   # consequences of DCC proved in §34.3z¹¹ (items 1-4), valid in every real instance
    for u in U:
        Su = {m: LE(F[(m, u)], z3.IntVal(u)) for m in (p, q)}
        if 'noL3' not in LAWS: s.add(z3.Not(z3.And(isD(F[(p, u)]), Su[q])), z3.Not(z3.And(isD(F[(q, u)]), Su[p])))   # T_p∩S_q, T_q∩S_p
        if 'noL4' not in LAWS: s.add(z3.Not(z3.And(isQ(F[(r, u)]), Su[q])), z3.Not(z3.And(isP(F[(r, u)]), Su[p])))   # T_r^q∩S_q, T_r^p∩S_p
if 'lemX' in LAWS:   # Lemma X: s ∈ S_q, h(s) = v ∈ U ⇒ v ∉ T_r^q;  s ∈ S_p, h(s) = v ∈ U ⇒ v ∉ T_r^p
    for u in U:
        for v in U:
            s.add(z3.Not(z3.And(LE(F[(q, u)], z3.IntVal(u)), F[(r, u)] == v, isQ(F[(r, v)]))))
            s.add(z3.Not(z3.And(LE(F[(p, u)], z3.IntVal(u)), F[(r, u)] == v, isP(F[(r, v)]))))
if 'endsBelow' in LAWS:   # Kleene of f_m from ⊤ ends at e_m ≤ F(m, ⊤) with F(m, e_m) ∈ D and F(m, e_m) ≤ e_m
    for m in (r, p, q):
        s.add(z3.Or([z3.And(isD(F[(m, u)]), LE(F[(m, u)], z3.IntVal(u)), LE(z3.IntVal(u), F[(m, TOP)])) for u in U]))
if 'notC' in LAWS:   # negation of candidate: some u ∈ T_r^q has F(q,u) = v ∈ U with v ∈ T_r^p
    s.add(z3.Or([z3.And(isQ(F[(r, u)]), F[(q, u)] == v, isP(F[(r, v)])) for u in U for v in U]))
if 'notC2' in LAWS:  # weaker: some u ∈ T_r^q has F(q,u) ∈ T_q
    s.add(z3.Or([z3.And(isQ(F[(r, u)]), F[(q, u)] == v, isD(F[(q, v)])) for u in U for v in U]))
if 'meetR' in LAWS:   # boundary normal form: row r = glb(row p, row q)
    for u in U:
        for c in X:
            s.add(z3.Implies(F[(r, u)] == c, z3.And([z3.Implies(z3.And(LE(z3.IntVal(x), F[(p, u)]), LE(z3.IntVal(x), F[(q, u)])), le[x][c]) for x in X])))
if 'joinC' in LAWS:   # boundary normal form: rows p, q are joins of their values at minimal columns below
    for m in (p, q):
        for u in U:
            mins = [(v, z3.And(le[v][u], *[z3.Not(le[w][v]) for w in U if w != v])) for v in U]
            for x in X:   # every upper bound of {F(m,v) : v minimal ≤ u} is above F(m,u)
                s.add(z3.Implies(z3.And([z3.Implies(mv, LE(F[(m, v)], z3.IntVal(x))) for v, mv in mins]), LE(F[(m, u)], z3.IntVal(x))))
if 'notA1' in LAWS or 'A1prem' in LAWS:   # ChatGPT's A1, negated: the last U-term c_n of the r-orbit of ⊤ is q-type, and the
    # exact q-orbit o_0 = c_n, o_{i+1} = F(q, o_i) leaves T_r^q while still in U (i.e. reaches A_r or T_r^p)
    cn = z3.Int('cn'); s.add(z3.Or([cn == u for u in U]))
    Fat = lambda m, e: z3.Sum([z3.If(e == u, F[(m, u)], 0) for u in U])
    s.add(z3.Or([z3.And(cn == u, ORB[(r, u)]) for u in U]), isQ(Fat(r, cn)))
    # exact r-orbit membership of cn: demand an explicit chain ⊤ = c_0 → … → c_t = cn under F(r, ·)
    T = len(U); cs = [z3.Int(f'c{i}') for i in range(T + 1)]; tlen = z3.Int('tlen')
    s.add(cs[0] == TOP, tlen >= 0, tlen <= T)
    for i in range(T):
        s.add(z3.Implies(i < tlen, cs[i + 1] == Fat(r, cs[i])))
    s.add(z3.Or([z3.And(tlen == i, cs[i] == cn) for i in range(T + 1)]))
    for i in range(T + 1): s.add(z3.Or([cs[i] == u for u in U]))
    os_ = [z3.Int(f'o{i}') for i in range(T + 1)]; olen = z3.Int('olen')
    s.add(os_[0] == cn, olen >= 1, olen <= T)
    for i in range(T):
        s.add(z3.Implies(i < olen, z3.And(os_[i + 1] == Fat(q, os_[i]), isQ(Fat(r, os_[i])))))
    for i in range(T + 1): s.add(z3.Or([os_[i] == u for u in U]))
    if 'notA1' in LAWS: s.add(z3.Or([z3.And(olen == i, z3.Not(isQ(Fat(r, os_[i])))) for i in range(1, T + 1)]))
    else: pass
if 'Ztop' in LAWS:     # item 6: a minimal instance has Z = S_p ∩ S_q = {⊤}
    for u in U:
        if u != TOP: s.add(z3.Not(z3.And(LE(F[(p, u)], z3.IntVal(u)), LE(F[(q, u)], z3.IntVal(u)))))
r_ = s.check()
print(NU, NE, sorted(LAWS), r_, flush=True)
if r_ == z3.sat:
    M = s.model(); name = {r: 'r', p: 'p', q: 'q', **{e: f"e{i}" for i, e in enumerate(E)},
                           **{u: (f"u{i}" if u != TOP else '⊤') for i, u in enumerate(U)}}
    if "quiet" in LAWS: sys.exit(0)
    print(' order:', [(name[i], name[j]) for i in X for j in X if i != j and z3.is_true(M[le[i][j]])
                      and not any(k not in (i, j) and z3.is_true(M[le[i][k]]) and z3.is_true(M[le[k][j]]) for k in X)])
    print(' F:', {f"{name[m]},{name[u]}": name[M[v].as_long()] for (m, u), v in F.items()})
