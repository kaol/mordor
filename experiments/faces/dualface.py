"""Full m_J-orbit, hybrid faces and dual faces for the Hamiltonian 3-cycle (log §34.3z⁹²), z3.

Strict crossing triple; rows p_i, pairwise meets, m123 (= m_J), anchors c_i. Anchor orbits from ⊤ of lengths n_i
(w_i last outside point, e_i = F(c_i, w_i) ≤ p_{σ(i)}, e_i ≰ p_i; σ = 1→2→3→1; extra J-labels allowed but the
Lean dichotomy forbids them, so K_i = {σ(i)} exactly is imposed). Minimal dependence: y_i = ⋀_{j≠i} w_j ∉ D
(codim-one faces), v_J = ⋀ w ∈ D. The full m_J-orbit q_0 = ⊤, q_{r+1} = F(m_J, q_r), q_1..q_{N-1} ∉ D, q_N ∈ D.
Hybrid columns q_r ⊓ y_i (r = 1..N-1), dual faces u_ij = y_i ⊔ y_j, z = ⋀ u_ij. All named elements are columns;
F on every row × column, monotone; no witness at columns that are outside D (conditional). Variants: dual values
h(u_ij) required in D or not."""
import itertools, sys
from z3 import *
SIG = {1: 2, 2: 3, 3: 1}
def run(n, N, dual_in_D=False):
    I = [1, 2, 3]; P = [f"p{i}" for i in I]
    M = {'m12': ['p1', 'p2'], 'm13': ['p1', 'p3'], 'm23': ['p2', 'p3'], 'mJ': P}
    C = {'c1': ['m12', 'm13'], 'c2': ['m12', 'm23'], 'c3': ['m13', 'm23']}
    rows = P + list(M) + list(C)
    orb = {i: ['top'] + [f"o{i}_{k}" for k in range(1, n[i] + 1)] for i in I}
    w = {i: orb[i][-1] for i in I}
    q = ['top'] + [f"q{r}" for r in range(1, N)]
    y = {i: f"y{i}" for i in I}
    hyb = {(r, i): f"h{r}_{i}" for r in range(1, N) for i in I}
    u = {(i, j): f"u{i}{j}" for i, j in itertools.combinations(I, 2)}
    cols = ['top'] + [x for i in I for x in orb[i][1:]] + q[1:] + list(y.values()) + list(hyb.values()) + list(u.values()) + ['z', 'vJ']
    cols = list(dict.fromkeys(cols))
    val = {(a, c): f"F[{a},{c}]" for a in rows for c in cols}
    E = list(dict.fromkeys(['bot'] + rows + cols + list(val.values())))
    s = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    for a in E:
        s.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            for c in E: s.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
    inD = {a: Or([le[a, x] for x in P]) for a in E}
    for a, b in itertools.permutations(P, 2): s.add(Not(le[a, b]))
    def glb(zz, xs): s.add([le[zz, x] for x in xs]); s.add([Implies(And([le[t, x] for x in xs]), le[t, zz]) for t in E])
    def lub(zz, xs): s.add([le[x, zz] for x in xs]); s.add([Implies(And([le[x, t] for x in xs]), le[zz, t]) for t in E])
    for k, v in M.items(): glb(k, v)
    for k, v in C.items(): lub(k, v)
    s.add(Not(le['m23', 'p1']), Not(le['m13', 'p2']), Not(le['m12', 'p3']))
    s.add([inD[a] for a in rows])
    for (a, c), x in val.items():
        for (a2, c2), x2 in val.items():
            if (a, c) != (a2, c2): s.add(Implies(And(le[a, a2], le[c, c2]), le[x, x2]))
        s.add(Implies(Not(inD[c]), And(Not(le[x, a]), Not(le[c, x]))))
    eq = lambda a, b: And(le[a, b], le[b, a])
    for i in I:
        for k in range(n[i]): s.add(eq(orb[i][k + 1], val[f"c{i}", orb[i][k]]), Not(inD[orb[i][k + 1]]))
        e = val[f"c{i}", w[i]]
        s.add(inD[e], Not(le[e, f"p{i}"]))
        for j in I:
            if j != i: s.add(le[e, f"p{j}"] if j == SIG[i] else Not(le[e, f"p{j}"]))
    for i in I:
        glb(y[i], [w[j] for j in I if j != i]); s.add(Not(inD[y[i]]))
    glb('vJ', [w[i] for i in I]); s.add(inD['vJ'])
    for r in range(N):
        s.add(eq(q[r + 1] if r + 1 < N else val['mJ', q[r]], val['mJ', q[r]]))
        if r + 1 < N: s.add(Not(inD[q[r + 1]]))
    s.add(inD[val['mJ', q[N - 1]]])
    for (r, i), hname in hyb.items(): glb(hname, [q[r], y[i]])
    for (i, j), uname in u.items(): lub(uname, [y[i], y[j]])
    glb('z', list(u.values()))
    if dual_in_D:
        for (i, j), uname in u.items(): s.add(inD[val['mJ', uname]])
    r = s.check()
    out = str(r)
    if r == sat:
        mo = s.model()
        ev = lambda b: is_true(mo.eval(b))
        out += "  | hybrids in D: " + ",".join(h for h in hyb.values() if ev(inD[h]))
        out += " | z in D: " + str(ev(inD['z'])) + ", z <= vJ: " + str(ev(le['z', 'vJ']))
        out += " | mJ-entry labels: " + ",".join(x for x in P if ev(le[val['mJ', q[N - 1]], x]))
    return out
ALL = [((2, 2, 2), 2, False), ((2, 2, 2), 3, False), ((1, 2, 2), 2, False), ((2, 2, 2), 2, True), ((2, 2, 2), 1, False)]
cases = [ALL[int(a)] for a in sys.argv[1:]] if len(sys.argv) > 1 else ALL
for n, N, dd in cases:
    print(f"anchor lengths {n}, mJ-orbit entry at N={N}, dual values in D={dd}: "
          f"{run(dict(zip([1, 2, 3], n)), N, dd)}", flush=True)
