"""Second-order face incidence (log §34.3z⁹³), z3.

Strict crossing triple; rows p_i, pairwise meets, m = m123, anchors c_i. Hamiltonian last points w_i (columns) with
exact labels e_i = F(c_i, w_i) ≤ p_{σ(i)} only (σ = 1→2→3→1, hamiltonian_full_triple); faces y_i = ⋀_{j≠i} w_j
outside, v_J = ⋀ w ∈ D. Second order: u_ij = y_i ∨ y_j, v_i = u_ij ∧ u_ik, r_ij = v_i ∧ v_j, z = ⋀ v_i (all named,
all used as columns; no witness conditional on being outside D). No anchor orbits from ⊤ (the length-two N = 2 profile
of §34.3z⁹² is SAT; this model isolates the second-order cells). Cases from the brief's §5."""
import itertools, sys
from z3 import *
SIG = {1: 2, 2: 3, 3: 1}
def run(case):
    I = [1, 2, 3]; P = [f"p{i}" for i in I]
    M = {'m12': ['p1', 'p2'], 'm13': ['p1', 'p3'], 'm23': ['p2', 'p3'], 'm': P}
    C = {'c1': ['m12', 'm13'], 'c2': ['m12', 'm23'], 'c3': ['m13', 'm23']}
    rows = P + list(M) + list(C)
    pr = [(1, 2), (1, 3), (2, 3)]
    cols = ['top'] + [f"w{i}" for i in I] + [f"y{i}" for i in I] + [f"u{a}{b}" for a, b in pr] + \
        [f"v{i}" for i in I] + [f"r{a}{b}" for a, b in pr] + ['z', 'vJ']
    val = {(a, c): f"F[{a},{c}]" for a in rows for c in cols}
    E = ['bot'] + rows + cols + list(val.values())
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
    s.add([inD[a] for a in rows]); s.add(Not(inD['top']))
    for (a, c), x in val.items():
        for (a2, c2), x2 in val.items():
            if (a, c) != (a2, c2): s.add(Implies(And(le[a, a2], le[c, c2]), le[x, x2]))
        s.add(Implies(Not(inD[c]), And(Not(le[x, a]), Not(le[c, x]))))
    for i in I:
        s.add(Not(inD[f"w{i}"]))
        e = val[f"c{i}", f"w{i}"]
        for j in I: s.add(le[e, f"p{j}"] if j == SIG[i] else Not(le[e, f"p{j}"]))
        glb(f"y{i}", [f"w{j}" for j in I if j != i]); s.add(Not(inD[f"y{i}"]))
    glb('vJ', [f"w{i}" for i in I]); s.add(inD['vJ'])
    for a, b in pr: lub(f"u{a}{b}", [f"y{a}", f"y{b}"])
    U = lambda a, b: f"u{min(a,b)}{max(a,b)}"
    for i in I:
        j, k = [x for x in I if x != i]; glb(f"v{i}", [U(i, j), U(i, k)])
    for a, b in pr: glb(f"r{a}{b}", [f"v{a}", f"v{b}"])
    glb('z', [f"v{i}" for i in I])
    edgeD = [inD[val['m', f"u{a}{b}"]] for a, b in pr]
    rD = [inD[f"r{a}{b}"] for a, b in pr]
    eqv = [And(le[f"v{i}", f"y{i}"], le[f"y{i}", f"v{i}"]) for i in I]
    extra = {
        '1 all edge outputs in D': And(edgeD),
        '2 some edge output outside D': Not(And(edgeD)),
        '3 all r_ij in D': And(rD),
        '4 some r_ij outside D': Not(And(rD)),
        '4b all edges in D and some r_ij outside D (Lean: lower_vertex_in_D)': And(And(edgeD), Not(And(rD))),
        '5 degenerate v_i = y_i for all i': And(eqv),
        '6 some strict v_i > y_i': Not(And(eqv)),
        '6b all edges in D and some strict v_i > y_i': And(And(edgeD), Not(And(eqv))),
        '7 z strictly above vJ': Not(le['z', 'vJ']),
    }[case]
    s.add(extra)
    r = s.check()
    out = str(r)
    if r == sat:
        mo = s.model(); ev = lambda b: is_true(mo.eval(b))
        out += f" | edges in D: {[ev(x) for x in edgeD]} | r in D: {[ev(x) for x in rD]} | v=y: {[ev(x) for x in eqv]} | z<=vJ: {ev(le['z','vJ'])}"
    return out
for case in ['1 all edge outputs in D', '2 some edge output outside D', '3 all r_ij in D', '4 some r_ij outside D',
             '4b all edges in D and some r_ij outside D (Lean: lower_vertex_in_D)', '5 degenerate v_i = y_i for all i',
             '6 some strict v_i > y_i', '6b all edges in D and some strict v_i > y_i', '7 z strictly above vJ']:
    print(f"{case}: {run(case)}", flush=True)
