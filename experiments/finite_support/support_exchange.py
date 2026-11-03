"""Irredundant aggregate response supports and the response-exchange layer (log §34.3z¹⁰¹), z3.

Two-generator cut D = ↓p1 ∪ ↓p2. Column orbits c^j (from ⊥ along q_j, exit at N_j), row orbits y^i (from ⊤ along
p_i, enter at M_i), all named. Separately named fixed points r ∈ D, s ∉ D with the uniform aggregate inequalities at
every named row/column (F(x, s) ≤ s, r ≤ F(r, y)), r ≤ F(r, s) ≤ s, and TRUE supports (r, s not support members):
  size 2: s = F(p1, s) ∨ F(p2, s), r = F(r, q1) ∧ F(r, q2), with F(p_i, s) < s, r < F(r, q_j) (essential);
  size 3: a third row p3 ∈ D and column q3 ∉ D, irredundant: s ≰ join of any two, r ≱ meet of any two.
Exchange layer (`exchange`): u_i = F(p_i, s), v_j = F(r, q_j) named and used as row/column, cells F(v_j, u_i), with
no witness conditional on membership. All cells monotone. Patterns: free, all-B (as in §34.3z⁹⁹)."""
import itertools, sys
from z3 import *
def run(N, M, size=2, exchange=False, allB=False, named=False, case=None):
    c = {j: ['bot'] + [f"c{j}_{n}" for n in range(1, N[j] + 1)] for j in (1, 2)}
    y = {i: ['top'] + [f"y{i}_{m}" for m in range(1, M[i] + 1)] for i in (1, 2)}
    P = [f"a{k}" for k in range(1, size + 1)] if named else ['p1', 'p2'] + (['p3'] if size == 3 else []); Q = ['q1', 'q2'] + (['q3'] if size == 3 else [])
    U = [f"u{k}" for k in range(1, size + 1)]; V = [f"v{k}" for k in range(1, size + 1)]
    rowsD = list(dict.fromkeys([x for j in (1, 2) for x in c[j][:-1]] + ['p1', 'p2'] + P + ['g12', 'r'] + [y[i][-1] for i in (1, 2)]))
    colsO = list(dict.fromkeys(['top'] + Q + ['s'] + [c[j][-1] for j in (1, 2)] + [x for i in (1, 2) for x in y[i][:-1]]))
    rows = rowsD + (V if exchange else []); cols = colsO + (U if exchange else [])
    cell = {(a, b): f"F[{a},{b}]" for a in rows for b in cols}
    joins = [f"J{a}{b}" for a, b in itertools.combinations(range(1, size + 1), 2)] if size == 3 else []
    meets = [f"K{a}{b}" for a, b in itertools.combinations(range(1, size + 1), 2)] if size == 3 else []
    E = list(dict.fromkeys(rows + cols + U + V + joins + meets + list(cell.values()) + ['bot', 'top']))
    s = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    for a in E:
        s.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            for w in E: s.add(Implies(And(le[a, b], le[b, w]), le[a, w]))
    inD = {a: Or(le[a, 'p1'], le[a, 'p2']) for a in E}
    s.add(Not(le['p1', 'p2']), Not(le['p2', 'p1']))
    def lub(z, xs): s.add([le[q, z] for q in xs]); s.add([Implies(And([le[q, w] for q in xs]), le[z, w]) for w in E])
    def glb(z, xs): s.add([le[z, q] for q in xs]); s.add([Implies(And([le[w, q] for q in xs]), le[w, z]) for w in E])
    glb('g12', ['p1', 'p2'])
    s.add([inD[a] for a in rowsD]); s.add([Not(inD[b]) for b in colsO])
    for (a, b), v in cell.items():
        for (a2, b2), v2 in cell.items():
            if (a, b) != (a2, b2): s.add(Implies(And(le[a, a2], le[b, b2]), le[v, v2]))
        s.add(Implies(And(inD[a], Not(inD[b])), And(Not(le[v, a]), Not(le[b, v]))))
    eq = lambda a, b: And(le[a, b], le[b, a])
    for j in (1, 2):
        for n in range(N[j]): s.add(eq(c[j][n + 1], cell[(c[j][n], f"q{j}")]))
    for i in (1, 2):
        for m in range(M[i]): s.add(eq(y[i][m + 1], cell[(f"p{i}", y[i][m])]))
    # aggregate fixed points: uniform inequalities at named rows/columns, corner, true supports
    s.add([le[cell[(x, 's')], 's'] for x in rowsD]); s.add([le['r', cell[('r', k)]] for k in colsO])
    for k, p in enumerate(P): s.add(eq(U[k], cell[(p, 's')]), Not(le['s', U[k]]))
    for k, q in enumerate(Q): s.add(eq(V[k], cell[('r', q)]), Not(le[V[k], 'r']))
    lub('s', U); glb('r', V)
    if size == 3:
        for (a, b), jn, mt in zip(itertools.combinations(range(size), 2), joins, meets):
            lub(jn, [U[a], U[b]]); s.add(Not(le['s', jn]))
            glb(mt, [V[a], V[b]]); s.add(Not(le[mt, 'r']))
    Aside = {(i, j): Or([Not(le[c[j][n], f"p{i}"]) for n in range(1, N[j])] or [BoolVal(False)]) for i in (1, 2) for j in (1, 2)}
    Bside = {(i, j): Or([Not(le[f"q{j}", y[i][m]]) for m in range(1, M[i])] or [BoolVal(False)]) for i in (1, 2) for j in (1, 2)}
    if case == 'A': s.add([inD[x] for x in U])
    if case == 'B': s.add([Not(inD[x]) for x in V])
    if case == 'C': s.add(Or([And(Not(inD[x]), inD[w]) for x in U for w in V]))
    if allB: s.add(*[Bside[ij] for ij in Bside], *[Not(Aside[ij]) for ij in Aside])
    r = s.check(); out = str(r)
    if r == sat:
        mo = s.model(); ev = lambda b: is_true(mo.eval(b))
        out += f" | U in D: {[ev(inD[x]) for x in U]} | V in D: {[ev(inD[x]) for x in V]}"
        out += f" | mixed pairs (v in D, u out): {sum(1 for x in U for w in V if not ev(inD[x]) and ev(inD[w]))}"
    return out
MAIN = __name__ == '__main__' and len(sys.argv) == 1
cases = [] if not MAIN else [((2, 3), (3, 2), 'staggered'), ((2, 2), (2, 2), 'equal-time'), ((3, 2), (2, 3), 'reverse')]
for (n1, n2), (m1, m2), lab in cases:
    N = {1: n1, 2: n2}; M = {1: m1, 2: m2}
    print(f"{lab} N={N} M={M}, size-2 supports: all-B {run(N, M, 2, False, True)}", flush=True)
    print(f"   + exchange layer: all-B {run(N, M, 2, True, True)}", flush=True)
    if lab == 'staggered':
        print(f"   size-3 irredundant supports: all-B {run(N, M, 3, False, True)}", flush=True)
        print(f"   free (no forced pattern), size 2 + exchange: {run(N, M, 2, True, False)}", flush=True)

if len(sys.argv) > 1 and sys.argv[1] == 'named':
    N = {1: 2, 2: 3}; M = {1: 3, 2: 2}
    for size in (2, 3):
        print(f"staggered, named supports a_i (not generators), size {size}: all-B {run(N, M, size, False, True, True)}", flush=True)
    for case in 'ABC':
        print(f"staggered, generator support + exchange layer, case {case}: all-B {run(N, M, 2, True, True, False, case)}", flush=True)
    print(f"staggered, named size-3 + exchange layer, case C: all-B {run(N, M, 3, True, True, True, 'C')}", flush=True)
