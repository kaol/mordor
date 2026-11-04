"""Input-cofactor exchange of reciprocal supports (log §34.3z¹⁰²), z3.

Cut D = ⋃_{k<K} ↓g_k (generators pairwise incomparable). Named fixed points r ∈ D, s ∉ D; uniform inequalities
F(x, s) ≤ s, r ≤ F(r, y) at every named row/column on the right side of D (conditional on membership for cofactors).
Row support a_1..a_n ∈ D, column support b_1..b_n ∉ D, true and irredundant (named partial joins/meets of responses):
  s = ⋁ F(a_i, s), s ≰ ⋁_{j≠i} F(a_j, s);  r = ⋀ F(r, b_i), ⋀_{j≠i} F(r, b_j) ≰ r.
Cofactors a⁻_i = ⋁_{j≠i} a_j, b⁻_i = ⋀_{j≠i} b_j are named with cells F(a⁻_i, s), F(r, b⁻_i) only (plus, with
`orbits`, the two-generator (N; M) orbit profile of §34.3z⁹⁹). No witness on every cell, conditional on membership.
Row modes: all-in / one-out / multi-out; column modes: all-out / one-in / multi-in.
Generator rows carry their cells F(g_k, s) (needed: the Lean proof of `cofactor_stable_card` evaluates F at an
upper bound of the support, and every such bound in D lies below a generator).
`verify`: additionally demand that the exchanged support equation FAILS (expected UNSAT whenever all cofactors stay)."""
import itertools, sys
from z3 import *

def run(K, n, rowmode, colmode, verify=False, orbits=None, allB=False, caseC=False, gens_as_support=False, agg=None):
    G = [f"g{k}" for k in range(K)]
    A = G[:n] if gens_as_support else [f"a{i}" for i in range(n)]
    B = [f"b{i}" for i in range(n)]
    Ac = [f"a{i}m" for i in range(n)]; Bc = [f"b{i}m" for i in range(n)]
    rows = ['r'] + G + A + Ac; cols = ['s'] + B + Bc
    extra = []
    if orbits:
        N, M = orbits
        c = {j: ['bot'] + [f"c{j}_{t}" for t in range(1, N[j] + 1)] for j in (0, 1)}
        y = {i: ['top'] + [f"y{i}_{t}" for t in range(1, M[i] + 1)] for i in (0, 1)}
        qs = ['q0', 'q1']
        rows += [x for j in (0, 1) for x in c[j][:-1]] + G[:2] + ['g01'] + [y[i][-1] for i in (0, 1)]
        cols += ['top'] + qs + [c[j][-1] for j in (0, 1)] + [x for i in (0, 1) for x in y[i][:-1]]
    rows = list(dict.fromkeys(rows)); cols = list(dict.fromkeys(cols))
    # only the necessary cells: row-support/cofactor cells at s, column cells at r, plus full orbit grid if requested
    cellpairs = [(a, 's') for a in G + A + Ac + ['r']] + [('r', b) for b in B + Bc]
    if orbits:
        orow = [x for x in rows if x not in Ac and (x not in A or x in G)]; ocol = [x for x in cols if x not in B + Bc]
        cellpairs += [(a, b) for a in orow for b in ocol]
        cellpairs += [(x, 's') for x in orow] + [('r', x) for x in ocol]
    if agg is not None:  # size-2 aggregate cross pair (y, x), y = ⋀ b, x = ⋁ a, with the four neighbouring cells
        cellpairs += [('y', 'x'), ('y', 's'), ('r', 'x'), ('x', 's'), ('r', 'y')]
    cellpairs = list(dict.fromkeys(cellpairs))
    cell = {ab: f"F[{ab[0]},{ab[1]}]" for ab in cellpairs}
    U = [cell[(a, 's')] for a in A]; V = [cell[('r', b)] for b in B]
    Uj = [f"Uj{i}" for i in range(n)]; Vm = [f"Vm{i}" for i in range(n)]
    W = 'W' if verify else None
    E = list(dict.fromkeys(G + rows + cols + (['x', 'y'] if agg is not None else []) + list(cell.values()) + Uj + Vm + (['W', 'Z'] if verify else []) + ['bot', 'top']))
    sv = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    for a in E:
        sv.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            for w in E: sv.add(Implies(And(le[a, b], le[b, w]), le[a, w]))
    inD = {a: Or([le[a, g] for g in G]) for a in E}
    for g, h in itertools.permutations(G, 2): sv.add(Not(le[g, h]))
    def lub(z, xs): sv.add([le[q, z] for q in xs]); sv.add([Implies(And([le[q, w] for q in xs]), le[z, w]) for w in E])
    def glb(z, xs): sv.add([le[z, q] for q in xs]); sv.add([Implies(And([le[w, q] for q in xs]), le[w, z]) for w in E])
    if orbits: glb('g01', G[:2])
    for i in range(n):
        lub(Ac[i], [A[j] for j in range(n) if j != i]); glb(Bc[i], [B[j] for j in range(n) if j != i])
    sv.add([inD[a] for a in G + A + ['r']]); sv.add([Not(inD[b]) for b in B + ['s', 'top']])
    if orbits:
        sv.add([inD[x] for x in rows if x not in A + Ac]); sv.add([Not(inD[x]) for x in cols if x not in B + Bc])
    for (a, b), v in cell.items():
        for (a2, b2), v2 in cell.items():
            if (a, b) != (a2, b2): sv.add(Implies(And(le[a, a2], le[b, b2]), le[v, v2]))
        sv.add(Implies(And(inD[a], Not(inD[b])), And(Not(le[v, a]), Not(le[b, v]))))
    eq = lambda a, b: And(le[a, b], le[b, a])
    for a in rows:
        if (a, 's') in cell: sv.add(Implies(inD[a], le[cell[(a, 's')], 's']))
    for b in cols:
        if ('r', b) in cell: sv.add(Implies(Not(inD[b]), le['r', cell[('r', b)]]))
    sv.add(le['r', cell[('r', 's')]], le[cell[('r', 's')], 's'])
    lub('s', U); glb('r', V)
    for i in range(n):
        lub(Uj[i], [U[j] for j in range(n) if j != i]); sv.add(Not(le['s', Uj[i]]))
        glb(Vm[i], [V[j] for j in range(n) if j != i]); sv.add(Not(le[Vm[i], 'r']))
    if agg is not None:
        lub('x', A); glb('y', B); wv = cell[('y', 'x')]
        dIn, yle, wle = agg
        sv.add(inD[wv] if dIn else Not(inD[wv]))
        sv.add(le['y', wv] if yle else Not(le['y', wv]))
        sv.add(le[wv, 'x'] if wle else Not(le[wv, 'x']))
    outs = [Not(inD[x]) for x in Ac]; ins = [inD[x] for x in Bc]
    cnt = lambda bs: Sum([If(b, 1, 0) for b in bs])
    sv.add({'all-in': cnt(outs) == 0, 'one-out': cnt(outs) == 1, 'multi-out': cnt(outs) >= 2}[rowmode])
    sv.add({'all-out': cnt(ins) == 0, 'one-in': cnt(ins) == 1, 'multi-in': cnt(ins) >= 2}[colmode])
    if verify:  # exchanged equations fail: s ≰ W := ⋁ F(a⁻, s)  or  Z := ⋀ F(r, b⁻) ≰ r
        lub('W', [cell[(a, 's')] for a in Ac]); glb('Z', [cell[('r', b)] for b in Bc])
        sv.add(Or(Not(le['s', 'W']) if rowmode == 'all-in' else BoolVal(False),
                  Not(le['Z', 'r']) if colmode == 'all-out' else BoolVal(False)))
    if orbits:
        for j in (0, 1):
            for t in range(N[j]): sv.add(eq(c[j][t + 1], cell[(c[j][t], f"q{j}")]))
        for i in (0, 1):
            for t in range(M[i]): sv.add(eq(y[i][t + 1], cell[(G[i], y[i][t])]))
        Aside = {(i, j): Or([Not(le[c[j][t], G[i]]) for t in range(1, N[j])] or [BoolVal(False)]) for i in (0, 1) for j in (0, 1)}
        Bside = {(i, j): Or([Not(le[f"q{j}", y[i][t]]) for t in range(1, M[i])] or [BoolVal(False)]) for i in (0, 1) for j in (0, 1)}
        if allB: sv.add(*[Bside[ij] for ij in Bside], *[Not(Aside[ij]) for ij in Aside])
        if caseC: sv.add(Or([And(Not(inD[u]), inD[v]) for u in U for v in V]))
    return str(sv.check())

mode = sys.argv[1] if len(sys.argv) > 1 else 'small'
if mode == 'small':
    for K, n in ((2, 2), (2, 3), (3, 3)):
        for rm in ('all-in', 'one-out', 'multi-out'):
            line = [f"{cm}: {run(K, n, rm, cm)}" for cm in ('all-out', 'one-in', 'multi-in')]
            print(f"K={K} n={n} rows {rm:9s} | " + " | ".join(line), flush=True)
        print(f"K={K} n={n} verify exchanged equations (all-in, all-out, negated): {run(K, n, 'all-in', 'all-out', verify=True)}", flush=True)
    print(f"K=3 n=3 generator support, rows all-in: {run(3, 3, 'all-in', 'all-out', gens_as_support=True)}", flush=True)
elif mode == 'orbits':
    O = ({0: 2, 1: 3}, {0: 3, 1: 2})
    print(f"(2,2;2,2) equal-time all-B, named n=3, rows one-out, cols all-out (control): {run(2, 3, 'one-out', 'all-out', orbits=({0: 2, 1: 2}, {0: 2, 1: 2}), allB=True)}", flush=True)
    print(f"(2,3;3,2) all-B, generator support n=2 (cofactor = swap): {run(2, 2, 'all-in', 'all-out', orbits=O, allB=True, gens_as_support=True)}", flush=True)
    for rm in ('one-out', 'multi-out'):
        for cm in ('all-out', 'one-in', 'multi-in'):
            print(f"(2,3;3,2) all-B, named n=3, rows {rm}, cols {cm}: {run(2, 3, rm, cm, orbits=O, allB=True)}", flush=True)
    print(f"(2,3;3,2) all-B + Case C, named n=3, rows one-out, cols all-out: {run(2, 3, 'one-out', 'all-out', orbits=O, allB=True, caseC=True)}", flush=True)
elif mode.startswith('agg'):
    O = ({0: 2, 1: 3}, {0: 3, 1: 2}); part = int(mode[3:]) if len(mode) > 3 else None
    combos = list(itertools.product((True, False), repeat=3))
    for k, (dIn, yle, wle) in enumerate(combos):
        if part is not None and k % 2 != part: continue
        lab = f"F(y,x) {'in D' if dIn else 'outside D'}, {'y < F(y,x)' if yle else 'y ∥ F(y,x)'}, {'F(y,x) < x' if wle else 'F(y,x) ∥ x'}"
        print(f"(2,3;3,2) all-B, named n=2, aggregate pair: {lab}: {run(2, 2, 'all-in', 'all-out', orbits=O, allB=True, agg=(dIn, yle, wle))}", flush=True)
elif mode == 'card':
    print(f"K=3 n=4 rows all-in (cofactor_stable_card predicts unsat): {run(3, 4, 'all-in', 'all-out')}", flush=True)
    print(f"K=3 n=4 rows one-out (control): {run(3, 4, 'one-out', 'all-out')}", flush=True)
    print(f"K=3 n=2 named rows (size-2 support in a 3-generator cut): {run(3, 2, 'all-in', 'all-out')}", flush=True)
