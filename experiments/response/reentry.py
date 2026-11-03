"""Response re-entry chains (log §34.3z⁹⁴), z3.

A chain of cross pairs (x_t, y_t), t = 0..n. Each is a frontier pair: z_t = F(x_t, y_t), a_t = y_t ⊓ z_t ∈ D (glb),
b_t = x_t ⊔ z_t ∉ D (lub). Re-entry: case A (z_t ∈ D): next pair (z_t, b_t); case B (z_t ∉ D): next pair (a_t, z_t).
Optionally a terminalization step in between: the next frontier pair is (x', y') with x' ≥ the re-entered row,
y' ≤ the re-entered column. Rows: generators, their meet(s) and every named element of D; columns: every named element
outside D. F is a full cross table on named elements, monotone, witness-free; nothing on D × D.
Tests: (P) persistent degeneracy: every step degenerate (A: z_t ≤ y_t; B: x_t ≤ z_t), for k = 1, 2, 3 and case
patterns; (N) non-nesting: the next response interval [a_{t+1}, b_{t+1}] not contained in [a_t, b_t]."""
import itertools, sys
from z3 import *

def run(K, cases, degenerate, terminalize=False, nonnest=False):
    n = len(cases)
    P = [f"p{i}" for i in range(1, K + 1)]
    meets = []
    if K >= 2: meets = [f"m{a}{b}" for a, b in itertools.combinations(range(1, K + 1), 2)]
    elems = ['bot', 'top'] + P + meets
    X = ['x0']; Y = ['y0']; Z, A, B = [], [], []
    TX, TY = [], []
    for t in range(n + 1):
        Z.append(f"z{t}"); A.append(f"a{t}"); B.append(f"b{t}")
    names = elems + ['x0', 'y0'] + Z + A + B
    if terminalize:
        for t in range(1, n + 1): names += [f"xx{t}", f"yy{t}"]
    names = list(dict.fromkeys(names))
    s = Solver(); le = {(u, v): Bool(f"le|{u}|{v}") for u in names for v in names}
    # cells: F applied at every (D-element, outside element) pair among names, as fresh values
    inD_base = None
    for u in names:
        s.add(le[u, u], le['bot', u], le[u, 'top'])
    def trans(E):
        for u in E:
            for v in E:
                for w in E: s.add(Implies(And(le[u, v], le[v, w]), le[u, w]))
    # pair coordinates
    xs = ['x0']; ys = ['y0']
    for t in range(n):
        if cases[t] == 'A': nx, ny = Z[t], B[t]
        else: nx, ny = A[t], Z[t]
        if terminalize: xs.append(f"xx{t+1}"); ys.append(f"yy{t+1}")
        else: xs.append(nx); ys.append(ny)
    rows = P + meets + [r for r in dict.fromkeys(xs)]
    cols = ['top'] + [c for c in dict.fromkeys(ys)]
    val = {(r, c): f"F[{r},{c}]" for r in rows for c in cols}
    E = list(dict.fromkeys(names + list(val.values())))
    le = {(u, v): Bool(f"le|{u}|{v}") for u in E for v in E}
    s = Solver()
    for u in E: s.add(le[u, u], le['bot', u], le[u, 'top'])
    for u in E:
        for v in E:
            for w in E: s.add(Implies(And(le[u, v], le[v, w]), le[u, w]))
    inD = {u: Or([le[u, q] for q in P]) for u in E}
    for u, v in itertools.permutations(P, 2): s.add(Not(le[u, v]))
    def glb(zz, xs_): s.add([le[zz, q] for q in xs_]); s.add([Implies(And([le[w, q] for q in xs_]), le[w, zz]) for w in E])
    def lub(zz, xs_): s.add([le[q, zz] for q in xs_]); s.add([Implies(And([le[q, w] for q in xs_]), le[zz, w]) for w in E])
    for mname in meets: glb(mname, [f"p{mname[1]}", f"p{mname[2]}"])
    if K == 3: s.add(Not(le['m23', 'p1']), Not(le['m13', 'p2']), Not(le['m12', 'p3']))
    s.add(Not(inD['top']))
    for (r, c), v in val.items():
        for (r2, c2), v2 in val.items():
            if (r, c) != (r2, c2): s.add(Implies(And(le[r, r2], le[c, c2]), le[v, v2]))
        s.add(Implies(And(inD[r], Not(inD[c])), And(Not(le[v, r]), Not(le[c, v]))))
    eq = lambda u, v: And(le[u, v], le[v, u])
    for t in range(n + 1):
        x, y = xs[t], ys[t]
        s.add(inD[x], Not(inD[y]))
        s.add(eq(Z[t], val[x, y])); glb(A[t], [y, Z[t]]); lub(B[t], [x, Z[t]])
        s.add(inD[A[t]], Not(inD[B[t]]))
        if t < n:
            s.add(inD[Z[t]] if cases[t] == 'A' else Not(inD[Z[t]]))
            if degenerate:
                s.add(le[Z[t], y] if cases[t] == 'A' else le[x, Z[t]])
            if terminalize:
                nx, ny = (Z[t], B[t]) if cases[t] == 'A' else (A[t], Z[t])
                s.add(le[nx, xs[t + 1]], le[ys[t + 1], ny])
    if nonnest:
        s.add(Or([Not(And(le[A[t], A[t + 1]], le[B[t + 1], B[t]])) for t in range(n)]))
    return s.check()

print("(P) persistent degenerate re-entry, no terminalization (re-entered pairs are frontier pairs):")
for K in [1, 2, 3]:
    pats = [('B',), ('B', 'B'), ('B', 'B', 'B')] if K == 1 else [('A',), ('B',), ('A', 'B'), ('B', 'A'), ('A', 'A', 'A'), ('B', 'B', 'B'), ('A', 'B', 'A')]
    for pat in pats:
        print(f"  k={K} cases {''.join(pat)}: {run(K, pat, True)}", flush=True)
if K == 1: pass
print("(A1) k=1, case A at all (D principal, join-closed):", run(1, ('A',), False), flush=True)
print("(N) next response interval not nested in the previous one, with terminalization:")
for K in [1, 2]:
    for pat in [('B',), ('A',)] if K == 2 else [('B',)]:
        print(f"  k={K} case {pat[0]}: {run(K, pat, False, terminalize=True, nonnest=True)}", flush=True)
print("(N0) next response interval not nested, re-entered pair already a frontier pair (no terminalization):")
for K in [1, 2]:
    for pat in [('B',), ('A',)] if K == 2 else [('B',)]:
        print(f"  k={K} case {pat[0]}: {run(K, pat, False, nonnest=True)}", flush=True)
