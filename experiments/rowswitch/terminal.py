"""Terminal configuration of the row-switching system (log §34.3z⁸⁸), z3.

k = 2 (full A2 profile): columns s, s' = F(p1, s) (non-contracting start), the h-orbits of s and s' (h = F(m, ·),
m = p1 ⊓ p2): s enters at step n+1 below p1, s' still outside at step n (A2) and entering later below p2 from its
last point t; z = F(p2, t) (as a column) and d = t ⊓ z (glb), with d ∈ D below p1 or below p2.
k = 3 (terminal pair state alone): column t, pair entry F(m_xy, t) ≤ p_y, z = F(p_y, t) ∉ D, d = t ⊓ z ∈ D with
each possible label; all seven meet rows, strict crossing.
F on all rows × named columns, monotone, witness-free. No sandwich."""
import itertools, sys
from z3 import *

def base(P, rows_extra, cols):
    rows = P + rows_extra
    val = {(a, c): f"F[{a},{c}]" for a in rows for c in cols}
    E = ['bot', 'top'] + rows + cols + list(val.values()) + ['d']
    E = list(dict.fromkeys(E))
    S = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    for a in E:
        S.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            for c in E: S.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
    inD = {a: Or([le[a, q] for q in P]) for a in E}
    for a, b in itertools.permutations(P, 2): S.add(Not(le[a, b]))
    def glb(z, xs): S.add([le[z, x] for x in xs]); S.add([Implies(And([le[w, x] for x in xs]), le[w, z]) for w in E])
    S.add([inD[a] for a in rows]); S.add([Not(inD[c]) for c in cols])
    for (a, c), v in val.items():
        for (a2, c2), v2 in val.items():
            if (a, c) != (a2, c2): S.add(Implies(And(le[a, a2], le[c, c2]), le[v, v2]))
        S.add(Not(le[v, a]), Not(le[c, v]))
    eq = lambda a, b: And(le[a, b], le[b, a])
    return S, le, inD, val, glb, eq

def k2(n, n2, dlab):
    P = ['p1', 'p2']
    so = ['s'] + [f"s_{k}" for k in range(1, n + 1)]
    to = ['u'] + [f"u_{k}" for k in range(1, n2 + 1)]
    cols = ['top'] + so + to + ['z']
    S, le, inD, val, glb, eq = base(P, ['m'], cols)
    glb('m', P)
    S.add(eq('u', val['p1', 's']), Not(le[val['p1', 's'], 's']), Not(le['s', val['p1', 's']]))
    for orb in (so, to):
        for k in range(len(orb) - 1): S.add(eq(orb[k + 1], val['m', orb[k]]))
    S.add(le[val['m', so[-1]], 'p1'], le[val['m', to[-1]], 'p2'])          # opposite labels, A2 (n2 >= n)
    t = to[-1]
    S.add(eq('z', val['p2', t])); glb('d', [t, 'z']); S.add(le['d', dlab])
    return S.check()

def k3(dlab):
    P = ['p1', 'p2', 'p3']; cols = ['top', 't', 'z']
    M = {'m12': ['p1', 'p2'], 'm13': ['p1', 'p3'], 'm23': ['p2', 'p3'], 'b': P}
    S, le, inD, val, glb, eq = base(P, list(M), cols)
    for k, v in M.items(): glb(k, v)
    S.add(Not(le['m23', 'p1']), Not(le['m13', 'p2']), Not(le['m12', 'p3']))
    S.add(le[val['m12', 't'], 'p2'], eq('z', val['p2', 't'])); glb('d', ['t', 'z']); S.add(le['d', dlab])
    return S.check()

for n, n2 in [(1, 1), (1, 2), (2, 2)]:
    for dl in ['p1', 'p2']:
        print(f"k=2 A2 profile n={n}, n'={n2}, d below {dl}: {k2(n, n2, dl)}", flush=True)
for dl in ['p1', 'p2', 'p3']:
    print(f"k=3 terminal pair state (1,2), d below {dl}: {k3(dl)}", flush=True)
