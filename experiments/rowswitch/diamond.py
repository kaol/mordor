"""Extended terminal diamond with the top envelope (log §34.3z⁸⁹), z3.

Pair (x, y) = (1, 2), h = F(m12, ·). Columns: ⊤, v = h(⊤) (outside: the envelope column), the terminal column t' ≤ v,
q = F(p_y, t') (outside), u = t' ⊔ q (lub). Rows: generators, all meet rows, and the terminal entry value
e = F(m12, t') (in D, below p_y) used as a row. Named meets: d = t' ⊓ q (in D, each label tried) and
w = v ⊓ R with R = F(e, v) (in D with each label, or outside). F on every row × outside column, monotone,
witness-free; nothing imposed on D × D. No sandwich. k = 2 and k = 3 (strict crossing)."""
import itertools, sys
from z3 import *
def run(K, dlab, wlab):
    P = [f"p{i}" for i in range(1, K + 1)]
    M = {'m12': ['p1', 'p2']}
    if K == 3: M.update({'m13': ['p1', 'p3'], 'm23': ['p2', 'p3'], 'b': P})
    rows = P + list(M) + ['e']; cols = ['top', 'v', 't', 'q', 'u']
    val = {(a, c): f"F[{a},{c}]" for a in rows for c in cols}
    E = ['bot'] + rows + cols + list(val.values()) + ['d', 'w']
    S = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    for a in E:
        S.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            for c in E: S.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
    inD = {a: Or([le[a, q] for q in P]) for a in E}
    for a, b in itertools.permutations(P, 2): S.add(Not(le[a, b]))
    def glb(z, xs): S.add([le[z, x] for x in xs]); S.add([Implies(And([le[w_, x] for x in xs]), le[w_, z]) for w_ in E])
    def lub(z, xs): S.add([le[x, z] for x in xs]); S.add([Implies(And([le[x, w_] for x in xs]), le[z, w_]) for w_ in E])
    for k, v in M.items(): glb(k, v)
    if K == 3: S.add(Not(le['m23', 'p1']), Not(le['m13', 'p2']), Not(le['m12', 'p3']))
    S.add([inD[a] for a in rows]); S.add([Not(inD[c]) for c in cols])
    for (a, c), x in val.items():
        for (a2, c2), x2 in val.items():
            if (a, c) != (a2, c2): S.add(Implies(And(le[a, a2], le[c, c2]), le[x, x2]))
        S.add(Not(le[x, a]), Not(le[c, x]))
    eq = lambda a, b: And(le[a, b], le[b, a])
    S.add(eq('v', val['m12', 'top']), le['t', 'v'])
    S.add(eq('e', val['m12', 't']), le['e', 'p2'])
    S.add(eq('q', val['p2', 't'])); lub('u', ['t', 'q'])
    glb('d', ['t', 'q']); S.add(le['d', dlab])
    glb('w', ['v', val['e', 'v']])
    S.add(le['w', wlab] if wlab else Not(inD['w']))
    return S.check()
for K in [2, 3]:
    P = [f"p{i}" for i in range(1, K + 1)]
    for dl in P:
        for wl in P + [None]:
            print(f"k={K}: d below {dl}, v ⊓ R {'below ' + wl if wl else 'outside D'}: {run(K, dl, wl)}", flush=True)
