"""Calibration of the frontier-pair induction (log §34.3z⁸⁴), z3.

The mixed transitions of CrossCellInduction.frontier_pair always reach a frontier pair (x, y): x ∈ D, y ∉ D,
y ⊓ F(x, y) ∈ D, x ⊔ F(x, y) ∉ D. Is that terminal state contradictory, given monotonicity and no witness on the
named cells? Test for k = 1 (D = ↓p, where Cut has a three-line proof by the UNclipped orbit of F(p, ·)) and k = 2.
Named elements: generators, their meet, x, y, ⊤, the meet y ⊓ F(x, y) and join x ⊔ F(x, y) as glb/lub, F on
rows {generators, meet, x} × columns {y, ⊤} as named elements. Also tested: the frontier pair reached from (p₁, ⊤)
(x ≥ p₁, so x = p₁) and the variant with x = y ⊓ F(x, y) ∨ ... omitted."""
import itertools, sys
from z3 import *
def run(k, x_is_p1):
    P = [f"p{i}" for i in range(1, k + 1)]
    rows = P + (['m'] if k > 1 else []) + ['x']; cols = ['y', 'top']
    val = {(r, c): f"F[{r},{c}]" for r in rows for c in cols}
    E = ['bot'] + rows + cols + list(val.values()) + ['ym', 'xp']
    s = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    for a in E:
        s.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            for c in E: s.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
    inD = {a: Or([le[a, q] for q in P]) for a in E}
    for a, b in itertools.permutations(P, 2): s.add(Not(le[a, b]))
    def glb(z, xs): s.add([le[z, x] for x in xs]); s.add([Implies(And([le[w, x] for x in xs]), le[w, z]) for w in E])
    def lub(z, xs): s.add([le[x, z] for x in xs]); s.add([Implies(And([le[x, w] for x in xs]), le[z, w]) for w in E])
    if k > 1: glb('m', P)
    s.add([inD[r] for r in rows]); s.add([Not(inD[c]) for c in cols])
    for (r, c), v in val.items():
        for (r2, c2), v2 in val.items():
            if (r, c) != (r2, c2): s.add(Implies(And(le[r, r2], le[c, c2]), le[v, v2]))
        s.add(Not(le[v, r]), Not(le[c, v]))
    glb('ym', ['y', val['x', 'y']]); lub('xp', ['x', val['x', 'y']])
    s.add(inD['ym'], Not(inD['xp']))
    if x_is_p1: s.add(le['x', 'p1'], le['p1', 'x'])
    return s.check()
for k in [1, 2]:
    for xp in [False, True]:
        print(f"k={k}, frontier pair{' with x = p1' if xp else ''}: {run(k, xp)}", flush=True)
