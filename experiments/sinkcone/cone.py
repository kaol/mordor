"""The cone-restricted weak base (log §34.3z⁸²), z3: does the whole sink-cone package exclude the reduced failure?

Named partial model, several columns at once:
  columns  ⊤, u0 (cone top), v (≤ u0: the reduced weak-base failure), q = F(p_j, v) (as a column), w = v ∨ q (lub),
           o = F(c_j, ⊤) (the c_j-orbit of ⊤, entry at step 2, transferring by anchor_sandwich);
  rows     p_i, c_i, pairwise meets, triple meet, d = v ∧ q (glb; in D with label exactly {j}, weak_base_reduced).
F is given on every row × column as named elements, monotone, witness-free on cross cells.
Cone package (sink_below), imposed at EVERY named column y ≤ u0 outside D:
  ¬Transfer_j(y);  F(p_j, y) ≰ y;  the transfer-edge set at y equals that at u0;  Transfer_a(u0).
Reduced failure at v: F(c_j, v) ≤ v, F(c_j, v) ≤ p_j, d = v ∧ q ∈ D.
Proved global facts imposed: l4 at every named outside column; anchor_sandwich at ⊤ for c_j.
Cases: q ≤ u0 (then w is a cone column too) or q ≰ u0. For k = 3 the edge pattern of b is enumerated
(b → a, b → j, both, none; a → b, a → j, both), keeping only acyclic patterns. Control: k = 2 (generators a, j).
Usage: python3 cone.py [k2]"""
import itertools, sys
from z3 import *
K2 = 'k2' in sys.argv
IDX = ['a', 'j'] if K2 else ['a', 'b', 'j']
P = ['p' + i for i in IDX]; C = ['c' + i for i in IDX]
pairs = list(itertools.combinations(IDX, 2))
MX = ['m' + x + y for x, y in pairs]
BASE = P + C + MX + ['t']                          # t = triple (or pair) meet

def run(q_in_cone, edges):
    rows = BASE + ['d']; cols = ['top', 'u0', 'v', 'q', 'w', 'o']
    val = {(r, y): f"F[{r},{y}]" for r in rows for y in cols}
    E = ['bot'] + rows + cols + list(val.values())
    s = Solver(); le = {(x, y): Bool(f"le|{x}|{y}") for x in E for y in E}
    for x in E:
        s.add(le[x, x], le['bot', x], le[x, 'top'])
        for y in E:
            for z in E: s.add(Implies(And(le[x, y], le[y, z]), le[x, z]))
    inD = {x: Or([le[x, pp] for pp in P]) for x in E}
    for x, y in itertools.permutations(P, 2): s.add(Not(le[x, y]))
    def glb(z, xs): s.add([le[z, x] for x in xs]); s.add([Implies(And([le[w_, x] for x in xs]), le[w_, z]) for w_ in E])
    def lub(z, xs): s.add([le[x, z] for x in xs]); s.add([Implies(And([le[x, w_] for x in xs]), le[z, w_]) for w_ in E])
    for (x, y), m in zip(pairs, MX): glb(m, ['p' + x, 'p' + y])
    glb('t', P)
    if K2:
        glb('ca', P); glb('cj', P)
    else:
        for i in IDX:
            lub('c' + i, ['m' + ''.join(sorted(x + y, key=IDX.index)) if False else m for (x, y), m in zip(pairs, MX) if i in (x, y)])
        for (x, y), m in zip(pairs, MX):
            z = [i for i in IDX if i not in (x, y)][0]; s.add(Not(le[m, 'p' + z]))       # strict crossing
    s.add([inD[r] for r in rows]); s.add([Not(inD[c]) for c in cols])
    for (r, y), x in val.items():
        for (r2, y2), x2 in val.items():
            if (r, y) != (r2, y2): s.add(Implies(And(le[r, r2], le[y, y2]), le[x, x2]))
        s.add(Not(le[x, r]), Not(le[y, x]))
    eq = lambda x, y: And(le[x, y], le[y, x])
    edge = lambda i, k, y: le[val['c' + i, y], 'p' + k]
    for i in IDX:                                                                  # l4 everywhere
        for y in cols: s.add(Implies(And(le[val['p' + i, y], y], inD[val['c' + i, y]]), Not(le[val['c' + i, y], 'p' + i])))
    # c_j-orbit of top: o = F(c_j, top) outside, entry F(c_j, o) transfers (anchor_sandwich at top)
    s.add(eq('o', val['cj', 'top']), Or([edge('j', k, 'o') for k in IDX if k != 'j']))
    # reduced failure at v
    s.add(le['v', 'u0'], le[val['cj', 'v'], 'v'], edge('j', 'j', 'v'), eq('q', val['pj', 'v']))
    glb('d', ['v', 'q']); s.add(le['d', 'pj']); s.add([Not(le['d', 'p' + k]) for k in IDX if k != 'j'])
    lub('w', ['v', 'q'])
    s.add(le['q', 'u0'] if q_in_cone else Not(le['q', 'u0']))
    # cone package at every named column below u0
    for y in cols:
        incone = le[y, 'u0']
        s.add(Implies(incone, And([Not(edge('j', k, y)) for k in IDX if k != 'j'])))
        s.add(Implies(incone, Not(le[val['pj', y], y])))
        for i in IDX:
            for k in IDX:
                if k != i: s.add(Implies(incone, edge(i, k, y) == edge(i, k, 'u0')))
    for (i, k), on in edges.items(): s.add(edge(i, k, 'u0') if on else Not(edge(i, k, 'u0')))
    return s.check()

if K2:
    pats = [{('a', 'j'): True}]
else:
    pats = []
    for ab, aj, ba, bj in itertools.product([0, 1], repeat=4):
        if not (ab or aj): continue                      # a transfers
        if ab and ba: continue                           # acyclic
        pats.append({('a', 'b'): bool(ab), ('a', 'j'): bool(aj), ('b', 'a'): bool(ba), ('b', 'j'): bool(bj)})
for qc in [True, False]:
    for e in pats:
        tag = ','.join(f"{i}->{k}" for (i, k), on in e.items() if on) or '-'
        print(f"{'k=2 ' if K2 else ''}q {'<=' if qc else 'not <='} u0, edges {tag}: {run(qc, e)}", flush=True)
