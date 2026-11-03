"""Does the next frontier step from the squeeze pair escape the envelope [d, u]? (log §34.3z⁹⁶), z3.

One cross pair (x, y), z = F(x, y); envelope d = x ⊓ y ⊓ z (glb), u = x ⊔ y ⊔ z (lub); L = d ⊔ F(d, y),
U = u ⊓ F(x, u); the extracted cross pair (r, c) ∈ {(L, U), (d, L), (U, u)} (case chosen); its response
z2 = F(r, c), a2 = c ⊓ z2, b2 = r ⊔ z2. Escape: a2 ≱ d or b2 ≰ u. Cells: only the four named ones (F(x,y), F(d,y),
F(x,u), F(r,c)), monotone among themselves, witness-free on cross cells; nothing on D × D."""
import itertools, sys
from z3 import *
def run(K, case, escape):
    P = [f"p{i}" for i in range(1, K + 1)]
    base = ['bot', 'top'] + P + (['m'] if K == 2 else [])
    named = base + ['x', 'y', 'z', 'd', 'u', 'L', 'U', 'Fdy', 'Fxu', 'z2', 'a2', 'b2']
    r, c = {'LU': ('L', 'U'), 'dL': ('d', 'L'), 'Uu': ('U', 'u')}[case]
    cells = {('x', 'y'): 'z', ('d', 'y'): 'Fdy', ('x', 'u'): 'Fxu', (r, c): 'z2'}
    s = Solver(); E = named
    le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    for a in E:
        s.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            for w in E: s.add(Implies(And(le[a, b], le[b, w]), le[a, w]))
    inD = {a: Or([le[a, q] for q in P]) for a in E}
    for a, b in itertools.permutations(P, 2): s.add(Not(le[a, b]))
    def glb(zz, xs): s.add([le[zz, q] for q in xs]); s.add([Implies(And([le[w, q] for q in xs]), le[w, zz]) for w in E])
    def lub(zz, xs): s.add([le[q, zz] for q in xs]); s.add([Implies(And([le[q, w] for q in xs]), le[zz, w]) for w in E])
    if K == 2: glb('m', P)
    s.add(inD['x'], Not(inD['y']), Not(inD['top']))
    glb('d', ['x', 'y', 'z']); lub('u', ['x', 'y', 'z'])
    lub('L', ['d', 'Fdy']); glb('U', ['u', 'Fxu'])
    s.add(inD[r], Not(inD[c]))
    glb('a2', [c, 'z2']); lub('b2', [r, 'z2'])
    items = list(cells.items())
    for (rc, v) in items:
        for (rc2, v2) in items:
            if rc != rc2: s.add(Implies(And(le[rc[0], rc2[0]], le[rc[1], rc2[1]]), le[v, v2]))
        s.add(Implies(And(inD[rc[0]], Not(inD[rc[1]])), And(Not(le[v, rc[0]]), Not(le[rc[1], v]))))
    if escape: s.add(Or(Not(le['d', 'a2']), Not(le['b2', 'u'])))
    return s.check()
for K in [1, 2]:
    for case in ['LU', 'dL', 'Uu']:
        print(f"k={K} extracted pair {case}: consistent {run(K, case, False)}, next response escapes [d,u] {run(K, case, True)}", flush=True)
