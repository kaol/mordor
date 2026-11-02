"""Three generators: two pair states at a common outside column (log §34.3z⁹⁰), z3.

Strict crossing triple, all meet rows. Columns t, v, z = t ⊓ v (glb, outside D), ⊤. Pair state (i,j,t) = (1,2,t):
F(m12, t) ≤ p2; v is p2-contracting with H = F(p2, v) ≤ p3 (the independent baseline), so (2,3,v) is a pair state.
At z both hold by monotonicity. Question: is the third pair state F(m13, z) ≤ p1 forced (which would close the
triangle at row m123)? Test SAT of its negation, and of each alternative for F(p3, z) (switch target)."""
import itertools
from z3 import *
def run(extra):
    P = ['p1', 'p2', 'p3']; M = {'m12': ['p1', 'p2'], 'm13': ['p1', 'p3'], 'm23': ['p2', 'p3'], 'b': P}
    rows = P + list(M); cols = ['top', 't', 'v', 'z']
    val = {(a, c): f"F[{a},{c}]" for a in rows for c in cols}
    E = ['bot'] + rows + cols + list(val.values())
    S = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    for a in E:
        S.add(le[a, a], le['bot', a], le[a, 'top'])
        for b_ in E:
            for c in E: S.add(Implies(And(le[a, b_], le[b_, c]), le[a, c]))
    inD = {a: Or([le[a, q] for q in P]) for a in E}
    for a, b_ in itertools.permutations(P, 2): S.add(Not(le[a, b_]))
    def glb(z, xs): S.add([le[z, x] for x in xs]); S.add([Implies(And([le[w, x] for x in xs]), le[w, z]) for w in E])
    for k, v in M.items(): glb(k, v)
    S.add(Not(le['m23', 'p1']), Not(le['m13', 'p2']), Not(le['m12', 'p3']))
    S.add([inD[a] for a in rows]); S.add([Not(inD[c]) for c in cols])
    for (a, c), x in val.items():
        for (a2, c2), x2 in val.items():
            if (a, c) != (a2, c2): S.add(Implies(And(le[a, a2], le[c, c2]), le[x, x2]))
        S.add(Not(le[x, a]), Not(le[c, x]))
    glb('z', ['t', 'v'])
    S.add(le[val['m12', 't'], 'p2'], le[val['p2', 'v'], 'v'], le[val['p2', 'v'], 'p3'])
    S.add(extra(le, val, inD))
    return S.check()
print("third pair state F(m13,z) <= p1 fails:", run(lambda le, val, inD: Not(le[val['m13', 'z'], 'p1'])))
print("F(p3, z) outside D:", run(lambda le, val, inD: Not(inD[val['p3', 'z']])))
print("F(p3, z) <= p1 (switch to (3,1,z)):", run(lambda le, val, inD: le[val['p3', 'z'], 'p1']))
print("third pair state holds (triangle):", run(lambda le, val, inD: le[val['m13', 'z'], 'p1']))
