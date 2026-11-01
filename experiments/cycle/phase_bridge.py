"""Diagnostic model for the conjectured global phase bridge (log §34.3z⁷⁶), z3.

A strictly crossing triple p1, p2, p3 (antichain; pairwise meets m_ij and the triple meet b as glbs, with
m_jk ≰ p_i; join anchors c_i = m_ij ∨ m_ik as lubs), a generator cycle u_0 → u_1 → u_2 → u_0 under the word
(1, 2, 3) (u_{k+1} = F(p_{i_k}, u_k)), and the anchor cycle x_0 → x_1 → x_2 → x_0 under (c_1, c_2, c_3) with
x_k ≤ u_k. F is given on all rows {p_i, c_i, m_ij, b} × columns {u_k, x_k} as named elements, monotone over the
model's order (which is a preorder; values may coincide), and witness-free on every cross cell.
Question: can BOTH alternatives of the bridge fail at every phase,
  ¬ (u_{k+1} ≤ u_k)  and  ¬ (F(c_{i_{k+1}}, u_{k+1}) ≤ p_{i_{k+1}}),
with all u_k, x_k outside D (Branch B), or with the anchor cycle entering D (Branch A)?"""
import itertools, sys
from z3 import *
K2 = 'k2' in sys.argv          # control: two generators (Cut proved, FGTwo.cut_two), word (1, 2), anchor c_1 = c_2 = m12
if K2:
    P = ['p1', 'p2']; Mx = ['m12']; C = ['c1', 'c2']; ROWS = P + C + Mx + ['b']
    U = ['u0', 'u1']; X = ['x0', 'x1']
else:
    P = ['p1', 'p2', 'p3']; Mx = ['m12', 'm13', 'm23']; C = ['c1', 'c2', 'c3']; ROWS = P + C + Mx + ['b']
    U = ['u0', 'u1', 'u2']; X = ['x0', 'x1', 'x2']
COLS = U + X; R = len(U)
VAL = {(r, y): f"F[{r},{y}]" for r in ROWS for y in COLS}
E = ['bot', 'top'] + ROWS + COLS + list(VAL.values())
le = {(a, b_): Bool(f"le|{a}|{b_}") for a in E for b_ in E}
s = Solver()
for a in E:
    s.add(le[a, a], le['bot', a], le[a, 'top'])
    for b_ in E:
        for c in E: s.add(Implies(And(le[a, b_], le[b_, c]), le[a, c]))
inD = {a: Or([le[a, q] for q in P]) for a in E}
s.add([Not(le['top', q]) for q in P])
for a_, b_ in itertools.permutations(P, 2): s.add(Not(le[a_, b_]))
def glb(z, xs): s.add([le[z, x] for x in xs]); s.add([Implies(And([le[w, x] for x in xs]), le[w, z]) for w in E])
def lub(z, xs): s.add([le[x, z] for x in xs]); s.add([Implies(And([le[x, w] for x in xs]), le[z, w]) for w in E])
if K2:
    glb('m12', ['p1', 'p2']); glb('b', P); glb('c1', ['p1', 'p2']); glb('c2', ['p1', 'p2'])
else:
    glb('m12', ['p1', 'p2']); glb('m13', ['p1', 'p3']); glb('m23', ['p2', 'p3']); glb('b', P)
    lub('c1', ['m12', 'm13']); lub('c2', ['m12', 'm23']); lub('c3', ['m13', 'm23'])
    s.add(Not(le['m23', 'p1']), Not(le['m13', 'p2']), Not(le['m12', 'p3']))           # strict crossing
for (r, y), v in VAL.items():
    for (r2, y2), v2 in VAL.items():
        if (r, y) != (r2, y2): s.add(Implies(And(le[r, r2], le[y, y2]), le[v, v2]))
    s.add(Implies(Not(inD[y]), And(Not(le[v, r]), Not(le[y, v]))))                  # no witness (rows are in D)
eq = lambda a, b_: And(le[a, b_], le[b_, a])
word = ['1', '2'] if K2 else ['1', '2', '3']
for k in range(R):
    i = word[k]; k1 = (k + 1) % R
    s.add(eq(U[k1], VAL[('p' + i, U[k])]), eq(X[k1], VAL[('c' + i, X[k])]), le[X[k], U[k]])
    s.add(Not(inD[U[k]]))
bridge_fails = [And(Not(le[U[(k + 1) % R], U[k]]), Not(le[VAL[('c' + word[(k + 1) % R], U[(k + 1) % R])], 'p' + word[(k + 1) % R]]))
                for k in range(R)]
for name, extra in [("Branch B (anchor cycle outside D)", [Not(inD[x]) for x in X]),
                    ("Branch A (anchor cycle meets D)", [Or([inD[x] for x in X])])]:
    s.push(); s.add(bridge_fails + extra); r = s.check()
    print(f"{'k=2 control ' if K2 else ''}{name}: bridge fails at every phase -> {r}")
    if r == sat:
        mo = s.model()
        print("   u-states pairwise:", {f"{a}<={b_}": is_true(mo.eval(le[a, b_])) for a, b_ in itertools.permutations(U, 2)})
        print("   anchor states in D:", {x: is_true(mo.eval(inD[x])) for x in X})
    s.pop()
