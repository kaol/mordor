"""Local realizability of the minimal incompatible admissibility system (log §34.3z¹⁰⁷).
Find a finite partial order with exact meets/joins for the named elements, a down-set D, and the nine cell
values z(A, B) = F(⋀A, ⋁B), A ⊆ {p0, p1}, B ⊆ {u0, u1}, such that
  p0, p1 ∈ D are maximal among named elements of D, u0, u1 ∉ D are minimal among named elements outside D,
  F is monotone on the cells, no witness at every cell, and z ≤ p, u ≤ z hold EXACTLY as in the system.
The Dedekind–MacNeille completion keeps the existing meets and joins, so a model is a bounded lattice with D
the down-closure of the named D-elements; F extends monotonically by F(x, y) = ⋁{z(A,B) : ⋀A ≤ x, ⋁B ≤ y} ∨ ⊥."""
import itertools
from z3 import *
P = ['p0', 'p1']; U = ['u0', 'u1']
def subsets(xs): return [tuple(c) for r in range(1, len(xs) + 1) for c in itertools.combinations(xs, r)]
cells = [(A, B) for A in subsets(P) for B in subsets(U)]
xs = {('p0',): 'p0', ('p1',): 'p1', ('p0', 'p1'): 'm'}; ys = {('u0',): 'u0', ('u1',): 'u1', ('u0', 'u1'): 'j'}
zname = {c: f"z_{''.join(c[0])}_{''.join(c[1])}" for c in cells}
E = ['bot', 'top', 'p0', 'p1', 'm', 'u0', 'u1', 'j'] + list(zname.values())
s = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}; inD = {a: Bool(f"D|{a}") for a in E}
for a in E:
    s.add(le[a, a], le['bot', a], le[a, 'top'])
    for b in E:
        if a != b: s.add(Not(And(le[a, b], le[b, a])))  # antisymmetry: distinct names are distinct elements
        for c in E: s.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
        s.add(Implies(And(le[a, b], inD[b]), inD[a]))
def glb(z, xs_): s.add([le[z, q] for q in xs_]); s.add([Implies(And([le[w, q] for q in xs_]), le[w, z]) for w in E])
def lub(z, xs_): s.add([le[q, z] for q in xs_]); s.add([Implies(And([le[q, w] for q in xs_]), le[z, w]) for w in E])
glb('m', ['p0', 'p1']); lub('j', ['u0', 'u1'])
s.add(inD['p0'], inD['p1'], Not(inD['u0']), Not(inD['u1']), Not(inD['top']), inD['bot'])
for p in P: s.add([Not(And(le[p, w], inD[w])) for w in E if w != p])          # p maximal among named D
for u in U: s.add([Not(And(le[w, u], Not(inD[w]))) for w in E if w != u])    # u minimal among named outside
s.add(Not(le['p0', 'p1']), Not(le['p1', 'p0']), Not(le['u0', 'u1']), Not(le['u1', 'u0']))
SP = {c: set() for c in cells}; SU = {c: set() for c in cells}
SU[(('p0',), ('u0', 'u1'))] = {'u1'}
for B in subsets(U): SP[(('p0', 'p1'), B)] = {'p0'}
for c in cells:
    z = zname[c]; x = xs[c[0]]; y = ys[c[1]]
    s.add(Not(le[z, x]), Not(le[y, z]))                                     # no witness at the cell
    for p in P: s.add(le[z, p] if p in SP[c] else Not(le[z, p]))
    for u in U: s.add(le[u, z] if u in SU[c] else Not(le[u, z]))
    for c2 in cells:                                                         # monotone F on cells
        if set(c2[0]) <= set(c[0]) and set(c[1]) <= set(c2[1]): s.add(le[z, zname[c2]])
r = s.check(); print("locally realizable:", r)
if r == sat:
    mo = s.model(); ev = lambda b: is_true(mo.eval(b, model_completion=True))
    for c in cells:
        z = zname[c]
        ups = [w for w in E if w != z and ev(le[z, w]) and w in ('p0', 'p1', 'j', 'u0', 'u1', 'top')]
        print(f"  {z}: in D={ev(inD[z])}; below {ups}")
