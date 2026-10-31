"""The critical rectangle as a finite order-constraint model (log §34.3z⁵⁹), z3.

Elements: ⊥, ⊤; generators A = {p₁..p_a} and a new boundary element p* (all in D, maximal in D, pairwise incomparable);
B = {u₁..u_b} and u* (outside D, minimal outside D, pairwise incomparable); m = ⋀A, m' = m ⊓ p*, v = ⋁B,
v' = v ⊔ u* (glb/lub among the model's elements); values z00 = F(m, v), z10 = F(m', v), z01 = F(m, v'),
z11 = F(m', v') with the four monotonicity inequalities and no-witness at every cell (z ≰ row, col ≰ z).
The order is a preorder on the named elements (values may coincide with anything); D is a down-set.
Prints: the satisfiable side patterns (D-membership of z10, z00, z11, z01) and the status of candidate exchange
lemmas (VALID = negation unsat; FAILS = countermodel, printed in minimized form)."""
import itertools, sys
from z3 import *
a = int(sys.argv[1]) if len(sys.argv) > 1 else 2
b = int(sys.argv[2]) if len(sys.argv) > 2 else 2
A = [f"p{i}" for i in range(a)]; B = [f"u{j}" for j in range(b)]
E = ['bot', 'top'] + A + ['ps'] + B + ['us'] + ['m', "mp", 'v', "vu", 'z00', 'z10', 'z01', 'z11']
le = {(x, y): Bool(f"le_{x}_{y}") for x in E for y in E}
inD = {x: Bool(f"D_{x}") for x in E}
base = []
for x in E:
    base.append(le[x, x]); base.append(le['bot', x]); base.append(le[x, 'top'])
    for y in E:
        for w in E: base.append(Implies(And(le[x, y], le[y, w]), le[x, w]))
        base.append(Implies(And(le[x, y], inD[y]), inD[x]))                  # down-set
base += [inD['bot'], Not(inD['top'])]
P = A + ['ps']; U = B + ['us']
lt = lambda x, y: And(le[x, y], Not(le[y, x]))
for p in P:
    base.append(inD[p]); base += [Implies(lt(p, x), Not(inD[x])) for x in E]
for u in U:
    base.append(Not(inD[u])); base += [Implies(lt(x, u), inD[x]) for x in E]
for g, h in itertools.combinations(P, 2): base += [Not(le[g, h]), Not(le[h, g])]
for g, h in itertools.combinations(U, 2): base += [Not(le[g, h]), Not(le[h, g])]
def glb(z, xs): return [le[z, x] for x in xs] + [Implies(And([le[w, x] for x in xs]), le[w, z]) for w in E]
def lub(z, xs): return [le[x, z] for x in xs] + [Implies(And([le[x, w] for x in xs]), le[z, w]) for w in E]
base += glb('m', A) + glb('mp', ['m', 'ps']) + lub('v', B) + lub('vu', ['v', 'us'])
base += [le['z10', 'z00'], le['z00', 'z01'], le['z10', 'z11'], le['z11', 'z01']]
cell = {'z00': ('m', 'v'), 'z10': ('mp', 'v'), 'z01': ('m', 'vu'), 'z11': ('mp', 'vu')}
for z, (r, c) in cell.items(): base += [Not(le[z, r]), Not(le[c, z])]
cap = lambda z: If(inD[z], Or([le[z, p] for p in P]), Or([le[u, z] for u in U]))
capOld = lambda z: If(inD[z], Or([le[z, p] for p in A]), Or([le[u, z] for u in B]))
s = Solver(); s.add(base)
assert s.check() == sat
print(f"|A| = {a}, |B| = {b}")
print("side patterns (z10, z00, z11, z01 in D?):")
for pat in itertools.product((True, False), repeat=4):
    s.push(); s.add([inD[z] == t for z, t in zip(['z10', 'z00', 'z11', 'z01'], pat)])
    r = s.check(); s.pop()
    if r == sat: print("  ", ''.join('D' if t else 'U' for t in pat))
def test(name, hyp, concl):
    s.push(); s.add(hyp); s.add(Not(concl)); r = s.check()
    if r == unsat: print(f"VALID  {name}")
    else:
        mo = s.model()
        rel = sorted(f"{x}<{y}" for x in E for y in E if x != y and is_true(mo.eval(le[x, y])) and not is_true(mo.eval(le[y, x]))
                     and x not in ('bot',) and y != 'top')
        eq = sorted(f"{x}={y}" for x, y in itertools.combinations(E, 2) if is_true(mo.eval(le[x, y])) and is_true(mo.eval(le[y, x])))
        sides = {z: 'D' if is_true(mo.eval(inD[z])) else 'U' for z in cell}
        print(f"FAILS  {name}\n       sides {sides}; equalities {eq}\n       strict (non-⊥/⊤) {[r for r in rel if not r.startswith('bot') ]}")
    s.pop()
ext = [inD['z00'], Not(capOld('z00')), le['z00', 'ps'], Not(inD['z01']), Not(capOld('z01')), le['us', 'z01']]
test("X0: p* above an uncaptured z00 ∈ D captures z10", [inD['z00'], le['z00', 'ps']], cap('z10'))
test("X1: u* below an uncaptured z01 ∉ D captures z01 and z00 if z00 ∉ D", [Not(inD['z01']), le['us', 'z01']],
     And(cap('z01'), Implies(Not(inD['z00']), Or(cap('z00'), True))))
test("X2: after both extensions (p* captures z00, u* captures z01), z11 is captured", ext, cap('z11'))
test("X3: ... z11 is captured by p* or u* specifically", ext, Or(le['z11', 'ps'], le['us', 'z11']))
test("X4: ... z11 ∈ D (so p*-type capture is the only option)", ext, inD['z11'])
test("X5: ... z11 ∉ D", ext, Not(inD['z11']))
test("X6: ... z11 is comparable to z00", ext, Or(le['z11', 'z00'], le['z00', 'z11']))
test("X7: ... if z11 ∈ D it is captured by an old generator", ext + [inD['z11']], capOld('z11'))
