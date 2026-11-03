"""The dual finite-support boundary grid (log §34.3z⁹⁸), z3.

Atoms p_1..p_m (rows) and q_1..q_n (columns); p_A = ⋁_A p (lub), q_B = ⋀_B q (glb) for nonempty A, B. D is a
down-set on the named elements: p_A ∈ D for proper A, p_P ∉ D; q_B ∉ D for proper B, q_Q ∈ D (minimal supports).
First layer: z_{A,B} = F(p_A, q_B) for proper A, B (cross cells), plus the normalized boundary
F(p_P, q_B) = ⊤ and F(p_A, q_Q) = ⊥ (argument `noboundary` drops them; they are off the cross block).
Second layer (argument `layer2`): every first-layer value fed back as a row F(z, q_B) and as a column F(p_A, z), with
no witness conditional on membership. All cells monotone; no witness on cross cells only."""
import itertools, sys
from z3 import *
def run(m, n, boundary=True, layer2=False):
    Pi = list(range(1, m + 1)); Qj = list(range(1, n + 1))
    subs = lambda S: [frozenset(c) for r in range(1, len(S) + 1) for c in itertools.combinations(S, r)]
    PA = {A: "p" + "".join(map(str, sorted(A))) for A in subs(Pi)}
    QB = {B: "q" + "".join(map(str, sorted(B))) for B in subs(Qj)}
    fullP, fullQ = frozenset(Pi), frozenset(Qj)
    cells = {}
    for A in PA:
        for B in QB:
            if A != fullP and B != fullQ: cells[(PA[A], QB[B])] = f"z[{PA[A]},{QB[B]}]"
            elif boundary: cells[(PA[A], QB[B])] = f"z[{PA[A]},{QB[B]}]"
    first = [v for (r, c), v in cells.items()]
    if layer2:
        for (r, c), v in list(cells.items()):
            if r == PA[fullP] or c == QB[fullQ]: continue
            for B in QB:
                if B != fullQ: cells[(v, QB[B])] = f"F[{v},{QB[B]}]"
            for A in PA:
                if A != fullP: cells[(PA[A], v)] = f"F[{PA[A]},{v}]"
    E = list(dict.fromkeys(['bot', 'top'] + list(PA.values()) + list(QB.values()) + list(cells.values())))
    s = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    inD = {a: Bool(f"D|{a}") for a in E}
    for a in E:
        s.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            s.add(Implies(And(le[a, b], inD[b]), inD[a]))
            for c in E: s.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
    s.add(inD['bot'], Not(inD['top']))
    def lub(z, xs): s.add([le[x, z] for x in xs]); s.add([Implies(And([le[x, w] for x in xs]), le[z, w]) for w in E])
    def glb(z, xs): s.add([le[z, x] for x in xs]); s.add([Implies(And([le[w, x] for x in xs]), le[w, z]) for w in E])
    for A, nm in PA.items():
        if len(A) > 1: lub(nm, [PA[frozenset([i])] for i in A])
        s.add(inD[nm] if A != fullP else Not(inD[nm]))
    for B, nm in QB.items():
        if len(B) > 1: glb(nm, [QB[frozenset([j])] for j in B])
        s.add(Not(inD[nm]) if B != fullQ else inD[nm])
    for (r, c), v in cells.items():
        for (r2, c2), v2 in cells.items():
            if (r, c) != (r2, c2): s.add(Implies(And(le[r, r2], le[c, c2]), le[v, v2]))
        s.add(Implies(And(inD[r], Not(inD[c])), And(Not(le[v, r]), Not(le[c, v]))))
        if boundary and r == PA[fullP]: s.add(le['top', v])
        if boundary and c == QB[fullQ] and r != PA[fullP]: s.add(le[v, 'bot'])
    return s.check()
for m, n in [(2, 2), (2, 3), (3, 2), (3, 3)]:
    print(f"|P|={m}, |Q|={n}: first layer with normalized boundary {run(m, n)}", flush=True)
for m, n in [(2, 2), (2, 3), (3, 2)]:
    print(f"|P|={m}, |Q|={n}: with second layer {run(m, n, layer2=True)}", flush=True)
