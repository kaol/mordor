"""Capturing rows have unconstrained orbits (log §34.3z¹¹⁵).

Preorder model with exact meets. Old rows g1, g2 ∈ D with orbits γ1, γ2 from ⊤, first entry at time 2 each.
Grid columns W(a,b) = γ1(a) ∧ γ2(b). The capturing row c is an uncaptured D-column of the old grid (c ≰ g1, c ≰ g2),
chosen among the W(a,b); its orbit δ(n) = F(c,·)^n(⊤) first enters D at time E.
Question: which E are realizable with no witness on every cell?  A dominated row enters no later than its dominator
(`dominated_entry_no_later`), so E > 2 means c's orbit is bounded by no old orbit.
Controls: E > 2 together with δ(n) ≤ γ1(n) for all n (orbit domination) must be UNSAT; base without c must be SAT."""
import sys
from z3 import *

def run(E, mode='free', H=None):
    G = 3                                                   # γ_i(0..2), entry at 2
    g1 = ['top', 'y1', 'y2']; g2 = ['top', 'z1', 'z2']
    dl = ['top'] + [f"d{n}" for n in range(1, E + 1)]
    def wn(a, b):
        if a == 0 and b == 0: return 'top'
        if b == 0: return g1[a]
        if a == 0: return g2[b]
        return f"W{a}{b}"
    grid = [wn(a, b) for a in range(G) for b in range(G)]
    rows = ['g1', 'g2', 'c']
    cols = list(dict.fromkeys(grid + dl))
    cell = {(r, x): f"F[{r},{x}]" for r in rows for x in cols}
    E_ = list(dict.fromkeys(['bot', 'top'] + rows + cols + list(cell.values())))
    s = Solver(); le = {(x, y): Bool(f"le|{x}|{y}") for x in E_ for y in E_}; inD = {x: Bool(f"D|{x}") for x in E_}
    for x in E_:
        s.add(le[x, x], le['bot', x], le[x, 'top'])
        for y in E_:
            for z in E_: s.add(Implies(And(le[x, y], le[y, z]), le[x, z]))
            s.add(Implies(And(le[x, y], inD[y]), inD[x]))
    eq = lambda x, y: And(le[x, y], le[y, x])
    def glb(z, q): s.add([le[z, x] for x in q]); s.add([Implies(And([le[w, x] for x in q]), le[w, z]) for w in E_])
    s.add(inD['bot'], Not(inD['top']), inD['g1'], inD['g2'])
    for a in range(1, G):
        for b in range(1, G): glb(wn(a, b), [g1[a], g2[b]])
    for n in range(G - 1):
        s.add(eq(cell[('g1', g1[n])], g1[n + 1])); s.add(eq(cell[('g2', g2[n])], g2[n + 1]))
    s.add(Not(inD['y1']), inD['y2'], Not(inD['z1']), inD['z2'])
    for (r, x), v in cell.items():
        for (r2, x2), v2 in cell.items():
            if (r, x) != (r2, x2): s.add(Implies(And(le[r, r2], le[x, x2]), le[v, v2]))
        s.add(Implies(And(inD[r], Not(inD[x])), And(Not(le[v, r]), Not(le[x, v]))))
    if mode == 'base':
        return s.check()
    # capturing row: an uncaptured D-column of the old grid
    s.add(Or([eq('c', w) for w in grid if w != 'top']))
    s.add(inD['c'], Not(le['c', 'g1']), Not(le['c', 'g2']))
    for n in range(E): s.add(eq(cell[('c', dl[n])], dl[n + 1]))
    s.add([Not(inD[x]) for x in dl[1:E]]); s.add(inD[dl[E]])
    if mode in ('nondeg', 'nondeg_dominated'):
        s.add(Not(le['y2', 'z2']), Not(le['z2', 'y2']), Not(eq('c', 'y2')), Not(eq('c', 'z2')))
    if mode in ('dominated', 'nondeg_dominated'):
        s.add([le[dl[n], g1[min(n, G - 1)]] for n in range(1, E + 1)])
    r = s.check()
    if r == sat and mode in ('free', 'nondeg'):
        mo = s.model(); ev = lambda b: is_true(mo.eval(b, model_completion=True))
        cw = [w for w in grid if ev(le['c', w]) and ev(le[w, 'c'])]
        return r, cw
    return r

if __name__ == '__main__':
    print(f"base (two old rows, entries at 2, no capturing row): {run(1, 'base')}", flush=True)
    for E in (1, 2, 3, 4):
        print(f"capturing row c (uncaptured D-column), δ first entry at {E}: {run(E)}", flush=True)
    for E in (1, 2, 3, 4):
        print(f"non-degenerate (y2 ∥ z2, c ≢ y2, z2), δ first entry at {E}: {run(E, 'nondeg')}", flush=True)
    for E in (3, 4):
        print(f"control (non-degenerate): δ entry at {E} with δ(n) ≤ γ1(n) imposed: {run(E, 'nondeg_dominated')}", flush=True)
    for E in (3, 4):
        print(f"control: δ entry at {E} with δ(n) ≤ γ1(n) imposed (orbit domination): {run(E, 'dominated')}", flush=True)
