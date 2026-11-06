"""Dominated-row refinement (log §34.3z¹¹⁴).

Preorder model with exact meets. Old row g ∈ D, orbit γ(n) = F(g,·)^n(⊤), first entry at γ(2).
New row h ≤ g, h ∈ D, orbit δ(n) = F(h,·)^n(⊤), first entry at δ(Nd+1). Grid columns W(a,b) = γ(a) ∧ δ(b).
Lean (DominatedRows): δ(b) ≤ γ(b), hence W(a,b) ≤ P := γ(max(a,b)) (old parent); a new row captures nothing g does not.
Query, per pivot position (a,b): is there a no-witness model where W(a,b) ∈ D is uncaptured (≰ g, ≰ h), and is its
parent P in D or outside D?  Controls: δ(b) ≰ γ(b) (must be UNSAT); P ≤ g with W(a,b) uncaptured (must be UNSAT)."""
import sys
from z3 import *

def run(Nd, a, b, mode):
    Ng = 1
    gam = ['top'] + [f"y{n}" for n in range(1, Ng + 2)]
    dl = ['top'] + [f"d{n}" for n in range(1, Nd + 2)]
    A, B = len(gam), len(dl)
    def wn(i, j):
        if i == 0 and j == 0: return 'top'
        if j == 0: return gam[i]
        if i == 0: return dl[j]
        return f"W{i}{j}"
    rows = ['g', 'h']
    cols = list(dict.fromkeys(wn(i, j) for i in range(A) for j in range(B)))
    cell = {(r, c): f"F[{r},{c}]" for r in rows for c in cols}
    E = list(dict.fromkeys(['bot', 'top'] + rows + cols + list(cell.values())))
    s = Solver(); le = {(x, y): Bool(f"le|{x}|{y}") for x in E for y in E}; inD = {x: Bool(f"D|{x}") for x in E}
    for x in E:
        s.add(le[x, x], le['bot', x], le[x, 'top'])
        for y in E:
            for z in E: s.add(Implies(And(le[x, y], le[y, z]), le[x, z]))
            s.add(Implies(And(le[x, y], inD[y]), inD[x]))
    eq = lambda x, y: And(le[x, y], le[y, x])
    def glb(z, q): s.add([le[z, x] for x in q]); s.add([Implies(And([le[w, x] for x in q]), le[w, z]) for w in E])
    s.add(inD['bot'], Not(inD['top']), inD['g'], inD['h'], le['h', 'g'])
    for i in range(1, A):
        for j in range(1, B): glb(wn(i, j), [gam[i], dl[j]])
    for n in range(A - 1): s.add(eq(cell[('g', gam[n])], gam[n + 1]))
    for n in range(B - 1): s.add(eq(cell[('h', dl[n])], dl[n + 1]))
    s.add([Not(inD[x]) for x in gam[1:Ng + 1]]); s.add(inD[gam[Ng + 1]])
    s.add([Not(inD[x]) for x in dl[1:Nd + 1]]); s.add(inD[dl[Nd + 1]])
    for (r, c), v in cell.items():
        for (r2, c2), v2 in cell.items():
            if (r, c) != (r2, c2): s.add(Implies(And(le[r, r2], le[c, c2]), le[v, v2]))
        s.add(Implies(And(inD[r], Not(inD[c])), And(Not(le[v, r]), Not(le[c, v]))))
    if mode == 'base':
        return s.check()
    if mode == 'orbit_control':
        s.add(Or([Not(le[dl[j], gam[j]]) for j in range(1, min(A, B))]))
        return s.check()
    c = wn(a, b); P = gam[min(max(a, b), A - 1)] if max(a, b) < A else gam[A - 1]
    s.add(inD[c], Not(le[c, 'g']), Not(le[c, 'h']))
    if mode == 'P_in_D': s.add(inD[P])
    elif mode == 'P_out': s.add(Not(inD[P]))
    elif mode == 'P_captured': s.add(le[P, 'g'])
    return s.check()

if __name__ == '__main__':
    for Nd in (0, 1, 2):
        print(f"base consistency (Nd={Nd}, δ entry {Nd + 1} vs γ entry 2): {run(Nd, 0, 0, 'base')}", flush=True)
        print(f"control (Nd={Nd}): some δ(b) ≰ γ(b): {run(Nd, 0, 0, 'orbit_control')}", flush=True)
        if Nd >= 2: continue
        for a in range(3):
            for b in range(Nd + 2):
                if (a, b) == (0, 0): continue
                res = {m: run(Nd, a, b, m) for m in ('P_in_D', 'P_out', 'P_captured')}
                print(f"Nd={Nd} pivot W({a},{b}): uncaptured D-pivot with parent ∈ D: {res['P_in_D']}; "
                      f"parent ∉ D: {res['P_out']}; control parent ≤ g: {res['P_captured']}", flush=True)
