"""Pivot replacement with join compression, two steps with orbit provenance (log §34.3z¹¹³).

Preorder model with exact meets/joins (Dedekind–MacNeille completes a quotient):
  step 1: one row g ∈ D, orbit γ(n) = F(g, ·)^n(⊤) with first entry at γ(2); the relative pivot is c1 = γ(2)
          (Alternative II, h1 = p_T = γ(2)); c1 is uncaptured: c1 ≰ g.
  step 2: rows {g, c1}; orbit δ(n) = F(c1, ·)^n(⊤) of the new row with first entry at δ(Nδ+1); grid columns
          W(a, b) = γ(a) ∧ δ(b); the pivot c2 is some grid column in D captured by neither g nor c1
          (nor the running join J1 = c1), with Alternative I or II for some nonempty T ⊆ {g, c1}.
  join compression forces C = c1 ∨ c2 ∉ D (Case II).
Cells: rows {g, c1, μ = g ∧ c1, rows T-meets} × all named columns, monotone; no witness on every cross cell.
Question: is this SAT, i.e. can two replacement steps reach Case II with no witness? Also: does C ≤ F(μ, C) hold?"""
import itertools, sys
from z3 import *

def run(Nd, alt, extra_expand=False):
    gam = ['top', 'y1', 'y2']                       # γ(0..2): entry at 2
    dl = ['top'] + [f"d{n}" for n in range(1, Nd + 2)]  # δ(0..Nd+1)
    box = [(a, b) for a in range(3) for b in range(Nd + 2)]
    def wn(a, b):
        if a == 0 and b == 0: return 'top'
        if b == 0: return gam[a]
        if a == 0: return dl[b]
        return f"W{a}{b}"
    rows = ['g', 'c1', 'mu']
    cols = list(dict.fromkeys([wn(a, b) for a, b in box] + ['C']))
    cell = {(r, c): f"F[{r},{c}]" for r in rows for c in cols}
    E = list(dict.fromkeys(['bot', 'top'] + rows + cols + ['c2'] + list(cell.values())))
    s = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}; inD = {a: Bool(f"D|{a}") for a in E}
    for a in E:
        s.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            for c in E: s.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
            s.add(Implies(And(le[a, b], inD[b]), inD[a]))
    eq = lambda a, b: And(le[a, b], le[b, a])
    def glb(z, q): s.add([le[z, x] for x in q]); s.add([Implies(And([le[w, x] for x in q]), le[w, z]) for w in E])
    def lub(z, q): s.add([le[x, z] for x in q]); s.add([Implies(And([le[x, w] for x in q]), le[z, w]) for w in E])
    s.add(inD['bot'], Not(inD['top']))
    s.add(eq('c1', 'y2'))                           # step-1 pivot = first-entry point of γ
    glb('mu', ['g', 'c1'])
    for a, b in box:
        if a > 0 and b > 0: glb(wn(a, b), [gam[a], dl[b]])
    # orbit facts
    for n in range(2): s.add(eq(cell[('g', gam[n])], gam[n + 1]))
    for n in range(Nd + 1): s.add(eq(cell[('c1', dl[n])], dl[n + 1]))
    s.add(Not(inD['y1']), inD['y2']); s.add([Not(inD[x]) for x in dl[1:Nd + 1]]); s.add(inD[dl[Nd + 1]])
    s.add(inD['g']); s.add(Not(le['c1', 'g']))       # c1 uncaptured by g
    # step-2 pivot c2: a D-valued grid column, uncaptured by g and c1
    choices = [wn(a, b) for a, b in box if (a, b) != (0, 0)]
    s.add(Or([eq('c2', w) for w in choices]))
    s.add(inD['c2'], Not(le['c2', 'g']), Not(le['c2', 'c1']))
    # its alternative, for T in {g}, {c1}, {g, c1} (rows g, c1, mu)
    lub('C', ['c1', 'c2']); s.add(Not(inD['C']))    # join compression: Case II
    # monotone cells, no witness
    for (r, c), v in cell.items():
        for (r2, c2_), v2 in cell.items():
            if (r, c) != (r2, c2_): s.add(Implies(And(le[r, r2], le[c, c2_]), le[v, v2]))
        s.add(Implies(And(inD[r], Not(inD[c])), And(Not(le[v, r]), Not(le[c, v]))))
    # c2 as a column: its cells are those of the grid column it equals (monotonicity handles equal elements)
    if alt == 'I':   # F(m_T, c2) <= m_T for some T: rows g, c1, mu
        s.add(Or([And(eq('c2', w), le[cell[(r, w)], r]) for w in choices for r in rows]))
    elif alt == 'II':  # c2 lies past the entry of the T-orbits: c2 = a column with a=2 (γ) or b=Nd+1 (δ)
        s.add(Or([eq('c2', wn(a, b)) for a, b in box if a == 2 or b == Nd + 1]))
    if extra_expand: s.add(le['C', cell[('mu', 'C')]])
    r = s.check()
    return r, (s.model() if r == sat else None), le, inD, cell, choices

if __name__ == '__main__':
    for Nd in (0, 1):
        for alt in ('I', 'II'):
            r, mo, le, inD, cell, choices = run(Nd, alt)
            msg = f"two replacement steps, δ entry at {Nd + 1}, step-2 Alternative {alt}, Case II (c1 ∨ c2 ∉ D), no witness: {r}"
            if r == sat:
                ev = lambda b: is_true(mo.eval(b, model_completion=True))
                c2 = [w for w in choices if ev(le['c2', w]) and ev(le[w, 'c2'])]
                msg += f" | c2 = {c2[0] if c2 else '?'}; C ≤ F(μ, C): {ev(le['C', cell[('mu', 'C')]])}"
            print(msg, flush=True)
    r = run(0, 'I', extra_expand=True)[0]
    print(f"control: additionally impose C ≤ F(μ, C) (a witness at (μ, C)): {r}", flush=True)
