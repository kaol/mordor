"""Anchor-entry profiles and ko-transfer states (log §34.3z⁷⁷), z3.

Named partial models: a strictly crossing triple p1, p2, p3 (antichain; pairwise meets m_ij and triple meet b as
glbs, m_jk ≰ p_i; join anchors c_i = m_ij ∨ m_ik as lubs), or the control k = 2 (p1, p2, c1 = c2 = m12 = b).
Columns: ⊤ (and in test C a feedback pair u, u' = F(p_j, u)), plus the anchor orbits o_{i,k+1} = F(c_i, o_{i,k}) of each
column up to their entry into D. F is given on every row {p_i, c_i, m_ij, b} × every named column as named elements,
monotone, witness-free on cross cells. Proved global facts are imposed as constraints (sound, all checked in Lean):
  * anchor_sandwich at every column y with F(p_i, y) ≤ y whose c_i-orbit is named: entry not below p_i;
  * l4 (the n = 0 sandwich) at every named column outside D and row c_i.
Tests:
  A. which entry-time patterns (τ1, τ2, τ3) from ⊤ are consistent (Lean: (1,1,1) is not, contracting_simultaneous);
  B. ko-stuck profile from ⊤: every anchor transfers (label ∌ own index) and no transfer can be renewed
     (F(p_j, w_i) ≰ w_i for every j in the label of e_i, w_i the last outside orbit point), for each label profile;
  D. adding the meet x of the anchor last points of ⊤ (as a glb used as row and column): consistent, and x ∈ D
     is forced (Lean: lastpoints_no_common_lower);
  C. profile non-descent along a feedback step u → u' = F(p_j, u) ∉ D with u, u' incomparable:
     τ_i(u') ≥ τ_i(u) for all i and equal labels.
Run with argument k2 for the two-generator control (Cut proved: FGTwo.cut_two)."""
import itertools, sys
from z3 import *

K2 = 'k2' in sys.argv
IDX = ['1', '2'] if K2 else ['1', '2', '3']
P = ['p' + i for i in IDX]; C = ['c' + i for i in IDX]
MX = ['m12'] if K2 else ['m12', 'm13', 'm23']
ROWS = P + C + MX + ['b']

class Model:
    def __init__(self, columns, orbits, meet=None, role='rowcol', lemmas=True):
        """columns: list of base column names (outside D); orbits: dict (col, i) -> τ (entry time ≥ 1);
        meet: base column whose anchor last points get a named glb 'x', used as a row and as a column."""
        self.s = Solver(); s = self.s
        self.orb = {}
        cols = list(columns)
        for (y, i), t in orbits.items():
            pts = [y] + [f"o{y}_{i}_{k}" for k in range(1, t)]
            self.orb[y, i] = pts
            cols += pts[1:]
        rows = list(ROWS)
        if meet is not None and 'col' in role: cols.append('x')
        if meet is not None and 'row' in role: rows.append('x')
        self.cols = cols
        self.val = {(r, y): f"F[{r},{y}]" for r in rows for y in cols}
        E = ['bot', 'top'] + ROWS + [c for c in cols if c != 'top'] + list(self.val.values())
        if meet is not None and 'x' not in E: E.append('x')
        self.E = E
        le = self.le = {(a, c): Bool(f"le|{a}|{c}") for a in E for c in E}
        for a in E:
            s.add(le[a, a], le['bot', a], le[a, 'top'])
            for c in E:
                for d in E: s.add(Implies(And(le[a, c], le[c, d]), le[a, d]))
        self.inD = {a: Or([le[a, q] for q in P]) for a in E}
        s.add([Not(self.inD['top'])])
        for a, c in itertools.permutations(P, 2): s.add(Not(le[a, c]))
        def glb(z, xs): s.add([le[z, x] for x in xs]); s.add([Implies(And([le[w, x] for x in xs]), le[w, z]) for w in E])
        def lub(z, xs): s.add([le[x, z] for x in xs]); s.add([Implies(And([le[x, w] for x in xs]), le[z, w]) for w in E])
        if meet is not None: glb('x', [self.orb[meet, i][-1] for i in IDX])
        if K2:
            for z in ['m12', 'b', 'c1', 'c2']: glb(z, P)
        else:
            glb('m12', ['p1', 'p2']); glb('m13', ['p1', 'p3']); glb('m23', ['p2', 'p3']); glb('b', P)
            lub('c1', ['m12', 'm13']); lub('c2', ['m12', 'm23']); lub('c3', ['m13', 'm23'])
            s.add(Not(le['m23', 'p1']), Not(le['m13', 'p2']), Not(le['m12', 'p3']))
        for (r, y), v in self.val.items():
            for (r2, y2), v2 in self.val.items():
                if (r, y) != (r2, y2): s.add(Implies(And(le[r, r2], le[y, y2]), le[v, v2]))
            s.add(Implies(And(self.inD[r], Not(self.inD[y])), And(Not(le[v, r]), Not(le[y, v]))))
        eq = self.eq = lambda a, c: And(le[a, c], le[c, a])
        self.end = {}
        for (y, i), pts in self.orb.items():
            for k in range(len(pts) - 1): s.add(eq(pts[k + 1], self.val['c' + i, pts[k]]))
            s.add([Not(self.inD[q]) for q in pts])
            e = self.val['c' + i, pts[-1]]; self.end[y, i] = e
            s.add(self.inD[e])
            # anchor_sandwich: if some orbit point is p_i-contracting, the entry is not below p_i
            if lemmas: s.add(Implies(Or([le[self.val['p' + i, q], q] for q in pts]), Not(le[e, 'p' + i])))
        for y in (cols if lemmas else []):   # l4 at every named column
            for i in IDX:
                v = self.val['c' + i, y]
                s.add(Implies(And(Not(self.inD[y]), le[self.val['p' + i, y], y], self.inD[v]), Not(le[v, 'p' + i])))
    def label(self, e, L): return And([self.le[e, 'p' + j] if j in L else Not(self.le[e, 'p' + j]) for j in IDX])

def labels_for(i): return [set(c) for n in range(1, len(IDX)) for c in itertools.combinations([j for j in IDX if j != i], n)]
tag = 'k=2 control ' if K2 else ''

TESTS = [a for a in sys.argv[1:] if a in 'ABCD' and len(a) == 1] or ['A', 'B', 'C', 'D']
if 'A' in TESTS: print(f"== {tag}A. entry-time patterns from top")
for tau in (itertools.product([1, 2, 3], repeat=len(IDX)) if 'A' in TESTS else []):
    M = Model(['top'], {('top', i): t for i, t in zip(IDX, tau)})
    print(f"  tau={tau}: {M.s.check()}")

if 'B' in TESTS: print(f"== {tag}B. ko-stuck profiles from top (tau = 2 each; every transfer unrenewable)")
for Ls in (itertools.product(*[labels_for(i) for i in IDX]) if 'B' in TESTS else []):
    M = Model(['top'], {('top', i): 2 for i in IDX})
    for i, L in zip(IDX, Ls):
        e = M.end['top', i]; w = M.orb['top', i][-1]
        M.s.add(M.label(e, L))
        M.s.add([Not(M.le[M.val['p' + j, w], w]) for j in L])
    print(f"  labels={tuple(''.join(sorted(L)) for L in Ls)}: {M.s.check()}")
if K2 and 'B' in TESTS: print("  (no label sets exist for k = 2: every endpoint label must avoid both indices)")

if 'C' in TESTS: print(f"== {tag}C. profile non-descent along a feedback step u -> u' = F(p1, u)")
for tau in ([(1,) * len(IDX), (2,) * len(IDX)] if 'C' in TESTS else []):
    orbits = {(y, i): t for y in ['u', 'v'] for i, t in zip(IDX, tau)}
    M = Model(['u', 'v'], orbits)
    le = M.le
    M.s.add(M.eq('v', M.val['p1', 'u']), Not(le['u', 'v']), Not(le['v', 'u']))
    for i in IDX:
        eu, ev = M.end['u', i], M.end['v', i]
        M.s.add([le[ev, 'p' + j] == le[eu, 'p' + j] for j in IDX])
    print(f"  tau(u) = tau(u') = {tau}, equal labels: {M.s.check()}")

if 'D' in TESTS:
    print(f"== {tag}D. the meet x of the anchor last points of top, as a named glb (row and column)")
    pats = [(1, 1), (2, 2)] if K2 else [(1, 2, 2), (2, 2, 2), (1, 2, 3)]
    for tau in pats:
        M = Model(['top'], {('top', i): t for i, t in zip(IDX, tau)}, meet='top')
        r1 = M.s.check()
        M.s.push(); M.s.add(Not(M.inD['x'])); r2 = M.s.check(); M.s.pop()
        print(f"  tau={tau}: consistent -> {r1};  with x outside D -> {r2} (Lean: unsat, lastpoints_no_common_lower)")
    if not K2:
        print("  ablation for tau=(1,2,2): which ingredients the refutation uses")
        for role in ['rowcol', 'col', 'row', 'none']:
            for lem in [True, False]:
                M = Model(['top'], {('top', i): t for i, t in zip(IDX, (1, 2, 2))}, meet='top', role=role, lemmas=lem)
                M.s.add(M.inD['x'])   # sound: lastpoints_no_common_lower
                print(f"    x in D imposed, x as {role:6s}, sandwich/l4 imposed={lem}: {M.s.check()}")
