"""Minimal-boundary configurations of a sink (log §34.3z⁷⁹), z3, with a k = 2 control.

Named partial model: generators (k = 3 strictly crossing triple, or k = 2), pairwise meets, triple meet, join anchors
as glbs/lubs; a column v that is MINIMAL outside D (every named element strictly below v lies in D) and the column ⊤.
F is given on every row × {v, ⊤} as named elements, monotone, witness-free on cross cells; l4 is imposed at v.
Sink j at v: ¬Transfer_j(v) and F(p_j, v) ≰ v; generator a transfers at v; in k = 3 the third generator b transfers
(case I) or not (case II). Lower boundary of v:
  A-disjoint : v = x ∨ y, x, y ∈ D with disjoint labels (all label pairs tried),
  A-triangle : v = x01 ∨ x12 ∨ x02 with labels exactly {0,1}, {1,2}, {0,2}   (k = 3 only),
  B-jump     : every named w < v lies below B ∈ D, B < v, and the fixed point r = B ⊓ F(r, v) of jump_fixedpoint;
  R-rowfix   : (argument R) the row fixed point r = v ⊓ F(r, v), r < v, of minimal_row_fixedpoint, together with a
               cover x ∨ y = v of the given labels.
Printed: SAT/UNSAT per pattern. Usage: python3 boundary.py [k2] [R]"""
import itertools, sys
from z3 import *
K2 = 'k2' in sys.argv
IDX = ['0', '1'] if K2 else ['0', '1', '2']
P = ['p' + i for i in IDX]; C = ['c' + i for i in IDX]
MX = ['m01'] if K2 else ['m01', 'm02', 'm12']
BASE = P + C + MX + ['b']

def model(extra_rows, setup):
    rows = BASE + extra_rows; cols = ['v', 'top']
    val = {(r, y): f"F[{r},{y}]" for r in rows for y in cols}
    E = ['bot', 'top', 'v'] + rows + list(val.values())
    s = Solver(); le = {(a, c): Bool(f"le|{a}|{c}") for a in E for c in E}
    for a in E:
        s.add(le[a, a], le['bot', a], le[a, 'top'])
        for c in E:
            for d in E: s.add(Implies(And(le[a, c], le[c, d]), le[a, d]))
    inD = {a: Or([le[a, q] for q in P]) for a in E}
    s.add(Not(inD['top']), Not(inD['v']))
    for a, c in itertools.permutations(P, 2): s.add(Not(le[a, c]))
    def glb(z, xs): s.add([le[z, x] for x in xs]); s.add([Implies(And([le[w, x] for x in xs]), le[w, z]) for w in E])
    def lub(z, xs): s.add([le[x, z] for x in xs]); s.add([Implies(And([le[x, w] for x in xs]), le[z, w]) for w in E])
    if K2:
        for z in ['m01', 'b', 'c0', 'c1']: glb(z, P)
    else:
        glb('m01', ['p0', 'p1']); glb('m02', ['p0', 'p2']); glb('m12', ['p1', 'p2']); glb('b', P)
        lub('c0', ['m01', 'm02']); lub('c1', ['m01', 'm12']); lub('c2', ['m02', 'm12'])
        s.add(Not(le['m12', 'p0']), Not(le['m02', 'p1']), Not(le['m01', 'p2']))
    s.add([inD[r] for r in rows])
    for (r, y), w in val.items():
        for (r2, y2), w2 in val.items():
            if (r, y) != (r2, y2): s.add(Implies(And(le[r, r2], le[y, y2]), le[w, w2]))
        s.add(Not(le[w, r]), Not(le[y, w]))                                   # no witness (rows in D, columns out)
    for a in E:                                                                # v minimal outside D
        s.add(Implies(And(le[a, 'v'], Not(le['v', a])), inD[a]))
    for i in IDX:                                                              # l4 at v and at top
        for y in ['v', 'top']:
            w = val['c' + i, y]
            s.add(Implies(And(le[val['p' + i, y], y], inD[w]), Not(le[w, 'p' + i])))
    transfer = lambda i, y: Or([le[val['c' + i, y], 'p' + k] for k in IDX if k != i])
    ctx = dict(s=s, le=le, inD=inD, val=val, glb=glb, lub=lub, transfer=transfer, E=E)
    setup(ctx)
    return s.check()

def label(ctx, x, L): return [ctx['le'][x, 'p' + k] if k in L else Not(ctx['le'][x, 'p' + k]) for k in IDX]
def sink_ctx(j, a, b_tr):
    def f(ctx):
        s, le, val, tr = ctx['s'], ctx['le'], ctx['val'], ctx['transfer']
        s.add(Not(tr(j, 'v')), Not(le[val['p' + j, 'v'], 'v']), tr(a, 'v'))
        if not K2:
            b = [i for i in IDX if i not in (j, a)][0]
            s.add(tr(b, 'v') if b_tr else Not(tr(b, 'v')))
    return f
def nonempty(xs): return [set(c) for n in range(1, len(xs) + 1) for c in itertools.combinations(xs, n)]

j, a = ('1', '0') if K2 else ('2', '0')
cases = [('-', None)] if K2 else [('I (b transfers)', True), ('II (b does not)', False)]
tag = 'k=2 control ' if K2 else ''
ROWFIX = 'R' in sys.argv
for cname, btr in cases:
    print(f"== {tag}sink j={j}, a={a} transfers, case {cname}{' (row fixed point added)' if ROWFIX else ''}")
    seen = set()
    for Lx in nonempty(IDX):
        for Ly in nonempty(IDX):
            if Lx & Ly or (frozenset(Ly), frozenset(Lx)) in seen: continue
            seen.add((frozenset(Lx), frozenset(Ly)))
            def setup(ctx, Lx=Lx, Ly=Ly):
                sink_ctx(j, a, btr)(ctx); ctx['lub']('v', ['x', 'y'])
                ctx['s'].add(label(ctx, 'x', Lx) + label(ctx, 'y', Ly))
                if ROWFIX:
                    le = ctx['le']; ctx['s'].add(le['r', 'v'], Not(le['v', 'r'])); ctx['glb']('r', ['v', ctx['val']['r', 'v']])
            rows = ['x', 'y'] + (['r'] if ROWFIX else [])
            print(f"  A-disjoint labels {''.join(sorted(Lx))} | {''.join(sorted(Ly))}: {model(rows, setup)}")
    if ROWFIX: continue
    if not K2:
        def setup(ctx):
            sink_ctx(j, a, btr)(ctx); ctx['lub']('v', ['x01', 'x12', 'x02'])
            ctx['s'].add(label(ctx, 'x01', {'0', '1'}) + label(ctx, 'x12', {'1', '2'}) + label(ctx, 'x02', {'0', '2'}))
        print(f"  A-triangle: {model(['x01', 'x12', 'x02'], setup)}")
    def setup(ctx):
        s, le, val = ctx['s'], ctx['le'], ctx['val']
        sink_ctx(j, a, btr)(ctx)
        s.add(le['B', 'v'], Not(le['v', 'B']), le['r', 'B'])
        s.add([Implies(And(le[w, 'v'], Not(le['v', w])), le[w, 'B']) for w in ctx['E']])
        ctx['glb']('r', ['B', val['r', 'v']])
        s.add(Not(le[val['r', 'v'], 'B']))
    print(f"  B-jump: {model(['B', 'r'], setup)}")
