"""Independent row-orbit baseline, two generators (log §34.3z⁹⁰), z3.

Generators px, py, m = px ⊓ py. The g = F(py, ·)-orbit of ⊤ (N steps, last point v, H = F(py, v) ≤ px).
Terminal pair state at t: e = F(m, t) ≤ py, q = F(py, t) ∉ D (column), d = t ⊓ q ∈ D.
b = F(m, v) ≤ H; z = t ⊓ v (glb, in D, label tried), u = t ⊔ v (lub), w = e ⊔ b (lub, as a column).
Rows px, py, m, z, e, b, H, d; columns ⊤, g-orbit points, t, q, u, w. F on every row × column, monotone, witness-free.
No sandwich. Also: the m-orbit of ⊤ entering at step 2 with each label. Equal entry times (N = 1) force the label px
(net_sync: h^n(⊤) ≤ g^n(⊤) because m ≤ py); staggered times (N = 2) leave it free."""
import itertools, sys
from z3 import *
def run(N, zlab, dlab, mtop=None):
    P = ['px', 'py']
    rows = P + ['m', 'z', 'e', 'b', 'H', 'd']
    gorb = ['top'] + [f"g{k}" for k in range(1, N + 1)]          # g_N = v
    cols = gorb + ['t', 'q', 'u', 'w'] + (['o1'] if mtop else [])
    val = {(a, c): f"F[{a},{c}]" for a in rows for c in cols}
    E = ['bot'] + rows + cols + list(val.values())
    E = list(dict.fromkeys(E))
    S = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    for a in E:
        S.add(le[a, a], le['bot', a], le[a, 'top'])
        for b_ in E:
            for c in E: S.add(Implies(And(le[a, b_], le[b_, c]), le[a, c]))
    inD = {a: Or([le[a, q] for q in P]) for a in E}
    S.add(Not(le['px', 'py']), Not(le['py', 'px']))
    def glb(z, xs): S.add([le[z, x] for x in xs]); S.add([Implies(And([le[w_, x] for x in xs]), le[w_, z]) for w_ in E])
    def lub(z, xs): S.add([le[x, z] for x in xs]); S.add([Implies(And([le[x, w_] for x in xs]), le[z, w_]) for w_ in E])
    glb('m', P)
    S.add([inD[a] for a in rows]); S.add([Not(inD[c]) for c in cols])
    for (a, c), x in val.items():
        for (a2, c2), x2 in val.items():
            if (a, c) != (a2, c2): S.add(Implies(And(le[a, a2], le[c, c2]), le[x, x2]))
        S.add(Not(le[x, a]), Not(le[c, x]))
    eq = lambda a, b_: And(le[a, b_], le[b_, a])
    v = gorb[-1]
    for k in range(N): S.add(eq(gorb[k + 1], val['py', gorb[k]]))
    S.add(eq('H', val['py', v]), le['H', 'px'])
    S.add(eq('b', val['m', v]))
    S.add(eq('e', val['m', 't']), le['e', 'py'], eq('q', val['py', 't']))
    glb('d', ['t', 'q']); S.add(le['d', dlab])
    glb('z', ['t', v]); S.add(le['z', zlab])
    lub('u', ['t', v]); lub('w', ['e', 'b'])
    if mtop:
        S.add(eq('o1', val['m', 'top']), le[val['m', 'o1'], mtop])          # m-orbit of top enters at step 2
    return S.check()
for N in [1, 2]:
    for zl in ['px', 'py']:
        for dl in ['px', 'py']:
            print(f"N={N}, z below {zl}, d below {dl}: {run(N, zl, dl)}", flush=True)
for N in [1, 2]:
    for ml in ['px', 'py']:
        print(f"N={N}, z below px, d below px, m-orbit of top entering at step 2 below {ml} (no sandwich): "
              f"{run(N, 'px', 'px', ml)}", flush=True)
