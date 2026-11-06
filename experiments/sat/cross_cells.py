"""Cross-cell completion of the mixed-pivot ladder (log §34.3z¹¹⁸; brief Work Package C).

On top of axis_capture.setup at stage S6 (two- or three-row capture cycle, interior pivot c, new maximum q, its orbit,
joins, complement witnesses), add for a set X of old interior orbit points (default: all of them):
  y = ⋁ X (exact join); the cross rectangle F(c, x), F(q, x) (x ∈ X) and F(c, y), F(q, y), monotone with every other
  named cell and witness-free on every cross pair;
  output branches for every q-response z = F(q, x) and F(q, y): z ∈ D ⇒ a named maximal q_z ≥ z (maximal among named
  D-elements; incomparable with q is then forced), z ∉ D ⇒ a named minimal w_z ≤ z (minimal among named outside
  elements) with x ≰ w_z;
  'bnd': joins of all named maximal representatives (q, the rows, the q_z) pairwise ∉ D; meets of distinct minimal
  representatives (the w_z) pairwise ∈ D.
Partial models (F only on named cells); SAT is not a counterexample. Output: least H with SAT.
  python3 cross_cells.py [k2|k3|branch] [graph indices]   (k = 3: cross rectangle without the boundary layer)"""
import itertools
from z3 import *
import axis_capture as ac

def cross_pre(bnd, force=None):
    def pre(M, rows, orb, wname):
        X = [x for o in orb for x in o[1:-1]]                 # interior orbit points
        M.el('y'); M._X = X
        for r in ('c', 'q'):
            for x in X + ['y']:
                v = f"X[{r},{x}]"; M.el(v); M.cells[(r, x)] = v
        for x in X + ['y']:
            M.el(f"qz[{x}]", f"wz[{x}]")
        if bnd:
            reps = rows + ['q'] + [f"qz[{x}]" for x in X + ['y']]
            M._jn = {(a, b): f"Jn[{a},{b}]" for a, b in itertools.combinations(reps, 2)}
            mins = [f"wz[{x}]" for x in X + ['y']]
            M._mt = {(a, b): f"Mt[{a},{b}]" for a, b in itertools.combinations(mins, 2)}
            M.el(*M._jn.values(), *M._mt.values())
        orig = M.cons
        def extra(M2):
            S, le, D, eq = M2.S, M2.le, M2.D, M2.eq
            M2.lub('y', X)
            if force: S.add([D[f"X[q,{x}]"] if force == 'I' else Not(D[f"X[q,{x}]"]) for x in X + ['y']])
            for x in X + ['y']:
                z = f"X[q,{x}]"; qz = f"qz[{x}]"; wz = f"wz[{x}]"
                S.add(Implies(D[z], And(D[qz], le[z, qz], *[Implies(And(D[e], le[qz, e]), le[e, qz]) for e in M2.E if e != qz])))
                S.add(Implies(Not(D[z]), And(Not(D[wz]), le[wz, z], Not(le[x, wz]),
                                             *[Implies(And(Not(D[e]), le[e, wz]), le[wz, e]) for e in M2.E if e != wz])))
                # unused representative of the other branch: pin it to a harmless value
                S.add(Implies(D[z], eq(wz, 'top'))); S.add(Implies(Not(D[z]), eq(qz, 'bot')))
            if bnd:
                for (a, b), j in M2._jn.items():
                    M2.lub(j, [a, b]); S.add(Implies(And(D[a], D[b], Not(eq(a, b)), Not(eq(a, 'bot')), Not(eq(b, 'bot'))), Not(D[j])))
                for (a, b), m in M2._mt.items():
                    M2.glb(m, [a, b]); S.add(Implies(And(Not(D[a]), Not(D[b]), Not(eq(a, b)), Not(eq(a, 'top')), Not(eq(b, 'top'))), D[m]))
        M.cons = orig + [extra]
    return pre

def least_h(k, Es, G, bnd, Hmax=6, force=None):
    for H in range(1, Hmax + 1):
        for Eq in range(1, H + 1):
            if str(ac.setup(H, k, Es, G, 6, Eq, pre=cross_pre(bnd, force)).check()) == 'sat': return H, Eq
    return None, None

if __name__ == '__main__':
    import sys
    jobs = [(2, (2, 2)), (2, (2, 3)), (2, (3, 3))] + [(3, (2, 2, 2))]
    sel = sys.argv[1] if len(sys.argv) > 1 else 'all'
    if sel == 'branch':
        for f in ('I', 'II'):
            H, Eq = least_h(2, (2, 2), {(0, 1), (1, 0)}, True, force=f)
            print(f"k=2 E=(2,2) two-cycle, cross rectangle + boundary, all q-responses forced to branch {f}: least edge-height {H} (E_q={Eq})", flush=True)
        raise SystemExit
    gsel = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else None
    for k, Es in jobs:
        if sel == 'k2' and k != 2: continue
        if sel == 'k3' and k != 3: continue
        for gi, G in enumerate(ac.digraphs(k)):
            if gsel is not None and gi not in gsel: continue
            for bnd in ((False, True) if k == 2 else (False,)):
                H, Eq = least_h(k, Es, G, bnd)
                print(f"k={k} E={Es} graph={sorted(G)} cross rectangle{' + boundary joins/meets' if bnd else ''}: "
                      f"least edge-height {H} (E_q={Eq})", flush=True)
