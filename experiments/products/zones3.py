"""Zones with tameness that depends on the *type* of G (CEGAR over types).

Setting: L end-finite, K a finite lattice, G the two-sided reset on L x K, witness-free.
Anchors: rows s_i = (bot,i) (i in Ne) and t_i = (top,i) (i in Fu); columns s_j (j not in Ne)
and t_j (j not in Fu).  The *type* of G records, for every anchor cell, the class of the
first coordinate of its value (0 = bot, 1 = middle, 2 = top) and its layer.  Constraints:
monotone between comparable anchor cells, and no witness at anchor cells.

A value class (k,p,q) (an S_k value at a cell with row layer p, column layer q) is tame in a
type if one anchor box forces finitely many values or none:
  lower box (s_i,s_j), i<=p, j<=q :  z >= g   -> tame iff cls(g) != 0 or lay(g) not<= k
  upper box (t_i,t_j), p<=i, q<=j :  z <= g   -> tame iff cls(g) != 2 or k not<= lay(g)
  mixed box (s_i,t_j), i<=p, q<=j :  G(s_i,y) <= z <= G(x,t_j), both through g
        tame iff (cls(g) != 2 and lay(g) meet k <= i) or (cls(g) != 0 and j <= lay(g) join k)
Non-tame classes get a zone (lowered needs k not<= p, raised needs q not<= k); a raised class
below a lowered class (cells c <= d, layers k <= k') is forbidden.
For each type the zone problem must be satisfiable; tameness is monotone, so a type whose
tame set contains a solved one is skipped (blocking clause).
"""
import itertools, sys
from z3 import Int, Bool, Solver, Not, And, Or, Implies, sat, unsat, is_true, BoolVal
exec(open(__file__.replace('zones3.py', 'zones_check.py')).read().replace('if __name__ == "__main__"', 'if False'))

def analyse(K, le, name, only=None):
    idx = {a: n for n, a in enumerate(K)}
    bot = [a for a in K if all(le(a, b) for b in K)][0]
    top = [a for a in K if all(le(b, a) for b in K)][0]
    mid = [k for k in K if k not in (bot, top)]
    meet = lambda a, b: max((c for c in K if le(c, a) and le(c, b)), key=lambda c: sum(le(d, c) for d in K))
    join = lambda a, b: min((c for c in K if le(a, c) and le(b, c)), key=lambda c: sum(le(d, c) for d in K))
    ds = downsets(K, le); bad = []; ntypes = 0
    for Fu in ds:
        for Ne in ds:
            if not Fu <= Ne or bot not in Ne or top in Fu: continue
            if only and (sorted(Fu), sorted(Ne)) != only: continue
            rows = [('s', i) for i in K if i in Ne] + [('t', i) for i in K if i in Fu]
            cols = [('s', j) for j in K if j not in Ne] + [('t', j) for j in K if j not in Fu]
            ale = lambda u, v: le(u[1], v[1]) and not (u[0] == 't' and v[0] == 's')
            A = [(r, c) for r in rows for c in cols]
            cls = {a: Int(f"c_{a}") for a in A}; lay = {a: Int(f"l_{a}") for a in A}
            T = Solver()
            layle = lambda a, k: Or([lay[a] == idx[m] for m in K if le(m, k)])   # lay(a) <= k
            kle = lambda k, a: Or([lay[a] == idx[m] for m in K if le(k, m)])     # k <= lay(a)
            for a in A:
                T.add(cls[a] >= 0, cls[a] <= 2, lay[a] >= 0, lay[a] < len(K))
                (rt, i), (ct, j) = a
                T.add(Not(And(cls[a] == 0, layle(a, i))) if rt == 's' else Not(layle(a, i)))
                T.add(Not(kle(j, a)) if ct == 's' else Not(And(cls[a] == 2, kle(j, a))))
            for a in A:
                for b in A:
                    if a != b and ale(a[0], b[0]) and ale(a[1], b[1]):
                        T.add(Implies(cls[a] == 2, cls[b] == 2), Implies(cls[b] == 0, cls[a] == 0))
                        T.add(Or([And(lay[a] == idx[m], lay[b] == idx[m2]) for m in K for m2 in K if le(m, m2)]))
            cells = [(p, q) for p in K if p in Ne for q in K if q not in Fu]
            def tame_expr(k, c):
                p, q = c; ds_ = []
                for i in Ne:
                    if not le(i, p): continue
                    for j in K:
                        if j not in Ne and le(j, q):
                            a = (('s', i), ('s', j)); ds_.append(Or(cls[a] != 0, Not(layle(a, k))))
                        if j not in Fu and le(q, j):
                            a = (('s', i), ('t', j))
                            ds_.append(Or(And(cls[a] != 2, Or([And(lay[a] == idx[m], BoolVal(le(meet(m, k), i))) for m in K])),
                                          And(cls[a] != 0, Or([And(lay[a] == idx[m], BoolVal(le(j, join(m, k)))) for m in K]))))
                for i in Fu:
                    if not le(p, i): continue
                    for j in K:
                        if j not in Fu and le(q, j):
                            a = (('t', i), ('t', j)); ds_.append(Or(cls[a] != 2, Not(kle(k, a))))
                return Or(ds_) if ds_ else BoolVal(False)
            classes = [(k, c) for k in mid for c in cells]
            TE = {kc: tame_expr(*kc) for kc in classes}
            while T.check() == sat:
                ntypes += 1
                m = T.model()
                tame = {kc for kc in classes if is_true(m.eval(TE[kc], model_completion=True))}
                Z = Solver(); var = {}
                def zone(k, c):
                    if (k, c) in tame: return 'T'
                    p, q = c; lo, ra = not le(k, p), not le(q, k)
                    assert lo or ra, ("core not tame?", k, c)
                    if lo and not ra: return 'L'
                    if ra and not lo: return 'R'
                    if (k, c) not in var: var[(k, c)] = Bool(f"low_{k}_{c}")
                    return var[(k, c)]
                isL = lambda k, c: (lambda z: z if not isinstance(z, str) else z == 'L')(zone(k, c))
                isR = lambda k, c: (lambda z: Not(z) if not isinstance(z, str) else z == 'R')(zone(k, c))
                for (k, c) in classes:
                    for (k2, d) in classes:
                        if le(k, k2) and le(c[0], d[0]) and le(c[1], d[1]):
                            Z.add(Not(And(isR(k, c), isL(k2, d))))
                if Z.check() != sat:
                    bad.append((sorted(Fu), sorted(Ne), {str(a): (m[cls[a]], K[m[lay[a]].as_long()]) for a in A},
                                sorted(set(classes) - tame)))
                    break
                T.add(Or([Not(TE[kc]) for kc in tame]) if tame else BoolVal(False))
    print(name, f"{ntypes} tame patterns;", "all cut types OK" if not bad else f"{len(bad)} bad cut types")
    for b in bad[:2]:
        print("  cut type Fu =", b[0], "Ne =", b[1]); print("  type:", b[2]); print("  non-tame:", b[3])
    return bad

if __name__ == "__main__":
    for n in range(3, 8): analyse(*chain(n), f"C{n}")
    analyse(*boolean(3), "B3")
    C3sq = list(itertools.product(range(3), range(3)))
    analyse(C3sq, lambda a, b: a[0] <= b[0] and a[1] <= b[1], "C3xC3")
