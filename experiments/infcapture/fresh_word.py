"""Fresh-word pivot monotonicity (log §34.3z¹⁰⁹, brief "revision-tolerant pivot research").

Lemma A (conjectural). Pivot z* of a good word for (P, U):
  case 1: z* ∈ D, p ∈ Max D with z* ≤ p  ⇒  some good word of (P ∪ {p}, U) has pivot z' with z* ≤ z', z' ∈ D;
  case 2: z* ∉ D, u ∈ Min Dᶜ with u ≤ z*  ⇒  some good word of (P, U ∪ {u}) has pivot z' ≤ z*, z' ∉ D.
The new word may be arbitrary (any admissible selectors, any word). We build a finite partial order with exact
meets/joins (Dedekind–MacNeille completes it to a lattice), a down-set D, maximal/minimal representatives, cell
values z(A, B) = F(⋀A, ⋁B) monotone, no witness on every cell of the enlarged universe, the old pivot data, and the
REFUTING constraint "every balanced cell other than the old pivot is not on the required side of z*". Then, in the
concrete model, we enumerate every admissible selector system and every good word of the enlarged instance and test
Lemma A directly (pivot cells are balanced: |A| = |B|, since the pivot prefix has |P| letters)."""
import itertools, sys
from z3 import *

def subsets(xs): return [tuple(c) for r in range(1, len(xs) + 1) for c in itertools.combinations(xs, r)]

def build(P, U, extra):
    cells = [(A, B) for A in subsets(P) for B in subsets(U)]
    xs = {A: ('m_' + ''.join(A) if len(A) > 1 else A[0]) for A in subsets(P)}
    ys = {B: ('j_' + ''.join(B) if len(B) > 1 else B[0]) for B in subsets(U)}
    zn = {c: f"z_{''.join(c[0])}_{''.join(c[1])}" for c in cells}
    E = list(dict.fromkeys(['bot', 'top'] + list(xs.values()) + list(ys.values()) + list(zn.values())))
    s = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}; inD = {a: Bool(f"D|{a}") for a in E}
    for a in E:
        s.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            if a != b: s.add(Not(And(le[a, b], le[b, a])))
            for c in E: s.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
            s.add(Implies(And(le[a, b], inD[b]), inD[a]))
    def glb(z, q): s.add([le[z, x] for x in q]); s.add([Implies(And([le[w, x] for x in q]), le[w, z]) for w in E])
    def lub(z, q): s.add([le[x, z] for x in q]); s.add([Implies(And([le[x, w] for x in q]), le[z, w]) for w in E])
    for A in subsets(P):
        if len(A) > 1: glb(xs[A], list(A))
    for B in subsets(U):
        if len(B) > 1: lub(ys[B], list(B))
    s.add(inD['bot'], Not(inD['top']))
    for p in P:
        s.add(inD[p]); s.add([Not(And(le[p, w], inD[w])) for w in E if w != p])
    for u in U:
        s.add(Not(inD[u])); s.add([Not(And(le[w, u], Not(inD[w]))) for w in E if w != u])
    for a, b in itertools.permutations(P, 2): s.add(Not(le[a, b]))
    for a, b in itertools.permutations(U, 2): s.add(Not(le[a, b]))
    for c in cells:
        s.add(Not(le[zn[c], xs[c[0]]]), Not(le[ys[c[1]], zn[c]]))             # no witness
        for c2 in cells:
            if set(c2[0]) <= set(c[0]) and set(c[1]) <= set(c2[1]): s.add(le[zn[c], zn[c2]])
    extra(s, le, inD, zn, cells)
    return s, le, inD, zn, cells

def goods(P, U, adm1, adm2):
    """All good words of (P, U) over all admissible selector systems: yields (word, pivot cell)."""
    out = set(); kP = len(P)
    for w in itertools.permutations(P + U):
        if w[0] not in U or w[-1] not in P: continue
        cs = [(tuple(x for x in P if x not in w[:t]), tuple(x for x in U if x in w[:t])) for t in range(1, len(w))]
        # some admissible choice makes the first |P| cells a bijection onto P and the last |U| onto U (matching)
        first = cs[:kP]; last = cs[len(cs) - len(U):]
        okP = any(sorted(lab) == sorted(P) for lab in itertools.product(*[adm1[c] for c in first])) 
        okU = any(sorted(lab) == sorted(U) for lab in itertools.product(*[adm2[c] for c in last]))
        # consistency: the pivot cell is shared and gets one f1 and one f2 value, independent; other cells distinct
        if okP and okU: out.add((w, cs[kP - 1]))
    return out

def test(name, P, U, newP, newU, old_pivot, side, extra_rel, witness=()):
    """side 1: old pivot in D captured by new P letter; side 2: outside, captured by new U letter."""
    PP = P + newP; UU = U + newU; cnew = newP[0] if newP else newU[0]
    def extra(s, le, inD, zn, cells):
        zs = zn[old_pivot]
        if side == 1:
            s.add(inD[zs], le[zs, cnew]); s.add([Not(le[zs, p]) for p in P])
            for c in cells:
                if c != old_pivot and len(c[0]) == len(c[1]): s.add(Not(le[zs, zn[c]]))   # refute: no z' >= z*
        else:
            s.add(Not(inD[zs]), le[cnew, zs]); s.add([Not(le[u, zs]) for u in U])
            for c in cells:
                if c != old_pivot and len(c[0]) == len(c[1]): s.add(Not(le[zn[c], zs]))   # refute: no z' <= z*
        extra_rel(s, le, inD, zn)
        for c, lab in witness:   # labels making a chosen old word good (so the old pivot is a genuine pivot)
            s.add(Not(le[zn[c], lab]) if lab in PP else Not(le[lab, zn[c]]))
    s, le, inD, zn, cells = build(PP, UU, extra)
    r = s.check(); print(f"[{name}] locally realizable with every balanced cell incomparable on the required side: {r}", flush=True)
    if r != sat: return
    mo = s.model(); ev = lambda b: is_true(mo.eval(b, model_completion=True))
    adm1 = {c: [p for p in c[0] if not ev(le[zn[c], p])] for c in cells}
    adm2 = {c: [u for u in c[1] if not ev(le[u, zn[c]])] for c in cells}
    oldc = [c for c in cells if set(c[0]) <= set(P) and set(c[1]) <= set(U)]
    old_goods = goods(P, U, adm1, adm2); new_goods = goods(PP, UU, adm1, adm2)
    occurs = any(pc == old_pivot for _, pc in old_goods)
    print(f"   old instance: {len(old_goods)} (word, pivot) pairs; the given old pivot {old_pivot} occurs: {occurs}", flush=True)
    if not occurs: print("   INVALID TEST: the old pivot is not a pivot of the old instance", flush=True); return
    zs = zn[old_pivot]; ok = []
    for w, pc in sorted(new_goods):
        zp = zn[pc]; good_dir = ev(le[zs, zp]) if side == 1 else ev(le[zp, zs]); same = ev(inD[zp]) == (side == 1)
        if good_dir and same: ok.append((w, pc))
    pivots = sorted({pc for _, pc in new_goods})
    print(f"   enlarged instance: {len(new_goods)} (word, pivot) pairs, pivot cells {pivots}", flush=True)
    print(f"   pivots on the required side of z* and of D: {ok if ok else 'NONE — Lemma A fails in this lattice'}", flush=True)
    # mod-2 pivot spectra (cell -> number of (word, pivot) pairs) and their D-filtered parities
    so = {}; sn = {}
    for _, pc in old_goods: so[pc] = so.get(pc, 0) + 1
    for _, pc in new_goods: sn[pc] = sn.get(pc, 0) + 1
    fmt = lambda sp: {f"{''.join(c[0])}|{''.join(c[1])}": (v, 'D' if ev(inD[zn[c]]) else 'out') for c, v in sp.items()}
    print(f"   pivot spectra: old {fmt(so)}, enlarged {fmt(sn)}; D-filtered parity old "
          f"{sum(v for c, v in so.items() if ev(inD[zn[c]])) % 2}, enlarged {sum(v for c, v in sn.items() if ev(inD[zn[c]])) % 2}", flush=True)

if __name__ == '__main__' and len(sys.argv) > 1 and sys.argv[1] == 'larger':
    # old good word u0 p1 u1 p0: P-labels p1 at ({p0,p1},{u0}), p0 at the pivot ({p0},{u0});
    # U-labels u0 at the pivot, u1 at ({p0},{u0,u1})
    test('case 2, (2,2) + u2', ['p0', 'p1'], ['u0', 'u1'], [], ['u2'], (('p0',), ('u0',)), 2, lambda *a: None,
         witness=[((('p0', 'p1'), ('u0',)), 'p1'), ((('p0',), ('u0', 'u1')), 'u1')])
    test('case 1, (3,2) + p3', ['p0', 'p1', 'p2'], ['u0', 'u1'], ['p3'], [], (('p1', 'p2'), ('u0', 'u1')), 1, lambda *a: None)
    sys.exit()
if __name__ == '__main__':
    # Case 2: the locally realizable 2×2 captor system of §34.3z¹⁰⁸ (old instance ({p0,p1},{u0}), pivot ({p0},{u0}),
    # captor u1 ≤ z*); its SU/SP relations are imposed, everything else generic.
    def captor_rel(s, le, inD, zn):
        for c in [(('p0',), ('u0',)), (('p1',), ('u0',)), (('p0',), ('u0', 'u1')), (('p1',), ('u0', 'u1')),
                  (('p0', 'p1'), ('u0', 'u1'))]: s.add(le['u1', zn[c]])
        s.add(le[zn[(('p0', 'p1'), ('u0',))], 'p0'])
    test('case 2, 2x2 captor system', ['p0', 'p1'], ['u0'], [], ['u1'], (('p0',), ('u0',)), 2, captor_rel)
    # Case 1: old instance ({p0,p1},{u0}), pivot ({p1},{u0}) in D, captor p2.
    test('case 1, 3x1', ['p0', 'p1'], ['u0'], ['p2'], [], (('p1',), ('u0',)), 1, lambda *a: None)
    # Case 1 with two U letters: old ({p0,p1},{u0,u1}), pivot cell ({p1},{u0}) or ({p1,p0}... balanced) in D, captor p2.
    test('case 1, 3x2', ['p0', 'p1'], ['u0', 'u1'], ['p2'], [], (('p1',), ('u1',)), 1, lambda *a: None)
