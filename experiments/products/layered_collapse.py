"""Abstract anchor tables for L1 x L2 x C_n (n = 1 or 2 layers) and the layered collapse moves.

Anchors: A = {bot,top}^2 x layers.  D ∩ A is a down-set containing bot, missing top.
For anchor rows a ∈ D and anchor columns b ∉ D the value F(a,b) is abstracted to
(class of coord 1, class of coord 2, layer), class ∈ {0 = bot, 1 = middle, 2 = top}.
Constraints: monotone between comparable anchor cells, no witness at anchor cells.

Layered collapse of coordinate 1 succeeds if for every layer pair k <= k' with s_k = (bot,bot,k) ∈ D and
t_k' = (top,top,k') ∉ D one of
  (alpha) (bot,top,k) ∈ D and F((bot,top,k),(top,top,k'))_1 != top
  (beta)  (top,bot,k') ∉ D and F((bot,bot,k),(top,bot,k'))_1 != bot
holds (floor sets grow with the layer, ceiling sets shrink, so each pair may use either bound).
Collapse of coordinate 2: the same with the coordinates exchanged.
We list the abstract tables where both collapses fail.
"""
import itertools, sys
from z3 import Int, Bool, Solver, And, Or, Not, Implies, sat, BoolVal

def run(n, show=5):
    L = range(n)
    A = [(a, b, k) for a in (0, 2) for b in (0, 2) for k in L]   # 0 = bot, 2 = top
    le = lambda u, v: all(x <= y for x, y in zip(u, v))
    bot, top = (0, 0, 0), (2, 2, n - 1)
    inD = {a: Bool(f"D{a}") for a in A}
    s = Solver()
    s.add(inD[bot], Not(inD[top]))
    for u in A:
        for v in A:
            if le(u, v): s.add(Implies(inD[v], inD[u]))
    cells = [(a, b) for a in A for b in A]
    c1 = {c: Int(f"c1{c}") for c in cells}; c2 = {c: Int(f"c2{c}") for c in cells}; ly = {c: Int(f"l{c}") for c in cells}
    act = {c: And(inD[c[0]], Not(inD[c[1]])) for c in cells}
    for c in cells:
        s.add(c1[c] >= 0, c1[c] <= 2, c2[c] >= 0, c2[c] <= 2, ly[c] >= 0, ly[c] < n)
        a, b = c
        # value <= a  iff  c1 <= a1 (as classes: <= bot means bot; <= top always) etc.
        lea = And(Or(c1[c] == 0, BoolVal(a[0] == 2)), Or(c2[c] == 0, BoolVal(a[1] == 2)), ly[c] <= a[2])
        bge = And(Or(c1[c] == 2, BoolVal(b[0] == 0)), Or(c2[c] == 2, BoolVal(b[1] == 0)), ly[c] >= b[2])
        s.add(Implies(act[c], And(Not(lea), Not(bge))))
    for c in cells:
        for d in cells:
            if c != d and le(c[0], d[0]) and le(c[1], d[1]):
                s.add(Implies(And(act[c], act[d]), And(
                    Implies(c1[c] == 2, c1[d] == 2), Implies(c1[d] == 0, c1[c] == 0),
                    Implies(c2[c] == 2, c2[d] == 2), Implies(c2[d] == 0, c2[c] == 0), ly[c] <= ly[d])))
    def collapse(i):
        conds = []
        for k in L:
            for k2 in L:
                if k > k2: continue
                sk, tk = (0, 0, k), (2, 2, k2)
                if i == 1:
                    ra, ca = (0, 2, k), (2, 2, k2); rb, cb = (0, 0, k), (2, 0, k2); cl = c1
                else:
                    ra, ca = (2, 0, k), (2, 2, k2); rb, cb = (0, 0, k), (0, 2, k2); cl = c2
                alpha = And(inD[ra], cl[(ra, ca)] != 2)
                beta = And(Not(inD[cb]), cl[(rb, cb)] != 0)
                conds.append(Implies(And(inD[sk], Not(inD[tk])), Or(alpha, beta)))
        return And(conds)
    s.add(Not(collapse(1)), Not(collapse(2)))
    cnt = 0
    seen = set()
    while s.check() == sat and cnt < 200:
        m = s.model()
        Dset = tuple(a for a in A if m.eval(inD[a], model_completion=True))
        key = Dset
        if key not in seen:
            seen.add(key)
            if len(seen) <= show:
                print("  D ∩ A =", Dset)
        cnt += 1
        s.add(Or([inD[a] != m.eval(inD[a], model_completion=True) for a in A]))
    print(f"n={n}: {len(seen)} anchor cut types admit tables where both collapses fail")

if __name__ == "__main__":
    for n in (1, 2): run(n)


def run2(n, show=8):
    """Generalized collapse G-C1 / G-C2 with value types from the anchor-pass regions.
    Region (i,j): rows of layer i (anchor s_i), columns of layer j (anchor t_j), corner c_ij = F(s_i,t_j).
    Value types by corner class: (m,m) -> fin/H/V; (bot,m),(top,m) -> H; (m,bot),(m,top) -> V;
    (bot,top),(top,bot) -> anti; (bot,bot),(top,top) -> no values.
    A G-C1 stuck pair z <= z' (layers k <= k', k <= row layer of z, col layer of z' <= k') is discharged
    if z or z' is fin/V, or both are H (Layers corner), or a layered anchor bound alpha1/beta1(k,k') exists."""
    L = range(n)
    A = [(a, b, k) for a in (0, 2) for b in (0, 2) for k in L]
    le = lambda u, v: all(x <= y for x, y in zip(u, v))
    bot, top = (0, 0, 0), (2, 2, n - 1)
    inD = {a: Bool(f"D{a}") for a in A}
    s = Solver()
    s.add(inD[bot], Not(inD[top]))
    for u in A:
        for v in A:
            if le(u, v): s.add(Implies(inD[v], inD[u]))
    cells = [(a, b) for a in A for b in A]
    c1 = {c: Int(f"c1{c}") for c in cells}; c2 = {c: Int(f"c2{c}") for c in cells}; ly = {c: Int(f"l{c}") for c in cells}
    act = {c: And(inD[c[0]], Not(inD[c[1]])) for c in cells}
    for c in cells:
        s.add(c1[c] >= 0, c1[c] <= 2, c2[c] >= 0, c2[c] <= 2, ly[c] >= 0, ly[c] < n)
        a, b = c
        lea = And(Or(c1[c] == 0, BoolVal(a[0] == 2)), Or(c2[c] == 0, BoolVal(a[1] == 2)), ly[c] <= a[2])
        bge = And(Or(c1[c] == 2, BoolVal(b[0] == 0)), Or(c2[c] == 2, BoolVal(b[1] == 0)), ly[c] >= b[2])
        s.add(Implies(act[c], And(Not(lea), Not(bge))))
    for c in cells:
        for d in cells:
            if c != d and le(c[0], d[0]) and le(c[1], d[1]):
                s.add(Implies(And(act[c], act[d]), And(
                    Implies(c1[c] == 2, c1[d] == 2), Implies(c1[d] == 0, c1[c] == 0),
                    Implies(c2[c] == 2, c2[d] == 2), Implies(c2[d] == 0, c2[c] == 0), ly[c] <= ly[d])))
    sA = lambda i: (0, 0, i); tA = lambda j: (2, 2, j)
    def corner(i, j): return (sA(i), tA(j))
    def types(i, j):
        c = corner(i, j); h1, h2 = c1[c], c2[c]
        reg = And(inD[sA(i)], Not(inD[tA(j)]))
        mid1, mid2 = h1 == 1, h2 == 1
        return {
            'fin': And(reg, mid1, mid2),
            'H': And(reg, Or(And(mid1, mid2), And(Or(h1 == 0, h1 == 2), mid2))),
            'V': And(reg, Or(And(mid1, mid2), And(mid1, Or(h2 == 0, h2 == 2)))),
            'anti': And(reg, Or(And(h1 == 0, h2 == 2), And(h1 == 2, h2 == 0))),
        }
    def bound(i, k, k2):
        if i == 1:
            ra, ca = (0, 2, k), (2, 2, k2); rb, cb = (0, 0, k), (2, 0, k2); cl = c1
        else:
            ra, ca = (2, 0, k), (2, 2, k2); rb, cb = (0, 0, k), (0, 2, k2); cl = c2
        return Or(And(inD[ra], cl[(ra, ca)] != 2), And(Not(inD[cb]), cl[(rb, cb)] != 0))
    def fails(coord):
        good = ('fin', 'V') if coord == 1 else ('fin', 'H')
        same = 'H' if coord == 1 else 'V'
        bad = []
        for i in L:
            for j in L:
                for i2 in L:
                    for j2 in L:
                        if not (i <= i2 and j <= j2): continue
                        T, T2 = types(i, j), types(i2, j2)
                        for k in L:
                            for k2 in L:
                                if not (k <= k2 and k <= i and j2 <= k2): continue
                                for t in T:
                                    for t2 in T2:
                                        if t in good or t2 in good or (t == same and t2 == same): continue
                                        bad.append(And(T[t], T2[t2], Not(bound(coord, k, k2))))
        return Or(bad) if bad else BoolVal(False)
    s.add(fails(1), fails(2))
    seen = set()
    while s.check() == sat and len(seen) < 100:
        m = s.model()
        Dset = tuple(a for a in A if m.eval(inD[a], model_completion=True))
        if Dset not in seen:
            seen.add(Dset)
            if len(seen) <= show:
                corners = {(i, j): (m.eval(c1[corner(i, j)]), m.eval(c2[corner(i, j)]), m.eval(ly[corner(i, j)]))
                           for i in L for j in L}
                print("  D ∩ A =", Dset, " corners:", corners)
        s.add(Or([inD[a] != m.eval(inD[a], model_completion=True) for a in A]))
    print(f"n={n}: {len(seen)} anchor cut types with residue")

if __name__ == "__main__" and '-2' in sys.argv:
    for n in (1, 2): run2(n)
