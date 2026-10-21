"""Zone assignment for the multi-strip modification on L x K (L end-finite, K finite).

A value z in the strip S_k = L x {k} (k a middle element of K) at a cell whose
row has layer p and column layer q is
  core       if k <= p and q <= k      (finitely many values: core_finite),
  lowerable  if not k <= p             (s_k <= new value <= z),
  raisable   if not q <= k             (z <= new value <= t_k).
Ambiguous cells are both lowerable and raisable.  We need, for every k, a split
of the non-core cells into L_k (lowered) and R_k (raised) such that
  same strip:  no R_k cell lies below an L_k cell;
  cross strip: for k < k', an R_k cell (p,q) below an L_k' cell (p',q') is
               allowed only if k <= p and q' <= k'  (the corner argument with
               corner G(s_k, t_k') then puts z or z' in a finite guide set).
Layers only: the zone of a cell depends on (p,q) alone.
"""
import itertools, sys
from z3 import Bool, Solver, Not, And, Or, Implies, sat, is_true

def chain(n):
    return list(range(n)), (lambda a, b: a <= b)

def boolean(m):
    els = list(range(1 << m))
    return els, (lambda a, b: a & ~b == 0)

def solve(K, le, name):
    bot = [a for a in K if all(le(a, b) for b in K)][0]
    top = [a for a in K if all(le(b, a) for b in K)][0]
    mid = [k for k in K if k not in (bot, top)]
    cells = list(itertools.product(K, K))
    cle = lambda c, d: le(c[0], d[0]) and le(c[1], d[1])
    s = Solver()
    var = {}
    def zone(k, c):  # returns 'C', 'L', 'R', or a z3 Bool (True = lowered)
        p, q = c
        lo, ra = not le(k, p), not le(q, k)
        if not lo and not ra: return 'C'
        if lo and not ra: return 'L'
        if ra and not lo: return 'R'
        if (k, c) not in var: var[(k, c)] = Bool(f"low_{k}_{p}_{q}")
        return var[(k, c)]
    def isL(k, c):
        z = zone(k, c); return z if not isinstance(z, str) else (z == 'L')
    def isR(k, c):
        z = zone(k, c); return Not(z) if not isinstance(z, str) else (z == 'R')
    for k in mid:
        for k2 in mid:
            if not le(k, k2): continue
            for c in cells:
                for d in cells:
                    if not cle(c, d): continue
                    if k == k2:
                        s.add(Not(And(isR(k, c), isL(k, d))))
                    else:
                        if le(k, c[0]) and le(d[1], k2): continue
                        s.add(Not(And(isR(k, c), isL(k2, d))))
    r = s.check()
    print(name, r, f"({len(var)} ambiguous)")
    if r == sat and '-v' in sys.argv:
        m = s.model()
        for k in mid:
            lows = sorted(c for (kk, c) in var if kk == k and is_true(m[var[(kk, c)]]))
            print("  k =", k, "ambiguous lowered:", lows)
    return r

if __name__ == "__main__":
    for n in range(3, 8):
        solve(*chain(n), f"C{n}")
    for m in (2, 3):
        solve(*boolean(m), f"B{m}")
    # M3 and N5 and C3xC3
    M3 = [0, 1, 2, 3, 4]; leM3 = lambda a, b: a == b or a == 0 or b == 4
    solve(M3, leM3, "M3")
    N5 = [0, 1, 2, 3, 4]  # 0 < 1 < 2 < 4, 0 < 3 < 4
    rel = {(0,1),(0,2),(0,3),(0,4),(1,2),(1,4),(2,4),(3,4)}
    solve(N5, lambda a, b: a == b or (a, b) in rel, "N5")
    C3sq = list(itertools.product(range(3), range(3)))
    solve(C3sq, lambda a, b: a[0] <= b[0] and a[1] <= b[1], "C3xC3")


def downsets(K, le):
    out = []
    for mask in range(1 << len(K)):
        S = {K[i] for i in range(len(K)) if mask >> i & 1}
        if all((a in S) for b in S for a in K if le(a, b)):
            out.append(frozenset(S))
    return out

def solve_typed(K, le, name, verbose=False):
    """Per cut type: Fu = {k : D-hat_k = L}, Ne = {k : D-hat_k nonempty}, Fu <= Ne down-sets.
    Rows exist only in layers Ne, columns only in layers outside Fu."""
    bot = [a for a in K if all(le(a, b) for b in K)][0]
    top = [a for a in K if all(le(b, a) for b in K)][0]
    mid = [k for k in K if k not in (bot, top)]
    ds = downsets(K, le)
    bad = []
    for Fu in ds:
        for Ne in ds:
            if not Fu <= Ne or bot not in Ne or top in Fu: continue
            cells = [(p, q) for p in Ne for q in K if q not in Fu]
            cle = lambda c, d: le(c[0], d[0]) and le(c[1], d[1])
            s = Solver(); var = {}
            def zone(k, c):
                p, q = c
                lo, ra = not le(k, p), not le(q, k)
                if not lo and not ra: return 'C'
                if lo and not ra: return 'L'
                if ra and not lo: return 'R'
                if (k, c) not in var: var[(k, c)] = Bool(f"low_{k}_{p}_{q}")
                return var[(k, c)]
            isL = lambda k, c: (lambda z: z if not isinstance(z, str) else z == 'L')(zone(k, c))
            isR = lambda k, c: (lambda z: Not(z) if not isinstance(z, str) else z == 'R')(zone(k, c))
            for k in mid:
                for k2 in mid:
                    if not le(k, k2): continue
                    for c in cells:
                        for d in cells:
                            if not cle(c, d): continue
                            if k != k2 and le(k, c[0]) and le(d[1], k2): continue
                            s.add(Not(And(isR(k, c), isL(k2, d))))
            if s.check() != sat:
                bad.append((sorted(Fu), sorted(Ne)))
    print(name, "all cut types OK" if not bad else f"{len(bad)} bad cut types: {bad[:6]}")
    return bad

if __name__ == "__main__" and '-t' in sys.argv:
    for n in range(3, 8):
        solve_typed(*chain(n), f"C{n}")
    C3sq = list(itertools.product(range(3), range(3)))
    solve_typed(C3sq, lambda a, b: a[0] <= b[0] and a[1] <= b[1], "C3xC3")
    solve_typed(*boolean(3), "B3")
