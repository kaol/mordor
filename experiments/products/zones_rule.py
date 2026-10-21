"""Test a canonical zone rule against all types (chains), instead of solving zones by SAT.
Rule: for an ambiguous non-tame class (k,p,q), look at the corner g = G(s_p, t_q) of the
cell's own box: cls 0 -> lower, cls 2 -> raise, cls 1 -> lower iff k > lay(g) (tie: TIE)."""
import sys, itertools
from z3 import *
def chain(n):
    return list(range(n)), (lambda a, b: a <= b)

def downsets(K, le):
    out = []
    for mask in range(1 << len(K)):
        S = {K[i] for i in range(len(K)) if mask >> i & 1}
        if all((a in S) for b in S for a in K if le(a, b)):
            out.append(frozenset(S))
    return out

def rule_check(n, tie):
    K, le = chain(n); mid = list(range(1, n - 1)); bad = 0; nt = 0
    for Fu in downsets(K, le):
        for Ne in downsets(K, le):
            if not Fu <= Ne or 0 not in Ne or n - 1 in Fu: continue
            rows = [('s', i) for i in K if i in Ne] + [('t', i) for i in K if i in Fu]
            cols = [('s', j) for j in K if j not in Ne] + [('t', j) for j in K if j not in Fu]
            ale = lambda u, v: le(u[1], v[1]) and not (u[0] == 't' and v[0] == 's')
            A = [(r, c) for r in rows for c in cols]
            cls = {a: Int(f"c_{a}") for a in A}; lay = {a: Int(f"l_{a}") for a in A}
            T = Solver()
            for a in A:
                T.add(cls[a] >= 0, cls[a] <= 2, lay[a] >= 0, lay[a] < n)
                (rt, i), (ct, j) = a
                T.add(Not(And(cls[a] == 0, lay[a] <= i)) if rt == 's' else Not(lay[a] <= i))
                T.add(Not(lay[a] >= j) if ct == 's' else Not(And(cls[a] == 2, lay[a] >= j)))
            for a in A:
                for b in A:
                    if a != b and ale(a[0], b[0]) and ale(a[1], b[1]):
                        T.add(Implies(cls[a] == 2, cls[b] == 2), Implies(cls[b] == 0, cls[a] == 0), lay[a] <= lay[b])
            cells = [(p, q) for p in Ne for q in K if q not in Fu]
            def tame_expr(k, c):
                p, q = c; d = []
                for i in Ne:
                    if i > p: continue
                    for j in K:
                        if j not in Ne and j <= q:
                            a = (('s', i), ('s', j)); d.append(Or(cls[a] != 0, lay[a] > k))
                        if j not in Fu and q <= j:
                            a = (('s', i), ('t', j))
                            d.append(Or(And(cls[a] != 2, If(lay[a] < k, lay[a], k) <= i),
                                        And(cls[a] != 0, j <= If(lay[a] > k, lay[a], k))))
                for i in Fu:
                    if p > i: continue
                    for j in K:
                        if j not in Fu and q <= j:
                            a = (('t', i), ('t', j)); d.append(Or(cls[a] != 2, lay[a] < k))
                return Or(d) if d else BoolVal(False)
            def zone_expr(k, c):   # True = lowered (only meaningful when non-tame)
                p, q = c
                lo, ra = k > p, q > k
                if lo and not ra: return BoolVal(True)
                if ra and not lo: return BoolVal(False)
                a = (('s', p), ('t', q))
                return Or(cls[a] == 0, And(cls[a] == 1, (lay[a] <= k) if tie else (lay[a] < k)))
            classes = [(k, c) for k in mid for c in cells]
            # search a type with a conflict: non-tame raised (k,c) <= non-tame lowered (k2,d)
            confl = []
            for (k, c) in classes:
                for (k2, d) in classes:
                    if k <= k2 and c[0] <= d[0] and c[1] <= d[1]:
                        confl.append(And(Not(tame_expr(k, c)), Not(zone_expr(k, c)),
                                         Not(tame_expr(k2, d)), zone_expr(k2, d)))
            T.add(Or(confl))
            if T.check() == sat:
                bad += 1
                if bad <= 1:
                    m = T.model()
                    print("  conflict in cut type", sorted(Fu), sorted(Ne))
                    for (k, c) in classes:
                        for (k2, d) in classes:
                            if k <= k2 and c[0] <= d[0] and c[1] <= d[1] and is_true(m.eval(And(Not(tame_expr(k, c)), Not(zone_expr(k, c)), Not(tame_expr(k2, d)), zone_expr(k2, d)))):
                                print("   R", k, c, "<= L", k2, d)
                                print("   corners:", {str(a): (m[cls[a]], m[lay[a]]) for a in A if a[0][0]=='s' and a[1][0]=='t'})
                                break
    print(f"C{n} tie={'L' if tie else 'R'}:", "rule OK" if not bad else f"{bad} cut types with conflicts")

for n in range(3, 8):
    for tie in (True, False):
        rule_check(n, tie)
