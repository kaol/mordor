"""Seven-row boundary table (max-only CLL, k = 3) as a finite SMT model.
Points: top, b_B (a maximal label boundary of row B, InfiniteCLL.maximal_label_boundary), m fresh value points.
Row values are known at top and at the boundaries only: a label (W1) or a point. Constraints: partial order on points,
top greatest; W2 at known points; monotonicity (A >= A', x <= y known => w(A,x) <= w(A',y), labels below points,
labels reversed by inclusion); diagonal w(B, b_B) label; w(B, y) a point for known y > b_B.
  python3 boundary_table.py m [closed]   closed: also evaluate rows at the value points (a finite labelling: must be UNSAT)"""
import sys, itertools
from z3 import *
m = int(sys.argv[1]); CLOSED = len(sys.argv) > 2
G = range(3)
ROWS = [frozenset(A) for r in (1, 2, 3) for A in itertools.combinations(G, r)]
LABS = [A for A in ROWS if len(A) < 3]
P = ['top'] + [('b', i) for i in range(7)] + [('e', j) for j in range(m)]
n = len(P); TOP = 0
s = Solver()
le = [[Bool(f"le_{i}_{j}") for j in range(n)] for i in range(n)]
for i in range(n):
    s.add(le[i][i]); s.add(le[i][TOP])
    for j in range(n):
        if i != j: s.add(Not(And(le[i][j], le[j][i])))
        for k in range(n): s.add(Implies(And(le[i][j], le[j][k]), le[i][k]))
known = list(range(n)) if CLOSED else list(range(8))
# value of row A at known point x: label index (0..5) or point index (6 + p)
V = {}
for A in ROWS:
    for x in known:
        v = Int(f"v_{sorted(A)}_{x}"); V[(A, x)] = v
        okl = [i for i, L in enumerate(LABS) if not A <= L]
        s.add(Or([v == i for i in okl] + [And(v >= 6, v < 6 + n)]))
        for p in range(n): s.add(Implies(v == 6 + p, Not(le[x][p])))        # W2
def vle(u, v):   # value order
    cl = []
    for i, Li in enumerate(LABS):
        for j, Lj in enumerate(LABS):
            if not Lj <= Li: cl.append(And(u == i, v == j))
    for p in range(n):
        for q in range(n): cl.append(And(u == 6 + p, v == 6 + q, Not(le[p][q])))
        for j in range(6): cl.append(And(u == 6 + p, v == j))
    return Not(Or(cl))
for A in ROWS:
    for A2 in ROWS:
        if not A2 <= A: continue
        for x in known:
            for y in known:
                s.add(Implies(le[x][y], vle(V[(A, x)], V[(A2, y)])))
for bi, B in enumerate(ROWS):
    b = 1 + bi
    s.add(V[(B, b)] < 6)
    for y in known:
        if y != b: s.add(Implies(le[b][y], V[(B, y)] >= 6))
r = s.check(); print(f"m={m} closed={CLOSED}:", r)
if r == sat:
    mo = s.model()
    def show(v):
        x = mo.eval(v).as_long()
        return sorted(LABS[x]) if x < 6 else P[x - 6]
    for bi, B in enumerate(ROWS):
        print(f"  b_{sorted(B)}:", {tuple(sorted(A)): show(V[(A, 1 + bi)]) for A in ROWS})
    rel = [(P[i], P[j]) for i in range(1, n) for j in range(1, n) if i != j and is_true(mo.eval(le[i][j]))]
    print("  order (non-top):", rel)
