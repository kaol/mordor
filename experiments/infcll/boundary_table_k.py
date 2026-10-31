"""Boundary table for max-only CLL with k generators (2^k - 1 rows) as a finite SMT model; k = 3 is boundary_table.py.
Used as the k = 2 control in log §34.3z⁵⁷: an open table that is SAT where `cll_max_two` is a theorem shows that open
fragments do not see DCC or closure under values.
Points: top, b_B (a maximal label boundary of row B, InfiniteCLL.maximal_label_boundary), m fresh value points.
Row values are known at top and at the boundaries only: a label (W1) or a point. Constraints: partial order on points,
top greatest; W2 at known points; monotonicity (A >= A', x <= y known => w(A,x) <= w(A',y), labels below points,
labels reversed by inclusion); diagonal w(B, b_B) label; w(B, y) a point for known y > b_B.
  python3 boundary_table_k.py k m [closed]   closed: also evaluate rows at the value points (a finite labelling: must be UNSAT)"""
import sys, itertools
from z3 import *
K = int(sys.argv[1]); m = int(sys.argv[2]); CLOSED = len(sys.argv) > 3
G = range(K)
ROWS = [frozenset(A) for r in range(1, K + 1) for A in itertools.combinations(G, r)]
LABS = [A for A in ROWS if len(A) < K]
NL = len(LABS); NR = len(ROWS)
P = ['top'] + [('b', i) for i in range(NR)] + [('e', j) for j in range(m)]
n = len(P); TOP = 0
s = Solver()
le = [[Bool(f"le_{i}_{j}") for j in range(n)] for i in range(n)]
for i in range(n):
    s.add(le[i][i]); s.add(le[i][TOP])
    for j in range(n):
        if i != j: s.add(Not(And(le[i][j], le[j][i])))
        for k in range(n): s.add(Implies(And(le[i][j], le[j][k]), le[i][k]))
known = list(range(n)) if CLOSED else list(range(1 + NR))
# value of row A at known point x: label index (0..NL-1) or point index (NL + p)
V = {}
for A in ROWS:
    for x in known:
        v = Int(f"v_{sorted(A)}_{x}"); V[(A, x)] = v
        okl = [i for i, L in enumerate(LABS) if not A <= L]
        s.add(Or([v == i for i in okl] + [And(v >= NL, v < NL + n)]))
        for p in range(n): s.add(Implies(v == NL + p, Not(le[x][p])))        # W2
def vle(u, v):   # value order
    cl = []
    for i, Li in enumerate(LABS):
        for j, Lj in enumerate(LABS):
            if not Lj <= Li: cl.append(And(u == i, v == j))
    for p in range(n):
        for q in range(n): cl.append(And(u == NL + p, v == NL + q, Not(le[p][q])))
        for j in range(NL): cl.append(And(u == NL + p, v == j))
    return Not(Or(cl))
for A in ROWS:
    for A2 in ROWS:
        if not A2 <= A: continue
        for x in known:
            for y in known:
                s.add(Implies(le[x][y], vle(V[(A, x)], V[(A2, y)])))
for bi, B in enumerate(ROWS):
    b = 1 + bi
    s.add(V[(B, b)] < NL)
    for y in known:
        if y != b: s.add(Implies(le[b][y], V[(B, y)] >= NL))
r = s.check(); print(f"k={K} m={m} closed={CLOSED}:", r)
if r == sat:
    mo = s.model()
    def show(v):
        x = mo.eval(v).as_long()
        return sorted(LABS[x]) if x < NL else P[x - NL]
    for bi, B in enumerate(ROWS):
        print(f"  b_{sorted(B)}:", {tuple(sorted(A)): show(V[(A, 1 + bi)]) for A in ROWS})
    rel = [(P[i], P[j]) for i in range(1, n) for j in range(1, n) if i != j and is_true(mo.eval(le[i][j]))]
    print("  order (non-top):", rel)
