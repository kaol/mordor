"""Search for an infinite DCC counterexample to max-only CLL (InfiniteCLL.MaxLabelling k C).
C = boundary columns K (K[0] = top) + generic columns (i, t), i in N, t in types.
Order: K-K free; K-generic and generic-K depend on the type only; generic (i,t) < (j,u) only if j > i
(class of j - i clamped to 1..W+1) or j = i and t < u: every strict descent lowers (index, type), so DCC holds.
w(A, c): a label alpha (nonempty, A not a subset), a boundary column, or a generic column: at an absolute index
(e, v) for boundary inputs, at (i + e, v) for generic inputs (translation invariant), 0 <= e <= E.
Counterexample-guided: solve on the window [0, N], check on [0, NV], add violated instances, repeat.
k <= 2 must be UNSAT (InfiniteCLL.cll_max_one, cll_max_two).
  python3 maxcll.py k nT nK [W] [E] [N] [NV]"""
import sys, itertools, time
from pysat.solvers import Cadical153
k, nT, nK = map(int, sys.argv[1:4])
W = int(sys.argv[4]) if len(sys.argv) > 4 else 1
E = int(sys.argv[5]) if len(sys.argv) > 5 else 1
N = int(sys.argv[6]) if len(sys.argv) > 6 else 6
NV = int(sys.argv[7]) if len(sys.argv) > 7 else 14
NOW2 = len(sys.argv) > 8 and sys.argv[8] == 'nowit2'
G = list(range(k))
ROWS = [frozenset(A) for r in range(1, k + 1) for A in itertools.combinations(G, r)]
LABS = ROWS
T = list(range(nT)); K = list(range(nK)); TOP = ('K', 0)
nv = 0
def var():
    global nv; nv += 1; return nv
S = Cadical153(); ncl = 0
def add(c):
    global ncl
    out = []
    for l in c:
        if l is True: return
        if l is False: continue
        out.append(l)
    if not out: raise SystemExit("empty clause")
    S.add_clause(out); ncl += 1
def neg(l): return (not l) if isinstance(l, bool) else -l
KK = {(a, b): var() for a in K for b in K if a != b and a != 0}
KG = {(a, t): var() for a in K if a != 0 for t in T}
GK = {(t, a): var() for t in T for a in K if a != 0}
R0 = {(t, u): var() for t in T for u in T if t < u}
RD = {(t, u, d): var() for t in T for u in T for d in range(1, W + 2)}
def cl(d): return min(d, W + 1)
def le(a, b):
    if a == b: return True
    if b == TOP: return True
    if a == TOP: return False
    if a[0] == 'K' and b[0] == 'K': return KK[(a[1], b[1])]
    if a[0] == 'K': return KG[(a[1], b[2])]
    if b[0] == 'K': return GK[(a[2], b[1])]
    i, t, j, u = a[1], a[2], b[1], b[2]
    if j < i: return False
    if j == i: return False if t > u else R0[(t, u)]
    return RD[(t, u, cl(j - i))]
for a in K:
    for b in K:
        if a < b and a != 0 and b != 0: add([-KK[(a, b)], -KK[(b, a)]])
for a in K:
    if a == 0: continue
    for t in T: add([-KG[(a, t)], -GK[(t, a)]])
def elems(n): return [('K', a) for a in K] + [('G', i, t) for i in range(n + 1) for t in T]
def lev(x, y):     # value order: labels below columns, labels reversed by inclusion
    if x[0] == 'L' and y[0] == 'L': return y[1] <= x[1]
    if x[0] == 'L': return True
    if y[0] == 'L': return False
    return le(x, y)
def kind(c): return ('K', c[1]) if c[0] == 'K' else ('T', c[2])
OPT = {}; X = {}
for A in ROWS:
    for kd in [('K', a) for a in K] + [('T', t) for t in T]:
        o = [('L', al) for al in LABS if not A <= al] + [('K', a) for a in K if a != 0]
        o += [('abs' if kd[0] == 'K' else 'rel', e, v) for e in range(E + 1) for v in T]
        OPT[(A, kd)] = o; X[(A, kd)] = [var() for _ in o]
        add(X[(A, kd)])
        for i1 in range(len(o)):
            for i2 in range(i1 + 1, len(o)): add([-X[(A, kd)][i1], -X[(A, kd)][i2]])
def val(o, c):
    if o[0] in ('L', 'K'): return o
    if o[0] == 'abs': return ('G', o[1], o[2])
    return ('G', c[1] + o[1], o[2])
B = {}
def Bv(A, c, z):
    key = (A, c, z)
    if key in B: return B[key]
    b = var(); B[key] = b
    for o, xo in zip(OPT[(A, kind(c))], X[(A, kind(c))]):
        l = lev(val(o, c), z); add([-xo, -b, l]); add([-xo, b, neg(l)])
    return b
def inst(kind_, *args):
    if kind_ == 't':
        a, b, c = args; add([neg(le(a, b)), neg(le(b, c)), le(a, c)])
    elif kind_ == 'w2':
        if NOW2: return
        A, c = args
        for o, xo in zip(OPT[(A, kind(c))], X[(A, kind(c))]):
            v = val(o, c)
            if v[0] != 'L': add([-xo, neg(le(c, v))])
    elif kind_ == 'mc':
        A, c, c2 = args; L = le(c, c2)
        for o, xo in zip(OPT[(A, kind(c2))], X[(A, kind(c2))]): add([neg(L), -xo, Bv(A, c, val(o, c2))])
    elif kind_ == 'ma':
        A, A2, c = args
        for o, xo in zip(OPT[(A2, kind(c))], X[(A2, kind(c))]): add([-xo, Bv(A, c, val(o, c))])
EL = elems(N)
for a in EL:
    for b in EL:
        if a == b or le(a, b) is False: continue
        for c in EL:
            if c != b and le(b, c) is not False: inst('t', a, b, c)
for A in ROWS:
    for c in EL: inst('w2', A, c)
    for c in EL:
        for c2 in EL:
            if c != c2 and le(c, c2) is not False: inst('mc', A, c, c2)
for A in ROWS:
    for A2 in ROWS:
        if A2 < A:
            for c in EL: inst('ma', A, A2, c)
print(f"k={k} types={nT} boundary={nK} W={W} E={E} N={N}: vars {nv}, clauses {ncl}", flush=True)
def check(m):
    def L(a, b):
        l = le(a, b); return l if isinstance(l, bool) else (l in m)
    def wv(A, c):
        o = OPT[(A, kind(c))][[i for i, x in enumerate(X[(A, kind(c))]) if x in m][0]]; return val(o, c)
    def LV(x, y):
        if x[0] == 'L' or y[0] == 'L': return lev(x, y)
        return L(x, y)
    EL2 = elems(NV); bad = []
    for a in EL2:
        for b in EL2:
            if a != b and L(a, b):
                for c in EL2:
                    if c != b and L(b, c) and not L(a, c): bad.append(('t', a, b, c))
    WV = {(A, c): wv(A, c) for A in ROWS for c in EL2}
    for A in ROWS:
        for c in EL2:
            v = WV[(A, c)]
            if not NOW2 and v[0] != 'L' and L(c, v): bad.append(('w2', A, c))
            for c2 in EL2:
                if c2 != c and L(c, c2) and not LV(v, WV[(A, c2)]): bad.append(('mc', A, c, c2))
            for A2 in ROWS:
                if A2 < A and not LV(v, WV[(A2, c)]): bad.append(('ma', A, A2, c))
    return bad, WV
t0 = time.time(); rounds = 0
while True:
    ok = S.solve()
    if not ok: break
    m = set(l for l in S.get_model() if l > 0)
    bad, WV = check(m); rounds += 1
    if not bad: break
    for b in bad: inst(*b)
    if rounds % 5 == 0: print(f"  round {rounds}: {len(bad)} violations, clauses {ncl}", flush=True)
print(f"k={k} -> {'SAT, verified on [0, %d]' % NV if ok else 'UNSAT'} after {rounds} rounds ({time.time()-t0:.1f}s)", flush=True)
if ok:
    import pickle
    pickle.dump({'m': m, 'KK': KK, 'KG': KG, 'GK': GK, 'R0': R0, 'RD': RD, 'OPT': OPT, 'X': X, 'args': sys.argv[1:]},
                open(f"model_k{k}_{nT}_{nK}.pkl", "wb"))
