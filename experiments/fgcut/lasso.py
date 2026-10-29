"""Periodic (lasso) models of the reduced meet-row theory of a strictly crossing triple.
D-part: ⊥, the 7 meets (glbs), E extras.  Columns: c_{t,n} for types t < T and n ∈ ℕ, with c_{t,n} ≤ c_{s,m} only when
m ≥ n, depending on (t, s, min(m − n, W)) — eventually constant, so tails may be ascending chains (so DCC holds: descending chains lower n); U limit columns L_u (above whole type tails,
shift-invariant), and ⊤.  Rows: the 7 meet rows.  F(r, c_{t,n}) = a D-element, ⊤, some L_u, or c_{s,n+δ} (0 ≤ δ ≤ Δ),
shift-invariant; F(r, L_u), F(r, ⊤) ∈ D ∪ L ∪ {⊤}, and with 'open' also a fixed column c_{s,m} (m ≤ W).
Monotone; no-witness at every column, every L_u and ⊤ (log §34.3z²⁷).
   python3 lasso.py T W Δ U E [open] [nonw | nwcols | notop | nolim]"""
import sys, itertools
from pysat.solvers import Cadical195
TT, W, DL, U, NE = map(int, sys.argv[1:6])
FLAGS = sys.argv[6:]
OPEN = 'open' in FLAGS   # F(r, L_u), F(r, ⊤) may also be a column c_{s,m}, m ≤ W
subsets = [frozenset(A) for n in range(1, 4) for A in itertools.combinations(range(3), n)]
ND = 8 + NE; MEET = {A: 1 + k for k, A in enumerate(subsets)}; P = [MEET[frozenset([i])] for i in range(3)]
nv = [0]
def new(): nv[0] += 1; return nv[0]
cl = []
def add(c):
    out = []
    for l in c:
        if l is True: return
        if l is False: continue
        out.append(l)
    cl.append(out)
def neg(l): return (not l) if isinstance(l, bool) else -l
LD = [[True if i == j or i == 0 else (False if j == 0 else None) for j in range(ND)] for i in range(ND)]
for A in subsets:
    for B in subsets: LD[MEET[A]][MEET[B]] = (A >= B)
for i in range(ND):
    for j in range(ND):
        if LD[i][j] is None: LD[i][j] = new()
Q = [[new() for t in range(TT)] for d in range(ND)]
QL = [[new() for u in range(U)] for d in range(ND)]
R = {(t, s, k): (True if (k == 0 and t == s) else new()) for t in range(TT) for s in range(TT) for k in range(W + 1)}
for t in range(TT):
    for s in range(TT): R[(t, s, 'inf')] = R[(t, s, W)]       # offsets ≥ W: eventually constant
Z = [[new() for u in range(U)] for t in range(TT)]
LL = [[True if u == v else new() for v in range(U)] for u in range(U)]
def le(a, b):
    ka, kb = a[0], b[0]
    if kb == 'T': return True
    if ka == 'T': return False
    if ka == 'd':
        if kb == 'd': return LD[a[1]][b[1]]
        if kb == 'c': return Q[a[1]][b[1]]
        return QL[a[1]][b[1]]
    if ka == 'c':
        if kb == 'd' or kb == 'L' and False: return False
        if kb == 'd': return False
        if kb == 'c':
            k = b[2] - a[2]
            return False if k < 0 else R[(a[1], b[1], min(k, W))]
        return Z[a[1]][b[1]]
    if kb in ('d', 'c'): return False
    return LL[a[1]][b[1]]
D = [('d', i) for i in range(ND)]; Ls = [('L', u) for u in range(U)]; TOP = ('T',)
SAMPLE = D + [('c', t, k) for t in range(TT) for k in range(2 * W + 1)] + Ls + [TOP]
# poset axioms on the sample (shift invariance makes this complete)
for a in SAMPLE:
    for b in SAMPLE:
        if a != b and not (a[0] == 'c' and b[0] == 'c' and a[2] != b[2]): add([neg(le(a, b)), neg(le(b, a))])
        for c in SAMPLE:
            if a[0] == 'c' and a[2] != 0 and b[0] == 'c' and c[0] == 'c': continue
            add([neg(le(a, b)), neg(le(b, c)), le(a, c)])
for A in subsets:
    if len(A) > 1:
        for z in D: add([neg(le(z, ('d', P[i]))) for i in A] + [le(z, ('d', MEET[A]))])
for e in range(8, ND): add([le(('d', e), ('d', p)) for p in P])
# values
OPTC = D + [TOP] + Ls + [('c', s, d) for s in range(TT) for d in range(DL + 1)]
OPTL = D + [TOP] + Ls + ([('c', s, m) for s in range(TT) for m in range(W + 1)] if OPEN else [])
rows = list(MEET.values())
V = {(r, t): [new() for _ in OPTC] for r in rows for t in range(TT)}
VL = {(r, u): [new() for _ in OPTL] for r in rows for u in range(U)}
VT = {r: [new() for _ in OPTL] for r in rows}
for vs in list(V.values()) + list(VL.values()) + list(VT.values()):
    add(vs); [add([-vs[i], -vs[j]]) for i in range(len(vs)) for j in range(i + 1, len(vs))]
def opts(r, x):          # (selector, value element) for F(r, x)
    if x[0] == 'c':
        return [(V[(r, x[1])][i], (o if o[0] != 'c' else ('c', o[1], x[2] + o[2]))) for i, o in enumerate(OPTC)]
    if x[0] == 'L': return list(zip(VL[(r, x[1])], OPTL))
    return list(zip(VT[r], OPTL))
COLX = [('c', t, k) for t in range(TT) for k in range(W + 1)] + Ls + [TOP]
BASE = [('c', t, 0) for t in range(TT)] + Ls + [TOP]
for r in rows:
    for r2 in rows:
        if not LD[r][r2]: continue
        for x in BASE:
            for x2 in COLX:
                lx = le(x, x2)
                if lx is False: continue
                for s1, v1 in opts(r, x):
                    for s2, v2 in opts(r2, x2):
                        if x[0] == 'c' and x2[0] != 'c' and v1[0] == 'c' and v2[0] == 'c':
                            add([neg(lx), -s1, -s2])      # all n: a shifted column is not below a fixed one
                        else: add([neg(lx), -s1, -s2, le(v1, v2)])
# no-witness everywhere (flag 'nwcols': only at the periodic columns; 'nonw': nowhere)
for r in rows:
    for x in ([] if 'nonw' in FLAGS else [b for b in BASE if b[0] == 'c'] if 'nwcols' in FLAGS else
              [b for b in BASE if b[0] != 'T'] if 'notop' in FLAGS else [b for b in BASE if b[0] != 'L'] if 'nolim' in FLAGS else BASE):
        for s1, v1 in opts(r, x):
            if v1[0] == 'd': add([-s1, neg(le(v1, ('d', r)))])
            add([-s1, neg(le(x, v1))])
sol = Cadical195(bootstrap_with=cl); res = sol.solve()
print(f"T={TT} W={W} Δ={DL} U={U} E={NE}: {'SAT' if res else 'UNSAT'}  ({nv[0]} vars, {len(cl)} clauses)")
if res:
    M = set(l for l in sol.get_model() if l > 0)
    tr = lambda l: l if isinstance(l, bool) else (l in M)
    nm = lambda e: {'d': lambda: ['0'] + [('m' + ''.join(str(i+1) for i in sorted(A))) if len(A) > 1 else f'p{min(A)+1}' for A in subsets] + [f'e{k}' for k in range(NE)], }.get(e[0], lambda: None)()
    def name(e):
        if e[0] == 'd': return (['0'] + [('m' + ''.join(str(i+1) for i in sorted(A))) if len(A) > 1 else f'p{min(A)+1}' for A in subsets] + [f'e{k}' for k in range(NE)])[e[1]]
        if e[0] == 'c': return f'c{e[1]}[n+{e[2]}]'
        if e[0] == 'L': return f'L{e[1]}'
        return 'T'
    for t in range(TT):
        print(f' c{t}: below', [name(b) for b in SAMPLE if b != ('c', t, 0) and b[0] != 'd' and tr(le(('c', t, 0), b)) and b[0] != 'T'],
              ' above', [name(d) for d in D if tr(le(d, ('c', t, 0)))])
        for r in rows: print(f'   F({name(("d", r))}, c{t}[n]) =', name(next(v for s, v in opts(r, ('c', t, 0)) if s in M)))
    for u in range(U):
        print(f' L{u}: above D', [name(d) for d in D if tr(le(d, ('L', u)))], ' below L', [name(b) for b in Ls if b != ('L', u) and tr(le(('L', u), b))])
        for r in rows: print(f'   F({name(("d", r))}, L{u}) =', name(next(v for s, v in opts(r, ('L', u)) if s in M)))
    for r in rows: print(f'   F({name(("d", r))}, T) =', name(next(v for s, v in opts(r, TOP) if s in M)))
