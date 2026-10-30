"""bowtie x bowtie DCL with equivariance under a chosen subgroup of (C2)^4 (swaps ab, pq, uv, st).
   python3 dcl_eq.py GEN [GEN ...]   each GEN a 4-bit string, e.g. 1100 = (a b)(p q); the subgroup they generate."""
import itertools, sys, time
from pysat.solvers import Solver
def closure(n, rel):
    le = [[i == j for j in range(n)] for i in range(n)]
    for a, b in rel: le[a][b] = True
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if le[i][k] and le[k][j]: le[i][j] = True
    return le
nD = nC = 5
leD = closure(5, [(0,1),(0,2),(1,3),(1,4),(2,3),(2,4)]); leC = closure(5, [(0,2),(0,3),(1,2),(1,3),(2,4),(3,4)]); L = 10
def le(a, b):
    if a < nD and b < nD: return leD[a][b]
    if a < nD: return True
    if b < nD: return False
    return leC[a - nD][b - nD]
ch = lambda n, l: [frozenset(B) for r in range(1, n + 1) for B in itertools.combinations(range(n), r) if all(l[a][b] or l[b][a] for a in B for b in B)]
chD = ch(5, leD); chC = [frozenset(x + 5 for x in c) for c in ch(5, leC)]
cells = [(r, s) for r in chD for s in chC]
Z = {}; nv = 0
for c in cells:
    for v in range(L): nv += 1; Z[(c, v)] = nv
cl = []
for c in cells:
    cl.append([Z[(c, v)] for v in range(L)]); cl += [[-Z[(c, a)], -Z[(c, b)]] for a in range(L) for b in range(a + 1, L)]
    r, s = c
    mn = next(x for x in r if all(le(x, y) for y in r)); mx = next(x for x in s if all(le(y, x) for y in s))
    for v in range(L):
        if (v < nD and le(v, mn)) or (v >= nD and le(mx, v)): cl.append([-Z[(c, v)]])
for c in cells:
    for d in cells:
        if c != d and c[0] >= d[0] and c[1] <= d[1] and (len(c[0]) - len(d[0])) + (len(d[1]) - len(c[1])) == 1:
            for v in range(L): cl.append([-Z[(c, v)]] + [Z[(d, w)] for w in range(L) if le(v, w)])
def perm(bits):
    m = list(range(L))
    if bits[0]: m[1], m[2] = 2, 1
    if bits[1]: m[3], m[4] = 4, 3
    if bits[2]: m[6], m[7] = 7, 6     # C: u=5,v=6,s=7,t=8,⊤=9 → u↔v is 5↔6
    if bits[3]: m[7], m[8] = 8, 7
    return m
def permC(bits):
    m = list(range(L))
    if bits[0]: m[1], m[2] = 2, 1
    if bits[1]: m[3], m[4] = 4, 3
    if bits[2]: m[5], m[6] = 6, 5
    if bits[3]: m[7], m[8] = 8, 7
    return m
MODE = sys.argv[1]; gens = []
mxs = lambda s_: next(x for x in s_ if all(le(y, x) for y in s_))
mns = lambda r_: next(x for x in r_ if all(le(x, y) for y in r_))
for c in cells:
    for d in cells:
        if c < d:
            same = (MODE == 'Dchain' and c[0] == d[0] and mxs(c[1]) == mxs(d[1])) or \
                   (MODE == 'Cchain' and c[1] == d[1] and mns(c[0]) == mns(d[0])) or \
                   (MODE == 'cut' and mns(c[0]) == mns(d[0]) and mxs(c[1]) == mxs(d[1]))
            if same:
                for v in range(L): cl.append([-Z[(c, v)], Z[(d, v)]]); cl.append([Z[(c, v)], -Z[(d, v)]])
for g in gens:
    m = permC(g)
    for c in cells:
        gc = (frozenset(m[x] for x in c[0]), frozenset(m[x] for x in c[1]))
        for v in range(L):
            cl.append([-Z[(c, v)], Z[(gc, m[v])]])
t = time.time(); s = Solver(name='cadical195', bootstrap_with=cl); r = s.solve()
print(f"dependence {MODE}: {'SAT' if r else 'UNSAT'} ({time.time()-t:.1f}s)", flush=True)
if r:
    M = set(l for l in s.get_model() if l > 0)
    nm = ['0','a','b','p','q','u','v','s','t','T']
    sol = {c: next(v for v in range(L) if Z[(c, v)] in M) for c in cells}
    import json
    json.dump({f"{''.join(nm[x] for x in sorted(c[0]))}|{''.join(nm[x] for x in sorted(c[1]))}": nm[v] for c, v in sol.items()}, open('model.json', 'w'), indent=0)
    print('model written to model.json')
