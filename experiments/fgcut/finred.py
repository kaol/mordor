"""Finite models of the reduced crossing theory: elements = ⊥, the 7 meets of p1,p2,p3 (strict crossing), E extra D-elements,
NU columns (the last is ⊤).  Partial order free except the meet structure; meets are glbs; D = ↓p1 ∪ ↓p2 ∪ ↓p3; rows =
the 7 meets; F one-hot; monotone; no witness.   python3 finred.py NU E [strict|crossing]"""
import sys, itertools, time
from pysat.solvers import Cadical195
NU, NE = int(sys.argv[1]), int(sys.argv[2]); SHAPE = sys.argv[3] if len(sys.argv) > 3 else 'strict'
subsets = [frozenset(A) for n in range(1, 4) for A in itertools.combinations(range(3), n)]
BOT = 0; ROW = {A: 1 + k for k, A in enumerate(subsets)}; P = [ROW[frozenset([i])] for i in range(3)]
E = list(range(8, 8 + NE)); U = list(range(8 + NE, 8 + NE + NU)); TOP = U[-1]
X = list(range(8 + NE + NU)); n = len(X); Dset = [BOT] + list(ROW.values()) + E
nv = [0]
def new(): nv[0] += 1; return nv[0]
le = [[new() for j in X] for i in X]
cl = []
for i in X:
    cl.append([le[i][i]]); cl.append([le[BOT][i]]); cl.append([le[i][TOP]])
    for j in X:
        if i < j: cl.append([-le[i][j], -le[j][i]])
        for k in X: cl.append([-le[i][j], -le[j][k], le[i][k]])
for A in subsets:
    for B in subsets:
        if A != B:
            cl.append([le[ROW[A]][ROW[B]]] if A >= B else ([-le[ROW[A]][ROW[B]]] if (SHAPE == 'strict' or len(B) == 1) else []))
cl = [c for c in cl if c]
for A in subsets:                                    # glb
    if len(A) > 1:
        for x in X: cl.append([-le[x][P[i]] for i in A] + [le[x][ROW[A]]])
for e in E: cl.append([le[e][p] for p in P])          # extras in D
for u in U:                                          # columns outside D
    for p in P: cl.append([-le[u][p]])
for i, u in enumerate(U):                            # symmetry breaking: columns numbered by a linear extension
    for j, w in enumerate(U):
        if j < i: cl.append([-le[u][w]])
for i, e in enumerate(E):
    for j, f in enumerate(E):
        if j < i: cl.append([-le[e][f]])
Fv = {(a, u): [new() for v in X] for a in ROW.values() for u in U}
for c in Fv.values():
    cl.append(c); cl += [[-c[i], -c[j]] for i in range(n) for j in range(i + 1, n)]
cells = list(Fv)
for (a, u) in cells:
    for (b, w) in cells:
        if (a, u) == (b, w): continue
        rowle = le[a][b]                             # fixed true/false via unit clauses; include as literal
        for v in X:
            for x in X:
                if v == x: continue
                cl.append([-rowle, -le[u][w], -Fv[(a, u)][v], -Fv[(b, w)][x], le[v][x]])
    for v in X:                                      # no witness: F(a,u) ≰ a, u ≰ F(a,u)
        cl.append([-Fv[(a, u)][v], -le[v][a]]); cl.append([-Fv[(a, u)][v], -le[u][v]])
t0 = time.time()
s = Cadical195(bootstrap_with=cl)
r = s.solve()
print(f"NU={NU} E={NE} {SHAPE}: {'SAT' if r else 'UNSAT'} ({len(cl)} clauses, {time.time()-t0:.1f}s)", flush=True)
if r:
    M = set(l for l in s.get_model() if l > 0)
    names = {BOT: '0'}; names.update({ROW[A]: ('m' + ''.join(str(i+1) for i in sorted(A))) if len(A) > 1 else f'p{min(A)+1}' for A in subsets})
    names.update({e: f'e{k}' for k, e in enumerate(E)}); names.update({u: f'u{k}' for k, u in enumerate(U)}); names[TOP] = 'T'
    print('order (covers among columns and extras):')
    for i in X:
        ups = [names[j] for j in X if j != i and le[i][j] in M and not any(k != i and k != j and le[i][k] in M and le[k][j] in M for k in X)]
        print(f'  {names[i]} < {ups}')
    for (a, u), c in Fv.items():
        v = next(v for v in X if c[v] in M); print(f'  F({names[a]},{names[u]}) = {names[v]}')
