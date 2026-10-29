"""Bent cells of the terminal state: where must no-witness fail in a finite near-model?  The encoding of ctlocal.py
(⊥, the 7 meets, E extra D-elements, columns x, v, w = x ⊓ v, ⊤, N extra columns), with every no-witness clause W1/W2 at
every cell made soft; MaxSAT (RC2) finds the minimum number of dropped clauses and enumerates all minimum sets.
   python3 bentcells.py N E all out K MODE    (K: max sets listed; MODE: ct = T + case II + ¬CT, T = T + case II, none)
Each line names the dropped clause, its cell, the column's order relations to x, v, w, the cells whose value is that
column, and the cell value with its labels."""
import sys, itertools
from pysat.solvers import Cadical195
NX, NE, NWC, WD = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
subsets = [frozenset(A) for n in range(1, 4) for A in itertools.combinations(range(3), n)]
BOT = 0; ROW = {A: 1 + k for k, A in enumerate(subsets)}; P = [ROW[frozenset([i])] for i in range(3)]; Hr = ROW[frozenset(range(3))]
E = list(range(8, 8 + NE)); base = 8 + NE
X_, V_, W_ = base, base + 1, base + 2; EXTRA = list(range(base + 3, base + 3 + NX)); TOP = base + 3 + NX
EL = list(range(TOP + 1)); n = len(EL); COLS = [X_, V_, W_] + EXTRA + [TOP]
nv = [0]
def new(): nv[0] += 1; return nv[0]
le = [[new() for j in EL] for i in EL]; cl = []
for i in EL:
    cl += [[le[i][i]], [le[BOT][i]], [le[i][TOP]]]
    for j in EL:
        if i < j: cl.append([-le[i][j], -le[j][i]])
        for k in EL: cl.append([-le[i][j], -le[j][k], le[i][k]])
for A in subsets:
    for B in subsets:
        if A != B: cl.append([le[ROW[A]][ROW[B]]] if A >= B else [-le[ROW[A]][ROW[B]]])
for A in subsets:
    if len(A) > 1:
        for z in EL: cl.append([-le[z][P[i]] for i in A] + [le[z][ROW[A]]])
inD = {z: new() for z in EL}
for z in EL:
    cl.append([-inD[z]] + [le[z][p] for p in P])
    for p in P: cl.append([inD[z], -le[z][p]])
for z in [BOT] + list(ROW.values()) + E: cl.append([inD[z]])
for z in [X_, V_] + EXTRA + [TOP]: cl.append([-inD[z]])
cl.append([inD[W_]] if WD == 'in' else [-inD[W_]])
cl += [[le[W_][X_]], [le[W_][V_]]]
for z in EL: cl.append([-le[z][X_], -le[z][V_], le[z][W_]])       # w = x ⊓ v
F = {(a, c): [new() for _ in EL] for a in ROW.values() for c in COLS}
for vs in F.values(): cl.append(vs); cl += [[-vs[i], -vs[j]] for i in range(n) for j in range(i + 1, n)]
def Fle(a, c, z, pos=True):        # literal-clause helper: F(a,c) ≤ z  as implications over one-hot values
    return [[-F[(a, c)][u], le[u][z]] for u in EL] if pos else None
cells = list(F)
for (a, c) in cells:
    for (b, d) in cells:
        if (a, c) == (b, d): continue
        for u in EL:
            for t in EL:
                if u != t: cl.append([-le[a][b], -le[c][d], -F[(a, c)][u], -F[(b, d)][t], le[u][t]])
SEL = {}
for (a, c) in cells:
    for k in (1, 2):
        SEL[(a, c, k)] = new()
    for u in EL:
        cl.append([inD[c], -F[(a, c)][u], -le[u][a], SEL[(a, c, 1)]]); cl.append([inD[c], -F[(a, c)][u], -le[c][u], SEL[(a, c, 2)]])
MODE = sys.argv[6] if len(sys.argv) > 6 else 'ct'
# terminal state at x
def val_is(a, c, z): return F[(a, c)][z]
for u in (EL if MODE != 'none' else []):
    cl.append([-F[(P[0], X_)][u], le[u][X_]])                                  # g1(x) ≤ x
    cl.append([-F[(P[0], X_)][u], le[u][P[1]]]); cl.append([-F[(P[0], X_)][u], -le[u][P[0]]]); cl.append([-F[(P[0], X_)][u], -le[u][P[2]]])  # Λ(g1 x) = {2}
    cl.append([-F[(Hr, X_)][u], le[u][P[0]]]); cl.append([-F[(Hr, X_)][u], le[u][P[1]]]); cl.append([-F[(Hr, X_)][u], -le[u][P[2]]])     # Λ(h x) = {1,2}
if MODE != 'none': cl.append([F[(P[1], X_)][V_]])                                                   # v = g2(x)
if MODE != 'none': cl.append([-le[V_][X_]])                                                          # case II
for u in (EL if MODE == 'ct' else []):
    cl.append([-F[(P[0], W_)][u], -le[u][V_]])                                    # g1(w) ≰ v
    cl.append([-F[(P[1], W_)][u], -le[u][X_]])                                    # g2(w) ≰ x

from pysat.formula import WCNF
from pysat.examples.rc2 import RC2
nm = {BOT: '0'}; nm.update({ROW[A]: ('m' + ''.join(str(i+1) for i in sorted(A))) if len(A) > 1 else f'p{min(A)+1}' for A in subsets})
nm.update({e: f'e{k}' for k, e in enumerate(E)}); nm.update({X_: 'x', V_: 'v', W_: 'w', TOP: 'T'}); nm.update({c: f'c{k}' for k, c in enumerate(EXTRA)})
KMAX = int(sys.argv[5]) if len(sys.argv) > 5 else 20
seen = 0; blocks = []
best = None
while seen < KMAX:
    w = WCNF()
    for c_ in cl + blocks: w.append(c_)
    for s_ in SEL.values(): w.append([-s_], weight=1)
    with RC2(w) as rc:
        m = rc.compute()
        if m is None: print('no more'); break
        cost = rc.cost
    if best is None: best = cost; print('minimum bent cells:', cost)
    if cost > best: print('cost rises to', cost); break
    M = set(l for l in m if l > 0)
    lab = lambda z: ''.join(str(i+1) for i in range(3) if le[z][P[i]] in M)
    val = lambda a, c: next(u for u in EL if F[(a, c)][u] in M)
    dropped = [key for key, s_ in SEL.items() if s_ in M]
    desc = []
    for (a, c, k) in dropped:
        rel = []
        for o in [X_, V_, W_]:
            if c == o: continue
            l1, l2 = le[c][o] in M, le[o][c] in M
            rel.append(f"{'=' if l1 and l2 else '<' if l1 else '>' if l2 else '∥'}{nm[o]}")
        eqs = [f"{nm[a2]}({nm[c2]})" for (a2, c2) in cells if c2 != c and val(a2, c2) == c]
        u = val(a, c)
        desc.append(f"W{k}@({nm[a]},{nm[c]}{'' if c in (X_,V_,W_,TOP) else ' '+''.join(rel)}{' ='+'='.join(eqs) if eqs else ''}) val {nm[u]}{'['+lab(u)+']' if inD[u] in M else ''}")
    print(' ', '; '.join(desc), f"| w∈D={inD[W_] in M}")
    blocks.append([-SEL[k_] for k_ in dropped])
    seen += 1
