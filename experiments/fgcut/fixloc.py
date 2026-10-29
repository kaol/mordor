"""Local test of the label-fixed terminal state (log §34.3z²⁶).  Reduced meet-row theory of a strictly crossing triple:
elements ⊥, the 7 meets (glbs), E extra D-elements, columns y, ⊤ and N extra columns; F on the 7 meet rows × all
columns, monotone.  At y: h(y) ≤ y (h = g₁₂₃), every glb z_A = y ⊓ g_A(y) exists among the elements and lies in D (HT),
and y is minimal: no listed column c < y outside D has h(c) ≤ c.  The label fixed point K (Λ(z_K) = K) is then forced
and printed.  No-witness at the columns in NW:
   yT    — y and ⊤ only;
   vals  — y, ⊤ and every extra column that is a value g_A(y) or g_A(⊤);
   reach — every column reachable from y and ⊤ by row values (exact, by levels);
   all   — every column (vacuous: the reduced theory has no finite model, §34.3z²⁰).
   python3 fixloc.py N E NW"""
import sys, itertools
from pysat.solvers import Cadical195
NX, NE, NWC = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
BARE = len(sys.argv) > 4 and sys.argv[4] == 'bare'      # control: drop the terminal hypotheses at y
subsets = [frozenset(A) for n in range(1, 4) for A in itertools.combinations(range(3), n)]
BOT = 0; ROW = {A: 1 + k for k, A in enumerate(subsets)}; P = [ROW[frozenset([i])] for i in range(3)]; Hr = ROW[frozenset(range(3))]
E = list(range(8, 8 + NE)); Y = 8 + NE; EXTRA = list(range(Y + 1, Y + 1 + NX)); TOP = Y + 1 + NX
EL = list(range(TOP + 1)); n = len(EL); COLS = [Y] + EXTRA + [TOP]
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
for z in COLS: cl.append([-inD[z]])
F = {(a, c): [new() for _ in EL] for a in ROW.values() for c in COLS}
for vs in F.values(): cl.append(vs); cl += [[-vs[i], -vs[j]] for i in range(n) for j in range(i + 1, n)]
cells = list(F)
for (a, c) in cells:
    for (b, d) in cells:
        if (a, c) == (b, d): continue
        for u in EL:
            for t in EL:
                if u != t: cl.append([-le[a][b], -le[c][d], -F[(a, c)][u], -F[(b, d)][t], le[u][t]])
# HT with explicit glbs: G[A][u] ⇔ u = y ⊓ g_A(y)
G = {A: [new() for _ in EL] for A in subsets}
for A in subsets:
    vs = G[A]; cl.append(vs); cl += [[-vs[i], -vs[j]] for i in range(n) for j in range(i + 1, n)]
    for u in EL:
        cl += [[-vs[u], le[u][Y]]] + ([] if BARE else [[-vs[u], inD[u]]])
        for t in EL:
            cl.append([-vs[u], -F[(ROW[A], Y)][t], le[u][t]])
            for z in EL: cl.append([-vs[u], -F[(ROW[A], Y)][t], -le[z][Y], -le[z][t], le[z][u]])
for u in (EL if not BARE else []): cl.append([-F[(Hr, Y)][u], le[u][Y]])        # h(y) ≤ y
for c in (EXTRA if not BARE else []):                                              # minimality of y
    for u in EL: cl.append([-le[c][Y], -F[(Hr, c)][u], -le[u][c]])
isval = {}
for c in EXTRA:
    isval[c] = new()
    for a in ROW.values():
        for c0 in (Y, TOP): cl.append([-F[(a, c0)][c], isval[c]])
if NWC == 'reach':                                                                 # R[k][c]: c reached in ≤ k steps
    R = [{c: (new() if c in EXTRA else None) for c in COLS} for _ in range(NX + 1)]
    for c in EXTRA: cl.append([-R[0][c]])
    for k in range(1, NX + 1):
        for c in EXTRA:
            sup = [R[k - 1][c]]
            for a in ROW.values():
                for c0 in COLS:
                    if c0 == c: continue
                    t = new(); sup.append(t)
                    cl.append([-t, F[(a, c0)][c]])
                    if c0 in EXTRA: cl.append([-t, R[k - 1][c0]])
            cl.append([-R[k][c]] + sup)
            for a in ROW.values():
                for c0 in (Y, TOP): cl.append([-F[(a, c0)][c], R[k][c]])
                for c0 in EXTRA:
                    if c0 != c: cl.append([-F[(a, c0)][c], -R[k - 1][c0], R[k][c]])
            cl.append([-R[k - 1][c], R[k][c]])
    isval = {c: R[NX][c] for c in EXTRA}
for (a, c) in cells:
    if NWC == 'yT' and c not in (Y, TOP): continue
    g = [] if (NWC == 'all' or c in (Y, TOP)) else [-isval[c]]
    for u in EL:
        cl.append(g + [-F[(a, c)][u], -le[u][a]]); cl.append(g + [-F[(a, c)][u], -le[c][u]])
s = Cadical195(bootstrap_with=cl); r = s.solve()
print(f"N={NX} E={NE} NW at {NWC}{' (bare)' if BARE else ''}: {'SAT' if r else 'UNSAT'}")
if r:
    M = set(l for l in s.get_model() if l > 0)
    nm = {BOT: '0'}; nm.update({ROW[A]: ('m' + ''.join(str(i+1) for i in sorted(A))) if len(A) > 1 else f'p{min(A)+1}' for A in subsets})
    nm.update({e: f'e{k}' for k, e in enumerate(E)}); nm.update({Y: 'y', TOP: 'T'}); nm.update({c: f'c{k}' for k, c in enumerate(EXTRA)})
    lab = lambda z: frozenset(i for i in range(3) if le[z][P[i]] in M)
    val = lambda a, c: next(u for u in EL if F[(a, c)][u] in M)
    print(' covers:', ', '.join(f"{nm[i]}<{nm[j]}" for i in EL for j in EL if i != j and le[i][j] in M and not any(k not in (i, j) and le[i][k] in M and le[k][j] in M for k in EL) and i != BOT and j != TOP))
    for A in subsets:
        u = next(u for u in EL if G[A][u] in M); g = val(ROW[A], Y)
        print(f"  g_{nm[ROW[A]]}(y) = {nm[g]}{' ['+''.join(str(i+1) for i in sorted(lab(g)))+']' if inD[g] in M else ''},  z = {nm[u]} [{''.join(str(i+1) for i in sorted(lab(u)))}]"
              + ('   <- label fixed' if lab(u) == A else ''))
