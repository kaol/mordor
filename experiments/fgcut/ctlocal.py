"""Local test of the cross-row transfer (CT) at the terminal state.  Elements: ⊥, the 7 meets of a strictly crossing
triple (glbs), E extra D-elements, columns x, v, w, ⊤ and N extra columns.  F on all rows × all columns, monotone
everywhere.  No-witness only at the cells of the columns in NWCOLS.  Terminal hypotheses at x, v = g2(x), w = x ⊓ v
(glb), and the negation of CT: g1(w) ≰ v and g2(w) ≰ x.   python3 ctlocal.py N E NWCOLS wD   (NWCOLS e.g. xvw, xvwT, all;
wD = 'in' (w ∈ D) | 'out' (w ∉ D))"""
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
NW = COLS if NWC == 'all' else [{'x': X_, 'v': V_, 'w': W_, 'T': TOP}[ch] for ch in NWC]
for (a, c) in cells:
    if c not in NW: continue
    for u in EL:
        cl.append([inD[c], -F[(a, c)][u], -le[u][a]]); cl.append([inD[c], -F[(a, c)][u], -le[c][u]])
# terminal state at x
def val_is(a, c, z): return F[(a, c)][z]
for u in EL:
    cl.append([-F[(P[0], X_)][u], le[u][X_]])                                  # g1(x) ≤ x
    cl.append([-F[(P[0], X_)][u], le[u][P[1]]]); cl.append([-F[(P[0], X_)][u], -le[u][P[0]]]); cl.append([-F[(P[0], X_)][u], -le[u][P[2]]])  # Λ(g1 x) = {2}
    cl.append([-F[(Hr, X_)][u], le[u][P[0]]]); cl.append([-F[(Hr, X_)][u], le[u][P[1]]]); cl.append([-F[(Hr, X_)][u], -le[u][P[2]]])     # Λ(h x) = {1,2}
cl.append([F[(P[1], X_)][V_]])                                                   # v = g2(x)
cl.append([-le[V_][X_]])                                                          # case II
for u in EL:
    cl.append([-F[(P[0], W_)][u], -le[u][V_]])                                    # g1(w) ≰ v
    cl.append([-F[(P[1], W_)][u], -le[u][X_]])                                    # g2(w) ≰ x
s = Cadical195(bootstrap_with=cl); r = s.solve()
print(f"N={NX} E={NE} NW at {NWC}, w {WD} D: {'SAT (CT fails locally)' if r else 'UNSAT'}")
if r:
    M = set(l for l in s.get_model() if l > 0)
    nm = {BOT: '0'}; nm.update({ROW[A]: ('m' + ''.join(str(i+1) for i in sorted(A))) if len(A) > 1 else f'p{min(A)+1}' for A in subsets})
    nm.update({e: f'e{k}' for k, e in enumerate(E)}); nm.update({X_: 'x', V_: 'v', W_: 'w', TOP: 'T'}); nm.update({c: f'c{k}' for k, c in enumerate(EXTRA)})
    lab = lambda z: ''.join(str(i+1) for i in range(3) if le[z][P[i]] in M)
    print(' order:', ', '.join(f"{nm[i]}<{nm[j]}" for i in EL for j in EL if i != j and le[i][j] in M and not any(k not in (i, j) and le[i][k] in M and le[k][j] in M for k in EL) and i != BOT and j != TOP))
    for (a, c) in cells:
        if c in (X_, V_, W_):
            u = next(u for u in EL if F[(a, c)][u] in M); print(f"  F({nm[a]},{nm[c]}) = {nm[u]}" + (f" [labels {lab(u)}]" if (inD[u] in M) else ""))
