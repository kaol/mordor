"""Search for a translation-periodic infinite cut counterexample in the POSET version.
Elements: constants K (side D or C; K[0] = bot, K[-1] = top) and indexed elements (i, t), i in Z, t in types.
Order and F are translation invariant; relations between indexed elements depend on the class of the index
difference, cl(d) = clamp(d, -W-1, W+1). F on cross pairs (x in D, y in C) picks a constant or an indexed element
(anchor + e, v), anchor = index of x or of y, |e| <= E. Height bound: rank : kinds -> {0..H+1}, strict on <.
A model is a genuine infinite bounded poset of edge-height <= H with a witness-free cut (F extended by bot on D x D
and top elsewhere stays monotone). Height <= 5 is a theorem (Ground.cut_height5), so H <= 5 must be UNSAT.
  python3 periodic.py H nTD nTC nKD nKC [W] [E] [M] [opts]   opts: nowit (drop no-witness: control)"""
import sys, itertools, time
from pysat.solvers import Cadical153
H, nTD, nTC, nKD, nKC = map(int, sys.argv[1:6])
W = int(sys.argv[6]) if len(sys.argv) > 6 else 1
E = int(sys.argv[7]) if len(sys.argv) > 7 else 1
M = int(sys.argv[8]) if len(sys.argv) > 8 else 5
opts = sys.argv[9].split(',') if len(sys.argv) > 9 else []
T = list(range(nTD + nTC)); sideT = ['D'] * nTD + ['C'] * nTC
K = list(range(nKD + nKC)); sideK = ['D'] * nKD + ['C'] * nKC          # K[0] = bot (D), K[-1] = top (C)
BOT, TOP = 0, len(K) - 1
CLS = list(range(-W - 1, W + 2))
def cl(d): return max(-W - 1, min(W + 1, d))
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
    if not out: raise SystemExit("trivially UNSAT clause")
    S.add_clause(out); ncl += 1
def neg(l): return (not l) if isinstance(l, bool) else -l
KK = {(a, b): var() for a in K for b in K if a != b}
KI = {(k, t): var() for k in K for t in T}
IK = {(t, k): var() for t in T for k in K}
II = {(t, u, c): var() for t in T for u in T for c in CLS if t != u}
def side(e): return sideK[e[1]] if e[0] == 'K' else sideT[e[2]]
def le(a, b):
    if a == b: return True
    if side(a) == 'C' and side(b) == 'D': return False
    if a[0] == 'K' and a[1] == BOT: return True
    if b[0] == 'K' and b[1] == TOP: return True
    if a[0] == 'K' and a[1] == TOP: return False
    if b[0] == 'K' and b[1] == BOT: return False
    if a[0] == 'K' and b[0] == 'K': return KK[(a[1], b[1])]
    if a[0] == 'K': return KI[(a[1], b[2])]
    if b[0] == 'K': return IK[(a[2], b[1])]
    if a[2] == b[2]: return False          # same type, different index: incomparable (rank)
    return II[(a[2], b[2], cl(b[1] - a[1]))]
# ranks: kinds = ('K',k) / ('T',t); order encoding R[kind][r] = rank >= r, r = 1..H+1
kinds = [('K', k) for k in K] + [('T', t) for t in T]
R = {kd: {r: var() for r in range(1, H + 2)} for kd in kinds}
for kd in kinds:
    for r in range(2, H + 2): add([-R[kd][r], R[kd][r - 1]])
    if kd == ('K', BOT): add([-R[kd][1]])
    elif kd == ('K', TOP): add([R[kd][H + 1]])
    else: add([R[kd][1]]); add([-R[kd][H + 1]])
def kind(e): return ('K', e[1]) if e[0] == 'K' else ('T', e[2])
def strict(l, a, b):   # l => rank(a) < rank(b)
    ka, kb = kind(a), kind(b)
    add([neg(l), R[kb][1]])
    for r in range(1, H + 1): add([neg(l), -R[ka][r], R[kb][r + 1]])
    add([neg(l), -R[ka][H + 1]])
def elems(lo, hi):
    return [('K', k) for k in K] + [('I', i, t) for i in range(lo, hi + 1) for t in T]
# rank strictness, per relation variable (one representative each)
for (a, b), v in KK.items(): strict(v, ('K', a), ('K', b))
for (k, t), v in KI.items(): strict(v, ('K', k), ('I', 0, t))
for (t, k), v in IK.items(): strict(v, ('I', 0, t), ('K', k))
for (t, u, c), v in II.items(): strict(v, ('I', 0, t), ('I', c, u))
# transitivity on a window
t0 = time.time()
EL = elems(-6, 6)
seen = set()
for a in EL:
    if a[0] == 'I' and a[1] != 0: continue        # normalise: first element at index 0 if indexed
    for b in EL:
        lab = le(a, b)
        if lab is False or a == b: continue
        for c in EL:
            if c == b or c == a: continue
            lbc = le(b, c)
            if lbc is False: continue
            lac = le(a, c)
            key = (lab, lbc, lac)
            if key in seen: continue
            seen.add(key); add([neg(lab), neg(lbc), lac])
print(f"transitivity clauses {len(seen)} ({time.time()-t0:.1f}s)", flush=True)
# F on cross pairs
DK = [('K', k) for k in K if sideK[k] == 'D'] + [('T', t) for t in T if sideT[t] == 'D']
CKd = [('K', k) for k in K if sideK[k] == 'C'] + [('T', t) for t in T if sideT[t] == 'C']
def pat(x, y):
    c = cl(y[1] - x[1]) if (x[0] == 'I' and y[0] == 'I') else None
    return (kind(x), kind(y), c)
OPT = {}; X = {}
for xk in DK:
    for yk in CKd:
        for c in (CLS if (xk[0] == 'T' and yk[0] == 'T') else [None]):
            P = (xk, yk, c)
            o = [('K', k) for k in K]
            if xk[0] == 'T': o += [('x', e, v) for e in range(-E, E + 1) for v in T]
            if yk[0] == 'T' and not (xk[0] == 'T' and c == 0): o += [('y', e, v) for e in range(-E, E + 1) for v in T]
            OPT[P] = o; X[P] = [var() for _ in o]
            add(X[P])
            for i1 in range(len(o)):
                for i2 in range(i1 + 1, len(o)): add([-X[P][i1], -X[P][i2]])
def out(o, x, y):
    if o[0] == 'K': return o
    a = x[1] if o[0] == 'x' else y[1]
    return ('I', a + o[1], o[2])
def shift(e, s): return e if e[0] == 'K' else ('I', e[1] - s, e[2])
B = {}
def Bvar(x, y, z):    # [F(x,y) <= z]
    s = x[1] if x[0] == 'I' else (y[1] if y[0] == 'I' else 0)
    key = (shift(x, s), shift(y, s), shift(z, s))
    if key in B: return B[key]
    x, y, z = key; b = var(); B[key] = b; P = pat(x, y)
    for o, xo in zip(OPT[P], X[P]):
        l = le(out(o, x, y), z)
        add([-xo, -b, l]); add([-xo, b, neg(l)])
    return b
EL = elems(-M, M)
Del = [e for e in EL if side(e) == 'D']; Cel = [e for e in EL if side(e) == 'C']
# no witness
if 'nowit' not in opts and 'nowit1' not in opts:
    for x in Del:
        if x[0] == 'I' and x[1] != 0: continue
        for y in Cel:
            P = pat(x, y)
            for o, xo in zip(OPT[P], X[P]):
                w = out(o, x, y); add([-xo, neg(le(w, x))]); add([-xo, neg(le(y, w))])
if 'nowit1' in opts:
    for x in Del:
        if x[0] == 'I' and x[1] != 0: continue
        for y in Cel:
            P = pat(x, y)
            for o, xo in zip(OPT[P], X[P]):
                w = out(o, x, y); add([-xo, neg(le(y, w))])
t0 = time.time()
# monotonicity in each argument
for x in (Del if 'nomono' not in opts else []):
    for x2 in Del:
        if x2 == x: continue
        L = le(x, x2)
        if L is False: continue
        if not ((x[0] == 'I' and x[1] == 0) or (x[0] == 'K' and (x2[0] != 'I' or x2[1] == 0))): continue
        for y in Cel:
            P2 = pat(x2, y)
            for o, xo in zip(OPT[P2], X[P2]):
                add([neg(L), -xo, Bvar(x, y, out(o, x2, y))])
for y in (Cel if 'nomono' not in opts else []):
    for y2 in Cel:
        if y2 == y: continue
        L = le(y, y2)
        if L is False: continue
        if not ((y[0] == 'I' and y[1] == 0) or (y[0] == 'K' and (y2[0] != 'I' or y2[1] == 0))): continue
        for x in Del:
            P2 = pat(x, y2)
            for o, xo in zip(OPT[P2], X[P2]):
                add([neg(L), -xo, Bvar(x, y, out(o, x, y2))])
print(f"vars {nv}, clauses {ncl}, B vars {len(B)} ({time.time()-t0:.1f}s)", flush=True)
t0 = time.time(); ok = S.solve(); print("H", H, "types", nTD, nTC, "consts", nKD, nKC, "W E M", W, E, M, opts,
                                      "->", "SAT" if ok else "UNSAT", f"({time.time()-t0:.1f}s)", flush=True)
if ok:
    m = set(l for l in S.get_model() if l > 0)
    import pickle
    model = {'K': K, 'T': T, 'sideK': sideK, 'sideT': sideT, 'W': W, 'H': H,
             'KK': {k: v in m for k, v in KK.items()}, 'KI': {k: v in m for k, v in KI.items()},
             'IK': {k: v in m for k, v in IK.items()}, 'II': {k: v in m for k, v in II.items()},
             'rank': {kd: sum(1 for r in R[kd] if R[kd][r] in m) for kd in kinds},
             'F': {P: OPT[P][[i for i, xo in enumerate(X[P]) if xo in m][0]] for P in OPT}}
    pickle.dump(model, open(f"model_H{H}_{nTD}{nTC}{nKD}{nKC}.pkl", "wb")); print("model saved", flush=True)
