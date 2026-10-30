"""Funnel-constrained challenge game (InfiniteCLL.face_escape_funnel), k = 3.
Moves and constraints as descent_game2/3 (per-row end labels, squeeze for rows >= A, E_A preserved). Extra prover move
"challenge l" at states where every row avoiding l is a label or contracting and none carries {l}. The adversary must
reveal an escape reachable by face-row value steps:
  (a) a path of contracting face moves (usual successor constraints) to a state in U with a face row labelled {l}; or
  (b) a path of contracting face moves to a state with a non-contracting face row, after which one non-contracting
      step lands below c with labels growing from c only, i.e. any escape state in U whose labels contain those at c.
Both reachability sets are least fixpoints of the bitset join."""
import itertools, sys, numpy as np, time, os
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'descent_game2.py')).read().split("memo = {}")[0]
exec(src)
t0 = time.time()
FACE = {l: [b for b in range(7) if l not in ROWS[b]] for l in range(3)}
LAB1 = {l: LI[frozenset([l])] for l in range(3)}
def joiner(X):
    """returns succ(s, a, mode): does some state of X follow s by a move along row a? mode 'move' = squeeze move,
    'grow' = labels grow only; plus esc(s, l): some state of X label-growing from s with a face row labelled {l}."""
    Xidx = np.flatnonzero(X); nX = len(Xidx); words = max(1, (nX + 63) // 64)
    vals = K[Xidx].astype(np.int32) * 8 + (E[Xidx].astype(np.int32) + 1)
    bits = {}
    for b in range(7):
        col = vals[:, b]
        for v in np.unique(col):
            m = np.zeros(words * 64, bool); m[:nX] = col == v
            bits[(b, int(v))] = np.packbits(m, bitorder='little').view(np.uint64)
    zero = np.zeros(words, np.uint64); cache = {}
    def allowed(b, kb, eb, sup, isA):
        key = (b, kb, eb, sup, isA)
        if key in cache: return cache[key]
        acc = zero.copy()
        for (bb, v), bs in bits.items():
            if bb != b: continue
            tk, te = v // 8, v % 8 - 1
            if not SUP[kb][tk]: continue
            if sup:
                if tk == NC: continue
                if not COMP[eb if eb >= 0 else 6][te if te >= 0 else 6]: continue
            if isA and te != eb: continue
            acc |= bs
        cache[key] = acc; return acc
    def exact(b, kb, lab):
        key = ('x', b, kb, lab)
        if key in cache: return cache[key]
        acc = zero.copy()
        if SUP[kb][lab]:
            for (bb, v), bs in bits.items():
                if bb == b and v // 8 == lab: acc |= bs
        cache[key] = acc; return acc
    def succ(s, a):
        acc = None
        for b in range(7):
            x = allowed(b, int(K[s, b]), int(E[s, b]), b in supsets[a], b == a)
            acc = x if acc is None else acc & x
            if not acc.any(): return False
        return True
    def esc(s, l):
        for b0 in FACE[l]:
            acc = None
            for b in range(7):
                x = exact(b, int(K[s, b]), LAB1[l]) if b == b0 else allowed(b, int(K[s, b]), int(E[s, b]), False, False)
                acc = x if acc is None else acc & x
                if not acc.any(): break
            if acc.any(): return True
        return False
    return succ, esc
def lfp(T, l):
    """states from which some path of contracting face moves (>= 0 steps) reaches T"""
    P = T.copy()
    while True:
        succ, _ = joiner(P)
        new = P.copy()
        for s in np.flatnonzero(~P):
            if any(K[s, a] == LT and succ(s, a) for a in FACE[l]): new[s] = True
        if (new == P).all(): return P
        P = new
HASFACENC = {l: (K[:, FACE[l]] == NC).any(1) for l in range(3)}
HASESC = {l: (K[:, FACE[l]] == LAB1[l]).any(1) for l in range(3)}
P2 = {l: lfp(HASFACENC[l], l) for l in range(3)}
print("P2 sizes", [int(P2[l].sum()) for l in range(3)], f"({time.time()-t0:.0f}s)", flush=True)
def run(U):
    succ, esc = joiner(U)
    P1 = {l: lfp(U & HASESC[l], l) for l in range(3)}
    newU = U.copy()
    for s in np.flatnonzero(~U):
        win = True
        for a in range(7):
            if K[s, a] == LT and not succ(s, a): win = False; break
        if not win: continue
        for l in range(3):
            if HASFACENC[l][s] or HASESC[l][s]: continue          # challenge not offered
            # answer must come after >= 1 move: s itself is in neither target set here
            if P1[l][s] or (P2[l][s] and esc(s, l)): continue
            win = False; break
        if win: newU[s] = True
    return newU
U = dead.copy(); it = 0
while True:
    it += 1; U2 = run(U)
    print(f"iteration {it}: adversary-winning states {U2.sum()} ({time.time()-t0:.0f}s)", flush=True)
    if (U2 == U).all(): break
    U = U2
init = ~(K == NC).any(1)
bad = np.flatnonzero(init & U)
print(f"initial states {init.sum()}, adversary wins from {len(bad)}", flush=True)
if len(bad):
    s = bad[0]
    print("example:", {tuple(sorted(ROWS[b])): (sorted(LABS[K[s, b]]) if K[s, b] < 6 else ('lt' if K[s, b] == LT else 'nc')) for b in range(7)},
          "E:", {tuple(sorted(ROWS[b])): sorted(LABS[E[s, b]]) for b in range(7) if E[s, b] >= 0})
