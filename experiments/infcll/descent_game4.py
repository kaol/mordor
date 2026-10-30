"""CHALLENGE VARIANT: adds the prover move "challenge l" at face-closed states (InfiniteCLL.face_escape_below): at a
column where every row avoiding l is a label or contracting and none carries {l}, the adversary must answer with a
state strictly below in which some row avoiding l carries exactly {l} (labels grow; no other relation).
Exact attractor for the strengthened descent game (k = 3), bitset join. Constraints as in descent_game2.py.
  python3 descent_game3.py [onlytop]   onlytop: successors must have a row not below them (WLOG: top is the only
  closed column, since below a closed column the labelling restricts)."""
import itertools, sys, numpy as np, time
src = open(__import__('os').path.join(__import__('os').path.dirname(__file__), 'descent_game2.py')).read().split("memo = {}")[0]
exec(src)
t0 = time.time()
ONLYTOP = len(sys.argv) > 1 and sys.argv[1] == 'onlytop'   # WLOG: top is the only closed column
HASNC = (K == NC).any(1)
def run(U):
    Uidx = np.flatnonzero(U & HASNC) if ONLYTOP else np.flatnonzero(U); nU = len(Uidx)
    words = (nU + 63) // 64
    vals = K[Uidx].astype(np.int32) * 8 + (E[Uidx].astype(np.int32) + 1)
    bits = {}
    for b in range(7):
        col = vals[:, b]
        for v in np.unique(col):
            m = np.zeros(words * 64, bool); m[:nU] = col == v
            bits[(b, int(v))] = np.packbits(m, bitorder='little').view(np.uint64)
    zero = np.zeros(words, np.uint64)
    cache = {}
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
        cache[key] = acc
        return acc
    def exact(b, kb, lab):
        key = ('x', b, kb, lab)
        if key in cache: return cache[key]
        acc = zero.copy()
        if SUP[kb][lab]:
            for (bb, v), bs in bits.items():
                if bb == b and v // 8 == lab: acc |= bs
        cache[key] = acc
        return acc
    newU = U.copy()
    for s in np.flatnonzero(~U):
        win = True
        for l in range(3):
            face = [b for b in range(7) if l not in ROWS[b]]
            lab = LI[frozenset([l])]
            if any(K[s, b] == NC for b in face) or any(K[s, b] == lab for b in face): continue
            # the adversary must answer some state below with a face row carrying exactly {l}
            ok = False
            for b0 in face:
                acc = None
                for b in range(7):
                    x = exact(b, int(K[s, b]), lab) if b == b0 else allowed(b, int(K[s, b]), int(E[s, b]), False, False)
                    acc = x if acc is None else acc & x
                    if not acc.any(): break
                if acc.any(): ok = True; break
            if not ok: win = False; break
        if not win: continue
        for a in range(7):
            if K[s, a] != LT: continue
            acc = None
            for b in range(7):
                x = allowed(b, int(K[s, b]), int(E[s, b]), b in supsets[a], b == a)
                acc = x if acc is None else acc & x
                if not acc.any(): break
            if not acc.any(): win = False; break
        if win: newU[s] = True
    return newU
U = dead.copy()
it = 0
while True:
    it += 1
    U2 = run(U)
    print(f"iteration {it}: adversary-winning states {U2.sum()} ({time.time()-t0:.0f}s)", flush=True)
    if (U2 == U).all() or not U2.any() and False: break
    U = U2
init = ~(K == NC).any(1)
bad = np.flatnonzero(init & U)
print(f"initial states {init.sum()}, adversary wins from {len(bad)}", flush=True)
if len(bad):
    s = bad[0]
    print("example:", {tuple(sorted(ROWS[b])): (sorted(LABS[K[s, b]]) if K[s, b] < 6 else ('lt' if K[s, b] == LT else 'nc')) for b in range(7)},
          "E:", {tuple(sorted(ROWS[b])): sorted(LABS[E[s, b]]) for b in range(7) if E[s, b] >= 0})
np.save('U.npy', U)
