"""Shared free-analysis helpers (no SAT): loads every distinct stored model (brief291/world.py W), caches
the W0+n1 ones and the relaxed 'base + every Z-row lands' ones. Everything recomputed from the definitions."""
import sys, os, json, pickle
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W, load_all, dedup
CACHE = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'models_cache.pkl')
def colours(w):
    F = w.F; b = w.bot
    return sorted({F[b][y] for y in range(w.n) if F[b][y] in w.atoms})
def bounded(w, A=None):
    A = colours(w) if A is None else A
    return any(all(w.le[c][z] for c in A) for z in w.Z)
def get(extra=()):
    if os.path.exists(CACHE) and not extra:
        D = pickle.load(open(CACHE, 'rb'))
    else:
        D = []
        for name, w in dedup(load_all(extra)):
            try:
                if not w.base(): continue
                lands = all(w.lam(x) is not None for x in w.Z)
                inW0 = w.w0flat() and w.w0()
            except Exception: continue
            D.append((name, w.sets, w.F, inW0, lands))
        if not extra: pickle.dump(D, open(CACHE, 'wb'))
    return [(name, W(s, F), inW0, lands) for name, s, F, inW0, lands in D]
def U(w, x, j, top=None):
    v = w.top if top is None else top
    for _ in range(j): v = w.F[x][v]
    return v
def descfrom(w, x, Y):
    v = Y; out = []
    while v not in out: out.append(v); v = w.F[x][v]
    return out
def lamfrom(w, x, Y):
    return next((v for v in descfrom(w, x, Y) if w.h[v] <= 2), None)
def gfp_row(w, S, top=None):
    """greatest fixed point of the joint row g_S = join of F(z, .) over z in S, by descent from top."""
    v = w.top if top is None else top; L = w.L
    while True:
        u = w.bot
        for z in S: u = L.join[u][w.F[z][v]]
        if u == v: return v
        v = u
