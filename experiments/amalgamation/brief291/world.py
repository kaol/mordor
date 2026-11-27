"""Independent W0-flat / W0 checker from the definitions (frontier §1), plus a loader of every stored model JSON in the
repository (read-only). A model = (lattice sets, F table). Nothing here is a SAT encoding."""
import sys, os, json, glob
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation'); sys.path.insert(0, '/home/user/mordor/experiments/separation')
import separator_stages as ss
REPO = '/home/user/mordor/experiments/amalgamation'

class W:
    def __init__(s, sets, F):
        s.sets = sets; s.L = L = ss.Lat(sets); s.F = F; s.n = n = L.n; s.le = L.le; s.h = L.rank
        s.bot, s.top = L.bot, L.top; le = s.le; h = s.h
        s.mono = all(le[F[x][y]][F[x2][y2]] for x in range(n) for y in range(n) for x2 in L.covers_up[x] + [x]
                     for y2 in L.covers_up[y] + [y])
        s.Z = [y for y in range(n) if F[s.bot][y] == s.bot]
        s.hi = [y for y in range(n) if h[y] >= 3]
        s.M2 = [m for m in s.Z if h[m] == 2]; s.atoms = [q for q in s.Z if h[q] == 1]
        s._a = {}
    def a(s, x):
        if x not in s._a:
            v = s.top
            while s.F[x][v] != v: v = s.F[x][v]
            s._a[x] = v
        return s._a[x]
    def b(s, y):                      # lfp of F(., y) by ascent from bottom
        v = s.bot
        while s.F[v][y] != v: v = s.F[v][y]
        return v
    def desc(s, x):
        v = s.top; out = []
        while v not in out: out.append(v); v = s.F[x][v]
        return out
    def lidx(s, x):
        return next((i for i, v in enumerate(s.desc(x)) if s.h[v] <= 2), None)
    def lam(s, x):
        i = s.lidx(x); return None if i is None else s.desc(x)[i]
    def last_hi(s, x):
        i = s.lidx(x); return None if not i else s.desc(x)[i - 1]
    def exits(s, x): p = s.lam(x); return p is not None and s.F[s.bot][p] != s.bot
    def c(s, x): return s.F[s.bot][s.lam(x)] if s.exits(x) else None
    def fixed(s, q): return s.exits(q) and s.c(q) == q
    def selfland(s, m): return s.lam(m) == m
    def tdesc(s): return s.desc(s.bot)
    def dN(s):
        tb = s.tdesc(); nz = [t for t in tb if t != s.bot]; d = nz[-1] if nz else None
        return d, (tb.index(d) if d is not None else None)
    # worlds
    def base(s):
        return (s.mono and s.a(s.bot) == s.bot and all(s.h[z] <= 2 for z in s.Z) and bool(s.M2) and s.h[s.top] >= 3)
    def Ta(s, x): return all(not s.le[y][s.F[x][y]] for y in s.hi)
    def Tb(s, x): return all(not s.le[s.F[x][y]][x] for y in s.hi)
    def w0flat(s):
        return s.base() and all(s.Ta(x) for x in s.Z) and all(s.Tb(x) for x in s.Z if s.h[x] <= 1)
    def w0(s): return s.w0flat() and all(s.Tb(x) for x in s.M2)
    def nofix(s): return not any(s.fixed(q) for q in s.atoms)
    def noexit(s): return not any(s.exits(x) for x in s.Z)
    def witnesses(s): return [m for m in s.M2 if s.selfland(m)]

def load_all(extra=()):
    files = sorted(set(glob.glob(REPO + '/**/*.json', recursive=True)) | set(extra))
    out = []
    for f in files:
        try: D = json.load(open(f))
        except Exception: continue
        D = D if isinstance(D, list) else [D]
        for k, d in enumerate(D):
            if isinstance(d, dict) and 'sets' in d and 'F' in d:
                try: out.append((f.replace(REPO + '/', '') + f'#{k}', W(d['sets'], d['F'])))
                except Exception as e: pass
    return out

def dedup(models):
    seen = set(); out = []
    for name, w in models:
        key = (tuple(w.sets), tuple(map(tuple, w.F)))
        if key in seen: continue
        seen.add(key); out.append((name, w))
    return out
