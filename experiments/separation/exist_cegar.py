"""Exact maximum of the existential minimum on a fixed lattice, by CEGAR (log §34.3z¹³⁶).

Question: does some monotone F and cut D on L have existential minimum (fewest stages over all maximal-separator
runs, `separator_stages.exist_min`) ≥ k?  Outer SAT (CaDiCaL) over f[x,y,v] (one-hot, monotone) and d[v] (cut).
Each candidate is checked exactly in Python; if it has a terminating run of < k stages, a shortest one is extracted,
with its stages T_0 … T_j and chosen separators, and blocked by the clause
  ¬( ∧_i bad-set(T_i) = B_i  ∧  every chosen s is a maximal separator of its pair  ∧  goal(T_j) ),
which no instance with existential minimum ≥ k satisfies (sound). UNSAT ⇒ maximum < k; SAT with a verified model
⇒ maximum ≥ k.
With --general the runs use general separators (any s ≥ F(x, y), y ≰ s; the blocking clause drops maximality).
With --nodesc: search for an instance with NO maximum-gap-descending run (blocking each descending run found).
  python3 exist_cegar.py [--general] [--nodesc] (pencil K | linear K SEED COUNT | chain N | closure K M SEED COUNT) KMAX [SECONDS]
"""
import sys, itertools, time, random
from pysat.solvers import Cadical153
import separator_stages as ss

class Cegar:
    def __init__(self, L):
        self.L = L; n = L.n; self.n = n; self.nv = 0; self.vars = {}; self.S = Cadical153(); le = L.le
        f = lambda x, y, v: self.v('f', x, y, v)
        for x in range(n):
            for y in range(n):
                lits = [f(x, y, v) for v in range(n)]; self.S.add_clause(lits)
                for a, b in itertools.combinations(lits, 2): self.S.add_clause([-a, -b])
        for x in range(n):
            for x2 in L.covers_up[x]:
                for y in range(n):
                    for v in range(n): self.S.add_clause([-f(x, y, v)] + [f(x2, y, w) for w in range(n) if le[v][w]])
        for y in range(n):
            for y2 in L.covers_up[y]:
                for x in range(n):
                    for v in range(n): self.S.add_clause([-f(x, y, v)] + [f(x, y2, w) for w in range(n) if le[v][w]])
        d = lambda v: self.v('d', v)
        self.S.add_clause([d(L.bot)]); self.S.add_clause([-d(L.top)])
        for a in range(n):
            for b in L.covers_up[a]: self.S.add_clause([-d(b), d(a)])
        self.badc = {}; self.iters = 0
    def v(self, *key):
        if key not in self.vars: self.nv += 1; self.vars[key] = self.nv
        return self.vars[key]
    def iff_or(self, out, lits):
        for l in lits: self.S.add_clause([out, -l])
        self.S.add_clause([-out] + list(lits))
    def iff_and(self, out, lits):
        for l in lits: self.S.add_clause([-out, l])
        self.S.add_clause([out] + [-l for l in lits])
    def fle(self, x, y, s):
        key = ('fle', x, y, s)
        if key not in self.vars:
            o = self.v(*key); self.iff_or(o, [self.v('f', x, y, w) for w in range(self.n) if self.L.le[w][s]])
        return self.vars[key]
    def yle(self, x, y):
        key = ('yle', x, y)
        if key not in self.vars:
            o = self.v(*key); self.iff_or(o, [self.v('f', x, y, w) for w in range(self.n) if self.L.le[y][w]])
        return self.vars[key]
    def bad(self, T, x, y):
        key = (T, x, y)
        if key not in self.badc:
            L = self.L
            if L.le[y][x]: self.badc[key] = None
            else:
                o = self.v('bad', T, x, y)
                self.iff_and(o, [self.v('d', x), -self.v('d', y)] + [-self.fle(x, y, s) for s in T if not L.le[y][s]])
                self.badc[key] = o
        return self.badc[key]
    def block(self, run):
        """run = list of (T, {pair: separator}) for non-goal stages, then final T (goal)."""
        L = self.L; conj = []
        for T, ch in run[:-1]:
            for x in T:
                for y in T:
                    b = self.bad(T, x, y)
                    if b is None: continue
                    conj.append(b if (x, y) in ch else -b)
            for (x, y), s in ch.items(): conj.append(self.fle(x, y, s))    # maximality of s is static given F ≤ s
        Tf = run[-1]; g = self.v('goal', Tf)
        bl = [self.bad(Tf, x, y) for x in Tf for y in Tf]; bl = [b for b in bl if b is not None]
        stuck = []
        for x in Tf:
            for y in Tf:
                b = self.bad(Tf, x, y)
                if b is None: continue
                a = self.v('stk', Tf, x, y); self.iff_and(a, [b, self.yle(x, y)]); stuck.append(a)
        nob = self.v('nobad', Tf); self.iff_and(nob, [-b for b in bl])
        self.iff_or(g, [nob] + stuck)
        self.S.add_clause([-c for c in conj] + [-g]); self.iters += 1
    def decode(self):
        m = set(x for x in self.S.get_model() if x > 0); n = self.n
        F = [[next(v for v in range(n) if self.vars[('f', x, y, v)] in m) for y in range(n)] for x in range(n)]
        return F, [self.vars[('d', v)] in m for v in range(n)]

def static_maxsep(L, s, y):
    return not L.le[y][s] and all(L.le[y][t] for t in L.covers_up[s])

GENERAL = False          # set by --general: any separator s ≥ F(x, y) with y ≰ s

def seps(L, F, x, y):
    if GENERAL: return [s for s in range(L.n) if L.le[F[x][y]][s] and not L.le[y][s]]
    return ss.max_separators(L, F[x][y], y)

def exist_min_any(L, F, D, k):
    return not shortest_runs(L, F, D, k, cap=1)

def shortest_runs(L, F, D, k, cap=200):
    """Up to cap terminating runs with fewer than k non-goal stages (BFS)."""
    T0 = ss.mclose(L, {L.bot, L.top}); layer = [(T0, [])]; out = []
    for st in range(k):
        nxt = []
        for T, hist in layer:
            bad = ss.bad_pairs(L, F, D, T)
            if not bad or any(L.le[y][F[x][y]] for x, y in bad):
                out.append(hist + [T]); 
                if len(out) >= cap: return out
                continue
            if st == k - 1: continue
            opts = [seps(L, F, x, y) for x, y in bad]
            for chv in itertools.product(*opts):
                nxt.append((ss.mclose(L, set(T) | set(chv)), hist + [(T, dict(zip(bad, chv)))]))
                if len(nxt) > 20000: break
        if out: return out
        layer = nxt
    return out

def descending_run(L, F, D, budget=200000):
    """A maximum-gap-descending terminating run (separators per `seps`), as for `shortest_runs`; None if none
    exists; 'cap' if the search budget is exceeded."""
    H = L.height; rk = L.rank; phi = lambda p: rk[p[1]] + H - rk[p[0]]; memo = set(); work = [0]
    def go(T, bound):
        bad = ss.bad_pairs(L, F, D, T)
        if not bad or any(L.le[y][F[x][y]] for x, y in bad): return [T]
        M = max(phi(p) for p in bad)
        if bound is not None and M >= bound: return None
        if (T, bound) in memo: return None
        for chv in itertools.product(*[seps(L, F, x, y) for x, y in bad]):
            work[0] += 1
            if work[0] > budget: raise RuntimeError
            r = go(ss.mclose(L, set(T) | set(chv)), M)
            if r is not None: return [(T, dict(zip(bad, chv)))] + r
        memo.add((T, bound)); return None
    try: return go(ss.mclose(L, {L.bot, L.top}), None)
    except RuntimeError: return 'cap'

def no_descent(L, seconds=None):
    """Search F, D with NO descending run: block every descending run found."""
    t0 = time.time(); C = Cegar(L)
    while True:
        if seconds and time.time() - t0 > seconds: return None, C.iters
        if not C.S.solve(): return False, C.iters
        F, D = C.decode(); r = descending_run(L, F, D)
        if r == 'cap': return 'cap', C.iters
        if r is None: return (F, D), C.iters
        C.block([(frozenset(T), ch) for T, ch in r[:-1]] + [frozenset(r[-1])])

def at_least(L, k, seconds=None):
    t0 = time.time(); C = Cegar(L)
    while True:
        if seconds and time.time() - t0 > seconds: return None, C.iters
        if not C.S.solve(): return False, C.iters
        F, D = C.decode(); runs = shortest_runs(L, F, D, k)
        if not runs:
            if not GENERAL: assert ss.exist_min(L, F, D, limit=10 ** 6) >= k
            return (F, D), C.iters
        for r in runs: C.block([(frozenset(T), ch) for T, ch in r[:-1]] + [frozenset(r[-1])])

def maximum(L, kmax, seconds):
    best = 0; wit = None; t0 = time.time()
    for k in range(1, kmax + 1):
        r, it = at_least(L, k, seconds)
        if r is None: return best, f'≥{best}, k = {k} undecided after {seconds} s ({it} blocks)', wit
        if r is False: return best, f'exact ({it} blocks at k = {k}, {time.time() - t0:.0f} s)', wit
        best = k; wit = r
    return best, 'reached KMAX', wit

if __name__ == '__main__':
    if '--general' in sys.argv: sys.argv.remove('--general'); GENERAL = True
    NODESC = '--nodesc' in sys.argv
    if NODESC: sys.argv.remove('--nodesc')
    fam = sys.argv[1]; secs = None
    def lats():
        if fam == 'pencil':
            import pencil_family; yield f'near-pencil {sys.argv[2]}', pencil_family.family(int(sys.argv[2]))[0]
        elif fam == 'chain':
            yield f'chain {sys.argv[2]}', ss.Lat([(1 << i) - 1 for i in range(int(sys.argv[2]))])
        elif fam == 'linear':
            from finite_landmarks import linear_space
            from term_sat import lat_of
            rng = random.Random(int(sys.argv[3]))
            for _ in range(int(sys.argv[4])):
                L = lat_of(linear_space(int(sys.argv[2]), rng), int(sys.argv[2]))
                if L.height == 3: yield f'linear space {sys.argv[2]}', L
        elif fam == 'closure':
            k, m, seed, cnt = (int(x) for x in sys.argv[2:6]); rng = random.Random(seed)
            for _ in range(cnt): yield f'closure {k}', ss.Lat(ss.closure_system(k, m, rng))
    nargs = {'pencil': 3, 'chain': 3, 'linear': 5, 'closure': 6}[fam]
    kmax = int(sys.argv[nargs]); secs = float(sys.argv[nargs + 1]) if len(sys.argv) > nargs + 1 else 500
    for name, L in lats():
        if NODESC:
            t0 = time.time(); r, it = no_descent(L, secs)
            verdict = ('no descent-free instance (UNSAT)' if r is False else 'undecided' if r is None else
                       'search budget exceeded' if r == 'cap' else 'FOUND an instance with no descending run')
            print(f"{name}: |L| = {L.n}, height {L.height}, {'general' if GENERAL else 'maximal'} separators: {verdict} "
                  f"({it} blocks, {time.time() - t0:.0f} s)", flush=True)
            if isinstance(r, tuple):
                import json
                json.dump(dict(sets=L.S, F=r[0], D=r[1], general=GENERAL),
                          open(f"nodesc_{'general' if GENERAL else 'maximal'}_{name.replace(' ', '')}_{L.n}.json", 'w'))
            continue
        b, how, wit = maximum(L, kmax, secs)
        print(f"{name}: |L| = {L.n}, height {L.height}, max existential minimum {b} ({how})", flush=True)
        if wit and fam == 'pencil':
            import json
            json.dump(dict(sets=L.S, F=wit[0], D=wit[1], exist_min=b, general=GENERAL),
                      open(f"exist_witness_pencil{sys.argv[2]}{'_general' if GENERAL else ''}.json", 'w'))
