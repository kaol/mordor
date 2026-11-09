"""Exact maximum response-run length of a fixed finite lattice (log §34.3z¹³²).

For a lattice L (closure system), SAT (CaDiCaL via PySAT) decides whether some monotone F : L × L → L and some cut D
(⊥ ∈ D, ⊤ ∉ D, down-set) give a response run (Lean `ResponseRun.respRun`) with at least k non-goal stages.
Variables: f[x,y,v] (F(x, y) = v, one-hot), d[v], t[n,e] (e ∈ T_n), b[n,x,y] (bad), r[n,v] (v a response of a bad pair).
Exact stage semantics:
  b[n,x,y] ⟺ t[n,x] ∧ d[x] ∧ t[n,y] ∧ ¬d[y] ∧ ¬∃ s (t[n,s] ∧ F(x,y) ≤ s ∧ y ≰ s);
  r[n,v] ⟺ ∃ x, y: b[n,x,y] ∧ f[x,y,v];
  t[n+1,e] ⟺ e = ⊤ ∨ ∀ z > e ∃ a: (t[n,a] ∨ r[n,a]) ∧ e ≤ a ∧ z ≰ a     (e is the meet of the members above it);
  stage n non-goal ⟺ ∃ bad pair ∧ no bad pair with y ≤ F(x, y).
Maximum = largest k with stages 0..k−1 non-goal (SAT), found by increasing k until UNSAT.
  python3 response_sat.py family ARGS      (family: linear K SEED COUNT | closure K M SEED COUNT | chain N | pencil K)
"""
import sys, itertools, time
from pysat.solvers import Cadical153
from pysat.card import CardEnc
import separator_stages as ss

class Enc:
    def __init__(self, L, k):
        self.L = L; self.k = k; self.n = L.n; self.nv = 0; self.S = Cadical153(); self.vars = {}
        self.build()
    def v(self, *key):
        if key not in self.vars: self.nv += 1; self.vars[key] = self.nv
        return self.vars[key]
    def cl(self, c): self.S.add_clause(c)
    def iff_and(self, out, lits):
        for l in lits: self.cl([-out, l])
        self.cl([out] + [-l for l in lits])
    def iff_or(self, out, lits):
        for l in lits: self.cl([out, -l])
        self.cl([-out] + list(lits))
    def build(self):
        L, n, k = self.L, self.n, self.k; le = L.le; bot, top = L.bot, L.top
        f = lambda x, y, v: self.v('f', x, y, v); d = lambda v: self.v('d', v)
        for x in range(n):
            for y in range(n):
                lits = [f(x, y, v) for v in range(n)]
                self.cl(lits)
                for a, b in itertools.combinations(lits, 2): self.cl([-a, -b])
        # monotone along covers
        for x in range(n):
            for x2 in L.covers_up[x]:
                for y in range(n):
                    for v in range(n): self.cl([-f(x, y, v)] + [f(x2, y, w) for w in range(n) if le[v][w]])
        for y in range(n):
            for y2 in L.covers_up[y]:
                for x in range(n):
                    for v in range(n): self.cl([-f(x, y, v)] + [f(x, y2, w) for w in range(n) if le[v][w]])
        self.cl([d(bot)]); self.cl([-d(top)])
        for a in range(n):
            for b in L.covers_up[a]: self.cl([-d(b), d(a)])
        # F(x,y) ≤ s
        fle = lambda x, y, s: self.v('fle', x, y, s)
        for x in range(n):
            for y in range(n):
                for s in range(n): self.iff_or(fle(x, y, s), [f(x, y, v) for v in range(n) if le[v][s]])
        t = lambda m, e: self.v('t', m, e)
        for e in range(n): self.cl([t(0, e)] if e in (bot, top) else [-t(0, e)])
        for m in range(k + 1):
            sep = {}
            for x in range(n):
                for y in range(n):
                    if le[y][x]: self.cl([-self.v('b', m, x, y)]); continue
                    seps = []
                    for s in range(n):
                        if le[y][s]: continue
                        a = self.v('sep', m, x, y, s); self.iff_and(a, [t(m, s), fle(x, y, s)]); seps.append(a)
                    anysep = self.v('anysep', m, x, y); self.iff_or(anysep, seps)
                    self.iff_and(self.v('b', m, x, y), [t(m, x), d(x), t(m, y), -d(y), -anysep])
            for v_ in range(n):
                terms = []
                for x in range(n):
                    for y in range(n):
                        a = self.v('bf', m, x, y, v_); self.iff_and(a, [self.v('b', m, x, y), f(x, y, v_)]); terms.append(a)
                self.iff_or(self.v('r', m, v_), terms)
            # stuck / non-goal
            stuck = []
            # stuck pair: bad and y ≤ F(x,y)  (y ≤ F ⟺ OR_{v ≥ y} f)
            for x in range(n):
                for y in range(n):
                    yle = self.v('yle', x, y); self.iff_or(yle, [f(x, y, v_) for v_ in range(n) if le[y][v_]])
                    a = self.v('stk', m, x, y); self.iff_and(a, [self.v('b', m, x, y), yle]); stuck.append(a)
            if m < k:
                self.cl([self.v('b', m, x, y) for x in range(n) for y in range(n)])      # some bad pair
                for a in stuck: self.cl([-a])                                            # none stuck
                # next stage
                for e in range(n):
                    if e == top: self.cl([t(m + 1, e)]); continue
                    conds = []
                    for z in range(n):
                        if z == e or not le[e][z]: continue
                        wit = []
                        for a_ in range(n):
                            if le[e][a_] and not le[z][a_]:
                                w = self.v('A', m, a_); self.iff_or(w, [t(m, a_), self.v('r', m, a_)]); wit.append(w)
                        c = self.v('ex', m, e, z); self.iff_or(c, wit); conds.append(c)
                    self.iff_and(t(m + 1, e), conds)

def decode(E):
    L = E.L; n = L.n; m = set(x for x in E.S.get_model() if x > 0)
    F = [[next(v for v in range(n) if E.vars[('f', x, y, v)] in m) for y in range(n)] for x in range(n)]
    D = [E.vars[('d', v)] in m for v in range(n)]
    return F, D

def verify(L, F, D, k):
    """Independent check with the reference simulator (general_sep.response_run)."""
    from general_sep import response_run
    assert all(L.le[F[a][b]][F[a2][b2]] for a in range(L.n) for a2 in range(L.n) for b in range(L.n) for b2 in range(L.n)
               if L.le[a][a2] and L.le[b][b2]), "F not monotone"
    assert D[L.bot] and not D[L.top] and all(D[a] for a in range(L.n) for b in range(L.n) if L.le[a][b] and D[b])
    return len(response_run(L, F, D)[1]) >= k

def max_length(L, kmax=12, budget=None):
    t0 = time.time(); best = 0
    for k in range(1, kmax + 1):
        E = Enc(L, k); r = E.S.solve()
        if r:
            F, D = decode(E)
            assert verify(L, F, D, k), "SAT model does not reproduce the run length"
        E.S.delete()
        if not r: return best, time.time() - t0
        best = k
        if budget and time.time() - t0 > budget: return best, None
    return best, time.time() - t0

if __name__ == '__main__':
    fam = sys.argv[1]
    if fam == 'chain':
        N = int(sys.argv[2]); L = ss.Lat([(1 << i) - 1 for i in range(N)])
        print(f"chain {N}: height {L.height}, max response-run length {max_length(L)}")
    elif fam == 'pencil':
        # near-pencil on k points: lines {p, q_i} (p = point 0) and the long line {q_1, ..., q_{k-1}}; height 3
        k = int(sys.argv[2])
        sets = {0, (1 << k) - 1} | {1 << i for i in range(k)} | {1 | (1 << i) for i in range(1, k)} | {((1 << k) - 1) ^ 1}
        L = ss.Lat(sorted(sets, key=lambda x: (bin(x).count('1'), x)))
        print(f"near-pencil on {k} points: |L| = {L.n}, height {L.height}, max response-run length (k, s) = "
              f"{max_length(L, kmax=4 * k, budget=560)}", flush=True)
    elif fam == 'linear':
        import random
        from finite_landmarks import linear_space
        rng = random.Random(int(sys.argv[3])); k = int(sys.argv[2])
        for _ in range(int(sys.argv[4])):
            sets = linear_space(k, rng)
            L = ss.Lat(sorted({int(''.join('1' if i in s else '0' for i in reversed(range(k))), 2) for s in sets},
                              key=lambda x: (bin(x).count('1'), x)))
            if L.height != 3: continue
            print(f"linear space on {k} points: |L| = {L.n}, height {L.height}, max response-run length (k, s) = "
                  f"{max_length(L, budget=500)}", flush=True)
    elif fam == 'closure':
        import random
        k, m, seed, cnt = (int(x) for x in sys.argv[2:6]); rng = random.Random(seed)
        for _ in range(cnt):
            L = ss.Lat(ss.closure_system(k, m, rng))
            print(f"closure system on {k} points: |L| = {L.n}, height {L.height}, max response-run length (k, s) = "
                  f"{max_length(L, budget=500)}", flush=True)
