"""Exact maximum term-d run length of a fixed finite lattice (log §34.3z¹³³).

Same encoding as response_sat.py (f, d, fle, t, b, r, stuck/non-goal) with the stage update of term_rule.term1_all:
  B[m,a] ⟺ t[m,a] ∨ r[m,a];   C[m,c] ⟺ B[m,c] ∨ ∃ a, b: B[m,a] ∧ B[m,b] ∧ (F(a,b) = c ∨ a ∨ b = c);
  cand[m,x,y,s] ⟺ C[m,s] ∧ F(x,y) ≤ s   (y ≰ s static);   mx ⟺ cand[s] ∧ ∀ s' > s ¬cand[s'];
  N[m,s] ⟺ ∃ x, y: b[m,x,y] ∧ mx[m,x,y,s];   t[m+1] = meet closure of t[m] ∪ N[m].
Every SAT model is decoded and re-simulated with term_rule.term_run.
  python3 term_sat.py (pencil K | linear K SEED COUNT | chain N)   [depth=D]   (suffix _m: close under meets too)
"""
import sys, itertools, time, random
import separator_stages as ss
from response_sat import Enc
from term_rule import term_run

class TermEnc(Enc):
    meets = False
    depth = 1
    def __init__(self, L, k, depth=1, meets=False):
        self.depth = depth; self.meets = meets; super().__init__(L, k)
    def build(self):
        L, n, k = self.L, self.n, self.k; le = L.le; bot, top = L.bot, L.top
        f = lambda x, y, v: self.v('f', x, y, v); d = lambda v: self.v('d', v)
        for x in range(n):
            for y in range(n):
                lits = [f(x, y, v) for v in range(n)]; self.cl(lits)
                for a, b in itertools.combinations(lits, 2): self.cl([-a, -b])
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
        fle = lambda x, y, s: self.v('fle', x, y, s)
        for x in range(n):
            for y in range(n):
                for s in range(n): self.iff_or(fle(x, y, s), [f(x, y, v) for v in range(n) if le[v][s]])
        t = lambda m, e: self.v('t', m, e)
        for e in range(n): self.cl([t(0, e)] if e in (bot, top) else [-t(0, e)])
        for m in range(k + 1):
            b = lambda x, y: self.v('b', m, x, y)
            for x in range(n):
                for y in range(n):
                    if le[y][x]: self.cl([-b(x, y)]); continue
                    seps = []
                    for s in range(n):
                        if le[y][s]: continue
                        a = self.v('sep', m, x, y, s); self.iff_and(a, [t(m, s), fle(x, y, s)]); seps.append(a)
                    anysep = self.v('anysep', m, x, y); self.iff_or(anysep, seps)
                    self.iff_and(b(x, y), [t(m, x), d(x), t(m, y), -d(y), -anysep])
            if m == k:
                break
            for v_ in range(n):
                terms = []
                for x in range(n):
                    for y in range(n):
                        a = self.v('bf', m, x, y, v_); self.iff_and(a, [b(x, y), f(x, y, v_)]); terms.append(a)
                self.iff_or(self.v('r', m, v_), terms)
            stuck = []
            for x in range(n):
                for y in range(n):
                    yle = self.v('yle', x, y); self.iff_or(yle, [f(x, y, v_) for v_ in range(n) if le[y][v_]])
                    a = self.v('stk', m, x, y); self.iff_and(a, [b(x, y), yle]); stuck.append(a)
            self.cl([b(x, y) for x in range(n) for y in range(n)])
            for a in stuck: self.cl([-a])
            B = lambda a: self.v('B', m, a)
            for a in range(n): self.iff_or(B(a), [t(m, a), self.v('r', m, a)])
            prev = B
            for j in range(self.depth):
                pair = {}
                for a in range(n):
                    for c in range(n):
                        p = self.v('pB', m, j, a, c); self.iff_and(p, [prev(a), prev(c)]); pair[(a, c)] = p
                for c in range(n):
                    lits = [prev(c)] + [pair[(a, a2)] for a in range(n) for a2 in range(n)
                                        if L.join[a][a2] == c or (self.meets and L.meet[a][a2] == c)]
                    for a in range(n):
                        for a2 in range(n):
                            w = self.v('pf', m, j, a, a2, c); self.iff_and(w, [pair[(a, a2)], f(a, a2, c)]); lits.append(w)
                    self.iff_or(self.v('C', m, j, c), lits)
                prev = (lambda jj: (lambda c: self.v('C', m, jj, c)))(j)
            C = prev
            Nlits = {s: [] for s in range(n)}
            for x in range(n):
                for y in range(n):
                    if le[y][x]: continue
                    cand = {}
                    for s in range(n):
                        if le[y][s]: continue
                        c_ = self.v('cand', m, x, y, s); self.iff_and(c_, [C(s), fle(x, y, s)]); cand[s] = c_
                    for s in cand:
                        mx = self.v('mx', m, x, y, s)
                        self.iff_and(mx, [cand[s]] + [-cand[s2] for s2 in cand if s2 != s and le[s][s2]])
                        w = self.v('bmx', m, x, y, s); self.iff_and(w, [b(x, y), mx]); Nlits[s].append(w)
            for s in range(n): self.iff_or(self.v('N', m, s), Nlits[s])
            for e in range(n):
                if e == top: self.cl([t(m + 1, e)]); continue
                conds = []
                for z in range(n):
                    if z == e or not le[e][z]: continue
                    wit = []
                    for a_ in range(n):
                        if le[e][a_] and not le[z][a_]:
                            w = self.v('A', m, a_); self.iff_or(w, [t(m, a_), self.v('N', m, a_)]); wit.append(w)
                    c = self.v('ex', m, e, z); self.iff_or(c, wit); conds.append(c)
                self.iff_and(t(m + 1, e), conds)

def decode(E):
    L = E.L; n = L.n; mdl = set(x for x in E.S.get_model() if x > 0)
    F = [[next(v for v in range(n) if E.vars[('f', x, y, v)] in mdl) for y in range(n)] for x in range(n)]
    return F, [E.vars[('d', v)] in mdl for v in range(n)]

def max_length(L, kmax=12, budget=None, meets=False, depth=1):
    t0 = time.time(); best = 0; witness = None
    for k in range(1, kmax + 1):
        E = TermEnc(L, k, depth, meets); r = E.S.solve()
        if r:
            F, D = decode(E)
            assert len(term_run(L, F, D, 'all', meets=meets, depth=depth)[1]) >= k, "model does not reproduce"
            witness = (F, D)
        E.S.delete()
        if not r: return best, round(time.time() - t0, 1), witness
        best = k
        if budget and time.time() - t0 > budget: return best, None, witness
    return best, None, witness

def lat_of(sets, k):
    return ss.Lat(sorted({sum(1 << i for i in s) for s in sets}, key=lambda x: (bin(x).count('1'), x)))

if __name__ == '__main__':
    fam = sys.argv[1]; M = fam.endswith('_m'); fam = fam.removesuffix('_m')
    DEP = int(sys.argv[-1].removeprefix('depth=')) if sys.argv[-1].startswith('depth=') else 1
    if DEP != 1: sys.argv.pop()
    rule = f"term{DEP}{'m' if M else ''}_all"
    if fam == 'chain':
        N = int(sys.argv[2]); L = ss.Lat([(1 << i) - 1 for i in range(N)])
        print(f"chain {N}: height {L.height}, max {rule} length {max_length(L, meets=M, depth=DEP)[:2]}", flush=True)
    elif fam == 'pencil':
        from pencil_family import family
        L = family(int(sys.argv[2]))[0]
        print(f"near-pencil on {sys.argv[2]} points: |L| = {L.n}, height {L.height}, max {rule} length (k, s) = "
              f"{max_length(L, budget=500, meets=M, depth=DEP)[:2]}", flush=True)
    elif fam == 'linear':
        from finite_landmarks import linear_space
        k = int(sys.argv[2]); rng = random.Random(int(sys.argv[3]))
        for _ in range(int(sys.argv[4])):
            L = lat_of(linear_space(k, rng), k)
            if L.height != 3: continue
            print(f"linear space on {k} points: |L| = {L.n}, height {L.height}, max {rule} length (k, s) = "
                  f"{max_length(L, budget=500, meets=M, depth=DEP)[:2]}", flush=True)
