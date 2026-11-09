"""Exact maximum run length of the lookahead term rule (look_rule.look_run, meets on) on a fixed lattice (§34.3z¹³⁴).

TermEnc (term_sat.py) with the selection replaced: for stage m and candidate s,
  ts[m,s,e] ⟺ e ∈ meetClose(T_m ∪ {s});  bs[m,s,x,y] ⟺ (x, y) bad at that stage;
  good[m,s] ⟺ ∀ x, y: bs[m,s,x,y] → b[m,x,y];   chosen ⟺ mx ∧ (good ∨ no C-maximal separator of the pair is good).
Every model is decoded and re-simulated with look_run.
  python3 look_sat.py (pencil K | linear K SEED COUNT | chain N) [depth=D]
"""
import sys, time, random
import separator_stages as ss
from term_sat import TermEnc, decode, lat_of
from look_rule import look_run

class LookEnc(TermEnc):
    def __init__(self, L, k, depth=1, meets=True):
        self.goodc = {}; self.exT = {}; super().__init__(L, k, depth, meets)
    def ex_T(self, m, e, z):
        key = (m, e, z)
        if key not in self.exT:
            L = self.L; v = self.v('exT', m, e, z)
            self.iff_or(v, [self.v('t', m, a) for a in range(self.n) if L.le[e][a] and not L.le[z][a]]); self.exT[key] = v
        return self.exT[key]
    def good(self, m, s):
        if (m, s) in self.goodc: return self.goodc[(m, s)]
        L, n = self.L, self.n; le = L.le; ts = {}
        for e in range(n):
            if e == L.top or e == s: ts[e] = None; continue           # None = true
            conds = [self.ex_T(m, e, z) for z in range(n) if z != e and le[e][z] and not (le[e][s] and not le[z][s])]
            v = self.v('ts', m, s, e); self.iff_and(v, conds); ts[e] = v
        lit = lambda e: [] if ts[e] is None else [ts[e]]
        viol = []
        for x in range(n):
            for y in range(n):
                if le[y][x]: continue
                seps = []
                for u in range(n):
                    if le[y][u]: continue
                    a = self.v('sepS', m, s, x, y, u); self.iff_and(a, lit(u) + [self.v('fle', x, y, u)]); seps.append(a)
                anys = self.v('anysepS', m, s, x, y); self.iff_or(anys, seps)
                bs = self.v('bs', m, s, x, y)
                self.iff_and(bs, lit(x) + lit(y) + [self.v('d', x), -self.v('d', y), -anys])
                w = self.v('newbad', m, s, x, y); self.iff_and(w, [bs, -self.v('b', m, x, y)]); viol.append(w)
        g = self.v('good', m, s); self.iff_and(g, [-w for w in viol]); self.goodc[(m, s)] = g
        return g
    def select(self, m, x, y, mxd):
        mg = {}
        for s, mx in mxd.items():
            a = self.v('mg', m, x, y, s); self.iff_and(a, [mx, self.good(m, s)]); mg[s] = a
        anyg = self.v('anyg', m, x, y); self.iff_or(anyg, list(mg.values()))
        out = {}
        for s, mx in mxd.items():
            gn = self.v('gn', m, x, y, s); self.iff_or(gn, [self.good(m, s), -anyg])
            ch = self.v('ch', m, x, y, s); self.iff_and(ch, [mx, gn]); out[s] = ch
        return out

def max_length(L, kmax=14, budget=None, depth=1):
    t0 = time.time(); best = 0
    for k in range(1, kmax + 1):
        E = LookEnc(L, k, depth); r = E.S.solve()
        if r:
            F, D = decode(E); got = look_run(L, F, D, depth)
            assert got is not None and got >= k, f"model does not reproduce ({got} < {k})"
        E.S.delete()
        if not r: return best, round(time.time() - t0, 1)
        best = k
        if budget and time.time() - t0 > budget: return best, None
    return best, None

if __name__ == '__main__':
    args = sys.argv[1:]; DEP = 1
    if args[-1].startswith('depth='): DEP = int(args.pop().removeprefix('depth='))
    fam = args[0]
    if fam == 'chain':
        L = ss.Lat([(1 << i) - 1 for i in range(int(args[1]))])
        print(f"chain {args[1]}: height {L.height}, max look{DEP} length {max_length(L, depth=DEP)}", flush=True)
    elif fam == 'pencil':
        import pencil_family
        L = pencil_family.family(int(args[1]))[0]
        print(f"near-pencil on {args[1]} points: |L| = {L.n}, height {L.height}, max look{DEP} length (k, s) = "
              f"{max_length(L, budget=500, depth=DEP)}", flush=True)
    elif fam == 'linear':
        from finite_landmarks import linear_space
        k = int(args[1]); rng = random.Random(int(args[2]))
        for _ in range(int(args[3])):
            L = lat_of(linear_space(k, rng), k)
            if L.height != 3: continue
            print(f"linear space on {k} points: |L| = {L.n}, height {L.height}, max look{DEP} length (k, s) = "
                  f"{max_length(L, budget=500, depth=DEP)}", flush=True)
