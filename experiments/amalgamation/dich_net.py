"""Dichotomy(k) and its configuration network (log §34.3z²²⁶).  rank(m) = K = k + 1.

Hypotheses (hard unless guarded): F monotone; m ∈ R_K \\ R_{K−1}; ¬IC(m); ⊤ ∉ R_{K+1}; R_K, R_{K−1} tight; a lower feeder
p ⋖ m, p ∈ R_{K−1}, F(p, m) ≤ p; nopostlayer NPL(x): h(x) = k, x ∈ R_k ⟹ x ≰ F(x, x).
Dichotomy(k) is violated iff additionally no configuration (p, c) has a certificate:
  CFG(p, c): p ∈ R_{k−1}, h(p) = k − 1, c ∈ R_k \\ R_{k−1}, h(c) = k, p < c, F(p, c) = p, and no v ≱ m with F(p, v) = c
  has y ∈ (c, v] with F(c, y) ≤ y ∨ y ≤ F(c, y).
Modes:
  test  — is Dichotomy(k) violated (SAT)?  Models are re-checked in Python.
  core  — every hypothesis instance and every CFG(p, c) guarded; deletion-minimal core; dump to JSON lines.
  python3 dich_net.py k MODE (sweep N MAX | closure K M SEED CNT) [out=FILE] [minlevel] [nonpl]
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from rstages import stages
k = int(sys.argv[1]); MODE = sys.argv[2]; K = k + 1
OUT = next((a[4:] for a in sys.argv if a.startswith('out=')), None); MINLEVEL = 'minlevel' in sys.argv; NONPL = 'nonpl' in sys.argv
args = [a for a in sys.argv[3:] if not a.startswith('out=') and a not in ('minlevel', 'nonpl')]
C = collections.Counter(); best = None; outf = open(OUT, 'w') if OUT else None

def py_violated(L, F, m):
    n = L.n; le = L.le; h = L.rank; st = stages(L, F); inR = lambda x, j: st[x] is not None and st[x] <= j
    if not NONPL and any(h[x] == k and inR(x, k) and le[x][F[x][x]] for x in range(n)): return False
    for p in range(n):
        for c in range(n):
            if not (h[p] == k - 1 and inR(p, k - 1) and h[c] == k and inR(c, k) and not inR(c, k - 1) and le[p][c] and p != c and F[p][c] == p): continue
            for v in range(n):
                if le[c][v] and v != c and not le[m][v] and F[p][v] == c and (not MINLEVEL or h[v] == K):
                    if any(le[c][y] and y != c and le[y][v] and (not MINLEVEL or y == v) and (le[F[c][y]][y] or le[y][F[c][y]]) for y in range(n)): return False
    return True

for L in lattices(args):
    n = L.n; le = L.le; h = L.rank
    nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
    for m in range(n):
        if h[m] != K or L.height <= K: continue
        feeders = [p for p in L.covers_dn[m] if h[p] == K - 1]
        if not feeders: continue
        E = Enc(L, K + 1); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z)
        E.S.add_clause([r(K, m)]); E.S.add_clause([-r(K - 1, m)])
        guards = {}
        def guard(tag, clauses):
            if MODE != 'core':
                for c_ in clauses: E.S.add_clause(c_)
                return
            s_ = E.v('g', *tag); guards[s_] = tag
            for c_ in clauses: E.S.add_clause([-s_] + c_)
        guard(('NOIC',), [[-ic(m)]]); guard(('TOP',), [[-r(K + 1, L.top)]])
        low = []
        for p in feeders: o = E.v('low', p); E.iff_and(o, [r(K - 1, p), fle(p, m, p)]); low.append(o)
        guard(('FEED',), [low])
        for z in range(n):
            if h[z] > K: guard(('TK', z), [[-r(K, z)]])
            if h[z] > K - 1: guard(('TK1', z), [[-r(K - 1, z)]])
            if h[z] == k and not NONPL: guard(('NPL', z), [[-r(k, z), -yle(z, z)]])
        for p in range(n):
            if h[p] != k - 1: continue
            for c in range(n):
                if h[c] != k or not le[p][c]: continue
                cl = []
                for v in range(n):
                    if not (le[c][v] and v != c and not le[m][v]): continue
                    if MINLEVEL and h[v] != K: continue          # 'minlevel': point certificates y = v of height k + 1 only
                    for y in range(n):
                        if le[c][y] and y != c and le[y][v] and (not MINLEVEL or y == v):
                            base = [-r(k - 1, p), -r(k, c), r(k - 1, c), -f(p, c, p), -f(p, v, c)]
                            cl += [base + [-fle(c, y, y)], base + [-yle(c, y)]]
                if cl: guard(('CFG', p, c), cl)
        if MODE == 'test':
            if E.S.solve():
                F = E.decode(); assert py_violated(L, F, m)
                C['violated'] += 1
                if best is None or n < best[0]: best = (n, dict(sets=L.S, F=F, m=m))
            else: C['holds'] += 1
            E.S.delete(); continue
        if not E.S.solve(): C['inconsistent without guards'] += 1; E.S.delete(); continue
        if E.S.solve(assumptions=list(guards)): C['violated'] += 1; E.S.delete(); continue
        core = E.S.get_core() or list(guards); i = 0
        while i < len(core):
            t = core[:i] + core[i + 1:]
            if not E.S.solve(assumptions=t): core = t
            else: i += 1
        tags = sorted(guards[s_] for s_ in core)
        C['cores'] += 1; C[('has CFG', any(t[0] == 'CFG' for t in tags))] += 1
        allcfg = sorted(t for t in guards.values() if t[0] == 'CFG')
        if outf: outf.write(json.dumps(dict(sets=L.S, m=m, core=tags, allcfg=allcfg)) + '\n')
        E.S.delete()
print(f'k={k} {MODE}', dict(C), 'smallest violation', best[0] if best else None)
if best: json.dump(best[1], open(f'dich{k}_violation_min{best[0]}.json', 'w'))
