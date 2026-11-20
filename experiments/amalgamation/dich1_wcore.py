"""Minimal cores of MinH2W (log §34.3z²³⁰), rank(m) = 2.  Hard: F monotone, m ∈ R_2 \\ R_1, m's column orbit (u_N = y*).
Guards: WL [w = F(m, y*) ≰ m], WU [m ≰ w], T2(z) [h(z) > 2 ⟹ z ∉ R_2], X(y) [y not a G-comparable height-2 point].
Flags: routeA / routeB force m's entry into R_2 by the a-route (m ≤ a(x), x ∈ R_1) / the b-route (m ≤ g, b(g) ∈ R_1).
  python3 dich1_wcore.py (sweep N MAX | closure K M SEED CNT) [routeA|routeB] [test] [limit=K]
  'test': no guards (all hypotheses hard); report whether MinH2W fails.
"""
import sys, collections, json
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
LIM = next((int(a[6:]) for a in sys.argv if a.startswith('limit=')), 10)
FL = {a for a in sys.argv if a in ('routeA', 'routeB', 'test')}
args = [a for a in sys.argv[1:] if not a.startswith('limit=') and a not in FL]
C = collections.Counter(); shown = 0; best = None
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top; jn = L.join
    nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
    for m in range(n):
        if h[m] != 2 or L.height <= 2: continue
        E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z)
        A = lambda x, g: E.v('A', x, g); B = lambda y, g: E.v('B', y, g); add = E.S.add_clause
        add([r(2, m)]); add([-r(1, m)])
        if 'routeA' in FL: add([E.v('ra', 1, x, g) for x in range(n) for g in range(n) if le[m][g]])
        if 'routeB' in FL: add([E.v('rb', 1, g, hh) for g in range(n) for hh in range(n) if le[m][g]])
        U = lambda i, z: E.v('U', i, z); NO = L.height + 1
        for z in range(n): add([U(0, z)] if z == top else [-U(0, z)])
        for i in range(NO - 1):
            for z in range(n):
                lits = []
                for v in range(n):
                    for g in range(n):
                        if jn[m][g] == z: o = E.v('Ust', i, v, g); E.iff_and(o, [U(i, v), f(m, v, g)]); lits.append(o)
                E.iff_or(U(i + 1, z), lits)
        N = NO - 1; guards = {}
        def guard(tag, clauses):
            if 'test' in FL:
                for c_ in clauses: add(c_)
                return
            s_ = E.v('g', *tag); guards[s_] = tag
            for c_ in clauses: add([-s_] + c_)
        guard(('WL',), [[-U(N, z), -f(m, z, g)] for z in range(n) for g in range(n) if le[g][m]])
        guard(('WU',), [[-U(N, z), -f(m, z, g)] for z in range(n) for g in range(n) if le[m][g]])
        for z in range(n):
            if h[z] > 2: guard(('T2', z), [[-r(2, z)]])
        for y in range(n):
            if h[y] != 2 or le[m][y]: continue
            cl = []
            for c in L.covers_dn[y]:
                if h[c] == 1: cl += [[-f(bot, y, c), -fle(c, y, y)], [-f(bot, y, c), -yle(c, y)]]
            if cl: guard(('X', y), cl)
        if 'test' in FL:
            if E.S.solve(): C['MinH2W fails'] += 1; best = best or (n, dict(sets=L.S, F=E.decode(), m=m))
            else: C['holds'] += 1
            E.S.delete(); continue
        if not E.S.solve(): C['inconsistent'] += 1; E.S.delete(); continue
        if E.S.solve(assumptions=list(guards)): C['MinH2W fails'] += 1; E.S.delete(); continue
        core = E.S.get_core() or list(guards); i = 0
        while i < len(core):
            t = core[:i] + core[i + 1:]
            if not E.S.solve(assumptions=t): core = t
            else: i += 1
        tags = sorted(guards[s_] for s_ in core)
        C['cores'] += 1
        if not any(t[0] == 'X' for t in tags): C['degenerate'] += 1; E.S.delete(); continue
        Xs = {t[1] for t in tags if t[0] == 'X'}
        C[('shape', tuple(sorted(collections.Counter(t[0] for t in tags).items())))] += 1
        for t in tags:
            if t[0] == 'T2':
                z = t[1]; C[('T2 at', 'z = ⊤' if z == top else ('z = m ∨ y (y ∈ X)' if any(jn[m][y] == z for y in Xs) else ('z ≥ m' if le[m][z] else 'z ∥ m')), 'h', h[z])] += 1
        C[('uses WL', any(t[0] == 'WL' for t in tags), 'uses WU', any(t[0] == 'WU' for t in tags))] += 1
        if shown < LIM: shown += 1; print(f'|L|={n} h={L.height} m={nm(m)}:', ' '.join(t[0] + ''.join(nm(a) for a in t[1:]) for t in tags), flush=True)
        E.S.delete()
print(sorted(FL), dict((k, v) for k, v in C.items() if isinstance(k, str)))
for k_, v_ in sorted(((k, v) for k, v in C.items() if not isinstance(k, str)), key=lambda kv: -kv[1])[:30]: print(k_, v_)
if best: json.dump(best[1], open(f'dich1_wcore_{"_".join(sorted(FL))}_min{best[0]}.json', 'w'))
