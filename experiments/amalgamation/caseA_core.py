"""Minimal cores of statement (A) of §34.3z²⁴¹ (log §34.3z²⁴²), m-free.  Hard: F monotone, the ⊥-descent from ⊤ with its
atom c, a(⊥) = ⊥, c < a(c), F(⊥, a(c)) ≠ c.  Guards: T1(z) [z ∉ R_1, h(z) > 1], T2(z) [z ∉ R_2, h(z) > 2].
  python3 caseA_core.py (sweep N MAX | closure K M SEED CNT) [limit=K]
"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
LIM = next((int(a[6:]) for a in sys.argv if a.startswith('limit=')), 10)
args = [a for a in sys.argv[1:] if not a.startswith('limit=') and a not in ('catom', 'as2')]
C = collections.Counter(); shown = 0
for L in lattices(args):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top; jn = L.join
    if L.height < 3: continue
    nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
    E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
    A_ = lambda x, g: E.v('A', x, g); NO = L.height + 1
    D = lambda i, z: E.v('D', i, z)
    for z in range(n): add([D(0, z)] if z == top else [-D(0, z)])
    for i in range(NO):
        for z in range(n):
            lits = []
            for v in range(n): o = E.v('Ds', i, v, z); E.iff_and(o, [D(i, v), f(bot, v, z)]); lits.append(o)
            E.iff_or(D(i + 1, z), lits)
    atoms = [c for c in range(n) if h[c] == 1]
    At = {c: E.v('datom', c) for c in atoms}
    for c in atoms: E.iff_or(At[c], [D(i, c) for i in range(NO + 1)])
    add(list(At.values())); add([A_(bot, bot)])
    for c in atoms:
        add([-At[c]] + [A_(c, g) for g in range(n) if le[c][g] and g != c])
        for g in range(n):
            if le[c][g] and g != c: add([-At[c], -A_(c, g), -f(bot, g, c)])
            if 'catom' in sys.argv and le[c][g] and g != c: add([-At[c], -A_(c, g)] + [f(bot, g, c2) for c2 in atoms if c2 != c])   # c' = F(⊥, a(c)) an atom ≠ c
            if 'as2' in sys.argv and h[g] > 2: add([-At[c], -A_(c, g)])                    # h(a(c)) ≤ 2 (hard)
    guards = {}
    def guard(tag, clauses):
        s_ = E.v('g', *tag); guards[s_] = tag
        for c_ in clauses: add([-s_] + c_)
    for z in range(n):
        if h[z] > 1: guard(('T1', z), [[-r(1, z)]])
        if h[z] > 2: guard(('T2', z), [[-r(2, z)]])
    if not E.S.solve(): C['inconsistent'] += 1; E.S.delete(); continue
    if E.S.solve(assumptions=list(guards)): C['(A) fails'] += 1; E.S.delete(); continue
    core = E.S.get_core() or list(guards); i = 0
    while i < len(core):
        t = core[:i] + core[i + 1:]
        if not E.S.solve(assumptions=t): core = t
        else: i += 1
    tags = sorted(guards[s_] for s_ in core)
    C['cores'] += 1; C[('shape', tuple(sorted(collections.Counter(t[0] for t in tags).items())))] += 1
    for t in tags: C[(t[0], 'h', h[t[1]], 'join of two atoms' if any(jn[a][b] == t[1] for a in atoms for b in atoms if a != b) else 'not an atom join')] += 1
    if shown < LIM: shown += 1; print(f'|L|={n}:', [nm(i) for i in range(n)], 'core', ' '.join(t[0] + nm(t[1]) for t in tags), flush=True)
    C[('T classes', tuple(sorted((t[0], h[t[1]]) for t in tags)))] += 1
    E.S.delete()
for k_, v_ in sorted(C.items(), key=lambda kv: -kv[1])[:25]: print(k_, v_)
