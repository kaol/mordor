"""The atom case of (A) (log §34.3z²⁴³): c' = F(⊥, a(c)) an atom ≠ c.  For each lattice where the hard constraints
alone are consistent, compute a minimal core over T1/T2 guards.  For each T2 instance g in it, take a near-model
(the other instances of the core only) and label g relative to that model.
  python3 caseA_atom_near.py (sweep N MAX | closure K M SEED CNT)
"""
import sys, collections
sys.path.insert(0, '../separation')
from amalg_sat import Enc
from tight_probe import helpers, lattices
from rstages import stages, a_of, b_of
C = collections.Counter(); shown = 0
def build(L, drop=None, guarded=False, keep=None):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top
    E = Enc(L, 3); fle, yle, ic = helpers(E, L); f = lambda a, b, u: E.v('f', a, b, u); r = lambda j, z: E.v('r', j, z); add = E.S.add_clause
    A_ = lambda x, g: E.v('A', x, g); NO = L.height + 1; D = lambda i, z: E.v('D', i, z)
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
            if le[c][g] and g != c: add([-At[c], -A_(c, g)] + [f(bot, g, c2) for c2 in atoms if c2 != c])
    guards = {}
    for z in range(n):
        for tag, j, cond in (('T1', 1, h[z] > 1), ('T2', 2, h[z] > 2)):
            if not cond or (tag, z) == drop or (keep is not None and (tag, z) not in keep): continue
            if guarded: s_ = E.v('g', tag, z); guards[s_] = (tag, z); add([-s_, -r(j, z)])
            else: add([-r(j, z)])
    return E, guards
for L in lattices(sys.argv[1:]):
    n = L.n; le = L.le; h = L.rank; bot = h.index(0); top = L.top; jn = L.join; mt = L.meet
    if L.height < 3: continue
    nm = lambda i: '{' + ''.join(str(j) for j in range(8) if L.S[i] >> j & 1) + '}'
    E, guards = build(L, guarded=True)
    if not E.S.solve(): C['hard-inconsistent'] += 1; E.S.delete(); continue
    if E.S.solve(assumptions=list(guards)): C['(A) atom case fails!'] += 1; E.S.delete(); continue
    core = E.S.get_core() or list(guards); i = 0
    while i < len(core):
        t = core[:i] + core[i + 1:]
        if not E.S.solve(assumptions=t): core = t
        else: i += 1
    tags = sorted(guards[s_] for s_ in core); E.S.delete(); C['cores'] += 1
    for tg in tags:
        if tg[0] != 'T2': C[('T1 in core',)] += 1; continue
        g = tg[1]; E2, _ = build(L, drop=tg, keep=set(tags))
        if not E2.S.solve(): C[('near-model UNSAT',)] += 1; E2.S.delete(); continue
        F = E2.decode(); E2.S.delete(); st = stages(L, F)
        v = top; seq = []
        while v not in seq: seq.append(v); v = F[bot][v]
        c = next(x for x in seq if h[x] == 1); ac = a_of(L, F, c); c2 = F[bot][ac]
        e = next(i for i, x in enumerate(seq) if le[x][ac]); dprev = seq[e - 1] if e >= 1 else None
        lab = ('g = a(c)' if g == ac else 'g = d_{e−1} ∨ a(c)' if dprev is not None and jn[dprev][ac] == g else 'g = d_{e−1}' if g == dprev else
               'g ≥ a(c)' if le[ac][g] else 'g ≥ d_{e−1}' if dprev is not None and le[dprev][g] else 'other')
        rts = sorted(set(('a' if le[g][a_of(L, F, x)] else 'b') + ':' + ('⊥' if x == bot else 'c' if x == c else "c'" if x == c2 else f'h{h[x]}')
                         for x in range(n) if st[x] is not None and st[x] <= 1 and (le[g][a_of(L, F, x)] or any(le[g][y] and b_of(L, F, y) == x for y in range(n)))))
        C[('label', lab, 'h(a(c))', h[ac], 'routes into R_2', tuple(rts))] += 1
        if shown < 8: shown += 1; print('|L|', n, 'g', nm(g), 'descent', [nm(x) for x in seq], 'c', nm(c), 'a(c)', nm(ac), "c'", nm(c2), 'label', lab, 'routes', rts, flush=True)
for k_, v_ in sorted(C.items(), key=lambda kv: -kv[1])[:20]: print(k_, v_)
