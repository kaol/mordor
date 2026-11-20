"""Near-models of (C′) (log §34.3z²⁴⁴; derived from caseA_atom_near.py): c ≰ a(c) and the row-c descent misses c.
Original header: the atom case of (A): c' = F(⊥, a(c)) an atom ≠ c.  For each lattice where the hard constraints
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
    add(list(At.values()))
    for c in atoms:
        for g in range(n):
            if le[c][g]: add([-At[c], -A_(c, g)])
        UC = lambda k, z: E.v('UC', c, k, z)
        for z in range(n): add([UC(0, z)] if z == top else [-UC(0, z)])
        for k in range(NO):
            for z in range(n):
                lits = []
                for v in range(n): o = E.v('UCs', c, k, v, z); E.iff_and(o, [UC(k, v), f(c, v, z)]); lits.append(o)
                E.iff_or(UC(k + 1, z), lits)
        for k in range(NO + 1): add([-At[c], -UC(k, c)])
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
        g = tg[1]; E2, _ = build(L, drop=tg, keep=set(tags))
        if not E2.S.solve(): C[('near-model UNSAT',)] += 1; E2.S.delete(); continue
        F = E2.decode(); E2.S.delete(); st = stages(L, F)
        v = top; ds = []
        while v not in ds: ds.append(v); v = F[bot][v]
        c = next(x for x in ds if h[x] == 1); p = ds[ds.index(c) - 1]
        v = top; us = []
        while v not in us: us.append(v); v = F[c][v]
        uK = [u for u in us if le[c][u]][-1]
        z = uK
        while jn[c][F[c][z]] != z: z = jn[c][F[c][z]]
        q = F[c][z]; ac = a_of(L, F, c)
        lab = ('g = z*' if g == z else 'g = u_K' if g == uK else 'g = p' if g == p else 'g = c ∨ p' if g == jn[c][p] else 'g = z* ∨ p' if g == jn[z][p] else
               'g = q' if g == q else 'g ≥ z*' if le[z][g] else 'g ≥ p' if le[p][g] else 'other')
        C[(tg[0], lab, 'h(g)', h[g], 'h(z*)', h[z], 'F(⊥,z*)=⊥' if F[bot][z] == bot else 'F(⊥,z*)≠⊥')] += 1
        if shown < 10: shown += 1; print(tg[0], '|L|', n, 'g', nm(g), 'd', [nm(x) for x in ds], 'u', [nm(x) for x in us], 'c', nm(c), 'z*', nm(z), 'q', nm(q), 'F(⊥,z*)', nm(F[bot][z]), 'a(c)', nm(ac), 'label', lab, flush=True)
for k_, v_ in sorted(C.items(), key=lambda kv: -kv[1])[:20]: print(k_, v_)
