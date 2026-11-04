"""Three-petal pairwise-meet / join-anchor incidence at a common contracting column (log §34.3z¹⁰³), z3.

D = ↓g1 ∪ ↓g2 ∪ ↓g3 (pairwise incomparable). Rows: g_i, m_ij = g_i ∧ g_j, g123, c_i = join anchors (c1 = m12 ∨ m13,
c2 = m12 ∨ m23, c3 = m13 ∨ m23), all named as exact glb/lub. Column s ∉ D, F(x, s) ≤ s for every row (all in D), and
the stable normal form s = e12 ∨ e13 ∨ e23 (e_ij = F(m_ij, s)); optional irredundancy s ≰ e_ij ∨ e_ik.
Optional orbits from s: anchor rows t_{i,n+1} = F(c_i, t_{i,n}) and generator rows w_{i,n+1} = F(g_i, w_{i,n}),
t_{i,0} = w_{i,0} = s, first entry into D exactly at the given length; full grid rows × orbit columns, monotone,
no witness on every cell (conditional on membership).
Labels: lab(x) = {k : x ≤ g_k} (empty = outside D). We enumerate the projections of all SAT models to label vectors."""
import itertools, sys
from z3 import *
R3 = (1, 2, 3); P3 = [(1, 2), (1, 3), (2, 3)]

def build(irr=False, tN=None, wN=None, extra=None, drop=(), support=True):
    G = [f"g{i}" for i in R3]; M = [f"m{i}{j}" for i, j in P3]; C = [f"c{i}" for i in R3]
    rows = [x for x in G + M + C + ['g123'] if x not in drop]
    cols = ['s']; t = {}; w = {}
    if tN:
        for i in R3:
            t[i] = ['s'] + [f"t{i}_{n}" for n in range(1, tN[i - 1] + 1)]; cols += t[i][1:]  # length 0: no orbit
    if wN:
        for i in R3:
            w[i] = ['s'] + [f"w{i}_{n}" for n in range(1, wN[i - 1] + 1)]; cols += w[i][1:]
    cell = {(a, b): f"F[{a},{b}]" for a in rows for b in cols}
    E = list(dict.fromkeys(['bot', 'top'] + G + M + C + ['g123'] + rows + cols + list(cell.values()) + [f"J{k}" for k in range(3)]))
    s = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    for a in E:
        s.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            for x in E: s.add(Implies(And(le[a, b], le[b, x]), le[a, x]))
    inD = {a: Or([le[a, g] for g in G]) for a in E}
    for g, h in itertools.permutations(G, 2): s.add(Not(le[g, h]))
    def lub(z, xs): s.add([le[q, z] for q in xs]); s.add([Implies(And([le[q, x] for q in xs]), le[z, x]) for x in E])
    def glb(z, xs): s.add([le[z, q] for q in xs]); s.add([Implies(And([le[x, q] for q in xs]), le[x, z]) for x in E])
    for (i, j), m in zip(P3, M): glb(m, [f"g{i}", f"g{j}"])
    glb('g123', G)
    lub('c1', ['m12', 'm13']); lub('c2', ['m12', 'm23']); lub('c3', ['m13', 'm23'])
    s.add(Not(inD['s']), Not(inD['top']))
    for (a, b), v in cell.items():
        for (a2, b2), v2 in cell.items():
            if (a, b) != (a2, b2): s.add(Implies(And(le[a, a2], le[b, b2]), le[v, v2]))
        s.add(Implies(And(inD[a], Not(inD[b])), And(Not(le[v, a]), Not(le[b, v]))))
    s.add([le[cell[(a, 's')], 's'] for a in rows])
    e = [cell[(m, 's')] for m in M if m not in drop]
    if support: lub('s', e)
    if irr:
        for k, (x, y) in enumerate(itertools.combinations(e, 2)):
            lub(f"J{k}", [x, y]); s.add(Not(le['s', f"J{k}"]))
    eq = lambda a, b: And(le[a, b], le[b, a])
    for orb, row, N in ((t, 'c', tN), (w, 'g', wN)):
        if not N: continue
        for i in R3:
            if N[i - 1] == 0: continue
            for n in range(N[i - 1]):
                s.add(eq(orb[i][n + 1], cell[(f"{row}{i}", orb[i][n])]))
                if n + 1 < N[i - 1]: s.add(Not(inD[orb[i][n + 1]]))
            s.add(inD[orb[i][N[i - 1]]])
    names = dict(e=e, a=[cell[(c, 's')] for c in C if c not in drop], u=[cell[(g, 's')] for g in G],
                 tend=[t[i][-1] for i in R3 if len(t[i]) > 1] if tN else [], wend=[w[i][-1] for i in R3] if wN else [])
    if extra: extra(s, le, inD, names, G)
    return s, le, G, names

def labels(s, le, G, xs, cap=4000):
    bits = [le[x, g] for x in xs for g in G]; seen = []
    while s.check() == sat and len(seen) < cap:
        mo = s.model(); v = tuple(is_true(mo.eval(b, model_completion=True)) for b in bits)
        seen.append(v); s.add(Or([b != val for b, val in zip(bits, v)]))
    return seen

def fmt(v, n):
    out = []
    for k in range(n):
        lab = [str(i) for i, bit in zip(R3, v[3 * k:3 * k + 3]) if bit]
        out.append('{' + ','.join(lab) + '}' if lab else 'out')
    return ' '.join(out)

def canon(v, n):  # orbit representative under S3 acting on generator indices AND on the pair/vertex positions
    best = None
    for perm in itertools.permutations(range(3)):
        # permuting generators permutes labels and also the positions of e (pairs) / a,u (vertices) consistently
        pos_pairs = {(0, 1): 0, (0, 2): 1, (1, 2): 2}
        def lab(k): return tuple(v[3 * k + j] for j in range(3))
        def plab(k): l = lab(k); return tuple(l[perm.index(j)] for j in range(3))
        # positions: e block (3 pairs), then vertex blocks of 3
        newv = [None] * n
        for k in range(n):
            blk, idx = divmod(k, 3)
            if blk == 0:
                i, j = [(0, 1), (0, 2), (1, 2)][idx]; ni, nj = sorted((perm[i], perm[j])); nk = pos_pairs[(ni, nj)]
            else:
                nk = perm[idx]
            newv[3 * blk + nk] = plab(k)
        key = tuple(x for l in newv for x in l)
        best = key if best is None or key < best else best
    return best

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'local'
    if mode == 'local':
        for irr in (False, True):
            s, le, G, nm = build(irr=irr)
            vs = labels(s, le, G, nm['e'] + nm['a'] + nm['u'])
            cl = sorted(set(canon(v, 9) for v in vs))
            ev = sorted(set(canon(v[:9] + (False,) * 0, 3) if False else tuple(v[:9]) for v in vs))
            print(f"irredundant={irr}: {len(vs)} label vectors (e|a|u), {len(cl)} up to S3; e-projections: {len(set(tuple(v[:9]) for v in vs))}", flush=True)
            for c in cl: print("   e:", fmt(c[:9], 3), "| a:", fmt(c[9:18], 3), "| u:", fmt(c[18:], 3))
        # sanity: Lean-forbidden patterns
        s, le, G, nm = build(extra=lambda s, le, inD, n, G: s.add([inD[x] for x in n['u']]))
        print("control: all u_i in D (generator_not_caseA forbids):", s.check(), flush=True)
    elif mode.startswith('orbits'):
        # Controls (UNSAT, each by a Lean theorem): generator lengths (1,1,1) `generator_not_caseA`; (2,1,1)
        # `two_outside_generator_responses`; anchor lengths (1,1,1) `contracting_simultaneous`; two anchor responses in D
        # (e.g. (1,1,2), or (1,·,·) with u_3 ∈ D, since a_3 ≤ u_3) `two_outside_anchor_responses`.
        controls = [((1, 1, 1), (2, 2, 2)), ((2, 2, 2), (2, 1, 1)), ((1, 2, 2), (2, 2, 1)), ((1, 1, 2), (2, 2, 2))]
        allowed = [((1, 2, 2), (1, 2, 2)), ((1, 2, 2), (2, 2, 2)), ((2, 2, 2), (2, 2, 2)), ((1, 2, 3), (1, 3, 2))]
        part = int(mode[6:]) if len(mode) > 6 else None
        jobs = [('control', c) for c in controls] + [('allowed', c) for c in allowed]
        for k, (kind, (tN, wN)) in enumerate(jobs):
            if part is not None and k % 2 != part: continue
            s, le, G, nm = build(irr=True, tN=tN, wN=wN)
            vs = labels(s, le, G, nm['tend'], cap=4)
            ends = sorted(set(fmt(v, 3) for v in vs))
            print(f"[{kind}] anchor orbit lengths {tN}, generator orbit lengths {wN}, irredundant meet support: "
                  f"{'SAT' if vs else 'UNSAT'}; sample anchor-entry labels (≤ 4): {ends}", flush=True)
    elif mode == 'minimize':
        # the UNSAT profile a_1 ∈ D, u_3 ∈ D, g1/g2 orbits entering at step 2, with rows dropped one at a time
        print("found: anchor lengths (1,·,·), generator lengths (2,2,1) is UNSAT (see `orbits`)", flush=True)
        for tN, wN, kw in [((1, 0, 0), (2, 2, 1), {}), ((1, 0, 0), (2, 0, 1), {}), ((1, 0, 0), (3, 2, 1), {}),
                           ((0, 1, 0), (2, 2, 1), {}), ((1, 0, 0), (2, 1, 2), {}), ((1, 0, 0), (1, 2, 2), {}),
                           ((1, 0, 0), (2, 2, 1), dict(support=False, drop=('c2', 'c3')))] + \
                          [((1, 0, 0), (2, 2, 1), dict(support=False, drop=('c2', 'c3', x))) for x in ('g123', 'm12', 'm13', 'm23')]:
            s, *_ = build(tN=tN, wN=wN, **kw)
            print(f"anchor lengths {tN} (0 = no orbit), generator lengths {wN}, {kw or 'full rows, meet support'}: {s.check()}", flush=True)
