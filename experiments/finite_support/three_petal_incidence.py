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

def build(irr=False, tN=None, wN=None, extra=None, drop=(), support=True, endmeets=False,
          meets=('v12', 'v13', 'v23', 'v123'), track=None):
    G = [f"g{i}" for i in R3]; M = [f"m{i}{j}" for i, j in P3]; C = [f"c{i}" for i in R3]
    rows = [x for x in G + M + C + ['g123'] if x not in drop]
    cols = ['s']; t = {}; w = {}
    if tN:
        for i in R3:
            t[i] = ['s'] + [f"t{i}_{n}" for n in range(1, tN[i - 1] + 1)]; cols += t[i][1:]  # length 0: no orbit
    if wN:
        for i in R3:
            w[i] = ['s'] + [f"w{i}_{n}" for n in range(1, wN[i - 1] + 1)]; cols += w[i][1:]
    vend = {}
    if endmeets:  # generator-orbit last outside points v_i and their pairwise / triple meets as new columns
        vend = {i: w[i][wN[i - 1] - 1] for i in R3}
        cols += list(meets)
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
    if endmeets:
        for name, idx in (('v12', (1, 2)), ('v13', (1, 3)), ('v23', (2, 3)), ('v123', (1, 2, 3))):
            if name in meets: glb(name, [vend[i] for i in idx])
    for (a, b), v in cell.items():
        for (a2, b2), v2 in cell.items():
            if (a, b) != (a2, b2): s.add(Implies(And(le[a, a2], le[b, b2]), le[v, v2]))
        nwc = Implies(And(inD[a], Not(inD[b])), And(Not(le[v, a]), Not(le[b, v])))
        if track is None: s.add(nwc)
        else:
            tag = Bool(f"NW[{a},{b}]"); track[tag] = (a, b); s.add(Implies(tag, nwc))
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
                 tend=[t[i][-1] for i in R3 if len(t[i]) > 1] if tN else [], vend=vend, w=w, cell=cell, wend=[w[i][-1] for i in R3] if wN else [])
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

def run_endpoints(part):
    """Endpoint labels Λ_i = labels of F(c_i, v_i), palettes Π_i = labels of F(g123, v_i), pairwise endpoint meets.
    Audit: F(g123, v_i) and F(c_i, v_i) are cells of the existing grid (rows g123, c_i; column v_i = last outside point
    of the g_i-orbit); the NEW constraints are the columns v_ij, v123 (exact meets) and their cells."""
    def cnt(bs): return Sum([If(b, 1, 0) for b in bs])
    def tests(le, inD, nm, G):
        c = nm['cell']; v = nm['vend']
        lam = {(i, j): le[c[(f"c{i}", v[i])], f"g{j}"] for i in R3 for j in R3}
        pal = {(i, j): le[c[('g123', v[i])], f"g{j}"] for i in R3 for j in R3}
        L = lambda i: [lam[(i, j)] for j in R3]; Pl = lambda i: [pal[(i, j)] for j in R3]
        eqP = lambda i, k: And([pal[(i, j)] == pal[(k, j)] for j in R3])
        exact = lambda i, S: And([lam[(i, j)] if j in S else Not(lam[(i, j)]) for j in R3])
        meetsD = [inD['v12'], inD['v13'], inD['v23']]
        return [
            ('C1 control: v123 outside D (endpoint_total_meet_in_D)', Not(inD['v123'])),
            ('C2 control: 2-cycle 1->2, 2->1 with v12 outside (endpoint_two_cycle)', And(lam[(1, 2)], lam[(2, 1)], Not(inD['v12']))),
            ('T1 singleton labels forming the 3-cycle 1->2->3->1', And(exact(1, {2}), exact(2, {3}), exact(3, {1}))),
            ('T2 some endpoint with >= 2 labels', Or([cnt(L(i)) >= 2 for i in R3])),
            ('T3 all endpoint palettes of size 1', And([cnt(Pl(i)) == 1 for i in R3])),
            ('T4 all endpoint palettes of size 2', And([cnt(Pl(i)) == 2 for i in R3])),
            ('T5 two identical palettes, one distinct', And(eqP(1, 2), Not(eqP(1, 3)))),
            ('T6 all pairwise endpoint meets outside D', And([Not(b) for b in meetsD])),
            ('T6+T1 3-cycle singleton labels and all pairwise meets outside', And(exact(1, {2}), exact(2, {3}), exact(3, {1}), *[Not(b) for b in meetsD])),
            ('T7 exactly one pairwise endpoint meet in D', cnt(meetsD) == 1),
        ]
    # memory: a full anchor+generator grid with the endpoint meets needs ~7 GB per process, so the main battery runs
    # with generator orbits only (anchor orbits are not needed for endpoint labels); the anchor profiles rerun the
    # decisive tests, one process at a time (part 'A').
    # Generator lengths (2, 2, 2) are excluded outright by `no_equal_time_two` (the base profile is UNSAT once the
    # endpoint meets are columns), so the battery runs on (2, 2, 3); (3, 3, 3) reruns the decisive tests (part 'A').
    if part == 'A':
        jobs = [((None, (3, 3, 3)), k) for k in (8, 9)]
    elif part == 'B':
        jobs = [((None, (2, 2, 2)), None)]
    else:
        jobs = [((None, (2, 2, 3)), k) for k in range(10)]
        jobs = [j for idx, j in enumerate(jobs) if part is None or idx % 2 == part]
    for pr, k in jobs:
        tN, wN = pr
        s, le, G, nm = build(irr=True, tN=tN, wN=wN, endmeets=True)
        ind = lambda a: Or([le[a, g] for g in G])  # membership in D, built on demand
        class D:  # lazy dict
            def __getitem__(self, a): return ind(a)
        name, cons = ('base profile (no test constraint)', BoolVal(True)) if k is None else tests(le, D(), nm, G)[k]
        s.add(cons)
        r = s.check(); extra = ''
        if r == sat:
            mo = s.model(); ev = lambda b: is_true(mo.eval(b, model_completion=True))
            c = nm['cell']; v = nm['vend']
            lab = lambda x: '{' + ','.join(str(j) for j in R3 if ev(le[x, f"g{j}"])) + '}' if ev(ind(x)) else 'out'
            Lam = [lab(c[(f"c{i}", v[i])]) for i in R3]
            Pi = [lab(c[('g123', v[i])]) for i in R3]
            trans = []
            for i in R3:
                orbit = nm['w'][i][:-1]
                trans.append('->'.join(lab(c[('g123', y)]) for y in orbit))
            md = ['D' if ev(ind(x)) else 'out' for x in ('v12', 'v13', 'v23', 'v123')]
            extra = f" | Λ={Lam} Π(v_i)={Pi} | palettes along g-orbits {trans} | v12,v13,v23,v123: {md}"
        print(f"anchor {tN} gen {wN}: {name}: {r}{extra}", flush=True)

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
    elif mode.startswith('endpoints'):
        arg = mode[9:]
        run_endpoints(arg if arg in ('A', 'B') else (int(arg) if arg else None))
    elif mode == 'minimize':
        # the UNSAT profile a_1 ∈ D, u_3 ∈ D, g1/g2 orbits entering at step 2, with rows dropped one at a time
        print("found: anchor lengths (1,·,·), generator lengths (2,2,1) is UNSAT (see `orbits`)", flush=True)
        for tN, wN, kw in [((1, 0, 0), (2, 2, 1), {}), ((1, 0, 0), (2, 0, 1), {}), ((1, 0, 0), (3, 2, 1), {}),
                           ((0, 1, 0), (2, 2, 1), {}), ((1, 0, 0), (2, 1, 2), {}), ((1, 0, 0), (1, 2, 2), {}),
                           ((1, 0, 0), (2, 2, 1), dict(support=False, drop=('c2', 'c3')))] + \
                          [((1, 0, 0), (2, 2, 1), dict(support=False, drop=('c2', 'c3', x))) for x in ('g123', 'm12', 'm13', 'm23')]:
            s, *_ = build(tN=tN, wN=wN, **kw)
            print(f"anchor lengths {tN} (0 = no orbit), generator lengths {wN}, {kw or 'full rows, meet support'}: {s.check()}", flush=True)
