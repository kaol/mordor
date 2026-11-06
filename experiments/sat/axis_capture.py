"""Axis-capture graphs and the mixed-pivot ladder at edge-height ≤ H (log §34.3z¹¹⁷; brief Program A5).

Preorder model with exact meets/joins on the named elements (a quotient of the real structure), F partial: only the
listed cells exist, with monotonicity between all of them and no witness on every cross cell. Edge-height ≤ H is
imposed on the named elements by a rank function (strict order ⇒ strictly larger rank, ranks in [0, H]). SAT answers
are partial models (not counterexamples to Cut); UNSAT answers are diagnostics of the finite constraint set.

Rows g_1..g_k ∈ D, orbits u_i(n) = F(g_i, u_i(n-1)) with exact first entry E_i, entry points e_i = u_i(E_i).
Graph: i → j iff e_i ≤ g_j, imposed exactly (edges and non-edges). Ladder (cumulative):
  S0 base; S1 rows pairwise incomparable and maximal among the named D-elements; S2 an interior (t_i < E_i)
  uncaptured D-valued grid column c; S3 Alternative I: F(m_T, c) ≤ m_T for some nonempty T (cells named);
  S4 a new maximum q ≥ c in D, incomparable with the rows, maximal among named D-elements;
  S5 q's own orbit with first entry E_q (some E_q ≤ H, tried in turn) and joins q ∨ g_i ∉ D;
  S6 minimal complement witnesses w_i ≤ q ∨ g_i (w_i ∉ D, minimal among named non-D elements), pairwise meets of
     distinct witnesses in D.
  python3 axis_capture.py classify | ladder H [job indices 0..9, comma-separated] | minh [job indices] | controls"""
import sys, itertools
from z3 import *

def digraphs(k):
    """Loopless digraphs on k vertices with every out-degree ≥ 1, up to isomorphism."""
    pairs = [(i, j) for i in range(k) for j in range(k) if i != j]
    seen, out = set(), []
    for bits in itertools.product((0, 1), repeat=len(pairs)):
        Ed = frozenset(p for p, b in zip(pairs, bits) if b)
        if any(not any((i, j) in Ed for j in range(k) if j != i) for i in range(k)): continue
        canon = min(tuple(sorted((pi[i], pi[j]) for i, j in Ed)) for pi in itertools.permutations(range(k)))
        if canon in seen: continue
        seen.add(canon); out.append(set(canon))
    return out

class Model:
    def __init__(s, H):
        s.H = H; s.E = []; s.cons = []; s.cells = {}
    def el(s, *names):
        for n in names:
            if n not in s.E: s.E.append(n)
    def build(s):
        S = Solver(); E = s.E
        le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}; D = {a: Bool(f"D|{a}") for a in E}
        rk = {a: Int(f"rk|{a}") for a in E}
        for a in E:
            S.add(le[a, a], le['bot', a], le[a, 'top'], rk[a] >= 0, rk[a] <= s.H)
            for b in E:
                for c in E: S.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
                S.add(Implies(And(le[a, b], D[b]), D[a]))
                S.add(Implies(And(le[a, b], Not(le[b, a])), rk[a] < rk[b]))
        S.add(D['bot'], Not(D['top']))
        s.S, s.le, s.D = S, le, D
        for f in s.cons: f(s)
        cl = list(s.cells.items())
        for (r, x), v in cl:
            S.add(Implies(And(D[r], Not(D[x])), And(Not(le[v, r]), Not(le[x, v]))))
            for (r2, x2), v2 in cl:
                if (r, x) != (r2, x2): S.add(Implies(And(le[r, r2], le[x, x2]), le[v, v2]))
        return S
    def eq(s, a, b): return And(s.le[a, b], s.le[b, a])
    def glb(s, z, q):
        s.S.add([s.le[z, x] for x in q]); s.S.add([Implies(And([s.le[w, x] for x in q]), s.le[w, z]) for w in s.E])
    def lub(s, z, q):
        s.S.add([s.le[x, z] for x in q]); s.S.add([Implies(And([s.le[x, w] for x in q]), s.le[z, w]) for w in s.E])

def setup(H, k, Es, graph, stage, Eq=1, extra=None, pre=None):
    M = Model(H); rows = [f"g{i}" for i in range(k)]
    M.el('bot', 'top', *rows)
    orb = [['top'] + [f"u{i}_{n}" for n in range(1, Es[i] + 1)] for i in range(k)]
    for i in range(k):
        M.el(*orb[i][1:])
        for n in range(Es[i]): M.cells[(rows[i], orb[i][n])] = orb[i][n + 1]
    Ts = [T for r in range(1, k + 1) for T in itertools.combinations(range(k), r)]
    mT = {T: (rows[T[0]] if len(T) == 1 else "m" + "".join(map(str, T))) for T in Ts}
    M.el(*mT.values())
    interior = [t for t in itertools.product(*[range(Es[i]) for i in range(k)]) if sum(1 for x in t if x) >= 2]
    wname = {t: "W" + "".join(map(str, t)) for t in interior}
    M.el(*wname.values()); M.el('c')
    if stage >= 3:
        for T in Ts: M.el(f"FT{mT[T]}"); M.cells[(mT[T], 'c')] = f"FT{mT[T]}"
    if stage >= 4: M.el('q')
    if stage >= 5:
        oq = ['top'] + [f"v_{n}" for n in range(1, Eq + 1)]; M.el(*oq[1:])
        for n in range(Eq): M.cells[('q', oq[n])] = oq[n + 1]
        M.el(*[f"J{i}" for i in range(k)])
    if stage >= 6: M.el(*[f"w{i}" for i in range(k)], *[f"wm{i}{j}" for i in range(k) for j in range(i + 1, k)])
    if pre: pre(M, rows, orb, wname)
    def base(M):
        S, le, D, eq = M.S, M.le, M.D, M.eq
        for r in rows: S.add(D[r])
        for i in range(k):
            S.add([Not(D[x]) for x in orb[i][1:Es[i]]]); S.add(D[orb[i][Es[i]]])
            e = orb[i][Es[i]]
            for j in range(k):
                if j != i: S.add(le[e, rows[j]] if (i, j) in graph else Not(le[e, rows[j]]))
        for T in Ts:
            if len(T) > 1: M.glb(mT[T], [rows[i] for i in T])
        for t in interior: M.glb(wname[t], [orb[i][t[i]] for i in range(k) if t[i]])
        if stage >= 1:
            for a in rows:
                for b in rows:
                    if a != b: S.add(Not(le[a, b]))
                for x in M.E:
                    if x != a: S.add(Implies(And(D[x], le[a, x]), le[x, a]))
        if stage >= 2:
            S.add(Or([eq('c', wname[t]) for t in interior])); S.add(D['c']); S.add([Not(le['c', r]) for r in rows])
        if stage >= 3: S.add(Or([le[f"FT{mT[T]}", mT[T]] for T in Ts]))
        if stage >= 4:
            S.add(D['q'], le['c', 'q']); S.add([And(Not(le['q', r]), Not(le[r, 'q'])) for r in rows])
            for x in M.E:
                if x != 'q': S.add(Implies(And(D[x], le['q', x]), le[x, 'q']))
        if stage >= 5:
            S.add([Not(D[x]) for x in oq[1:Eq]]); S.add(D[oq[Eq]])
            for i in range(k): M.lub(f"J{i}", ['q', rows[i]]); S.add(Not(D[f"J{i}"]))
        if stage >= 6:
            for i in range(k):
                w = f"w{i}"; S.add(Not(D[w]), le[w, f"J{i}"])
                for x in M.E:
                    if x != w: S.add(Implies(And(Not(D[x]), le[x, w]), le[w, x]))
            for i in range(k):
                for j in range(i + 1, k):
                    M.glb(f"wm{i}{j}", [f"w{i}", f"w{j}"])
                    S.add(Implies(Not(eq(f"w{i}", f"w{j}")), D[f"wm{i}{j}"]))
        if extra: extra(M, rows, orb, wname)
    M.cons.append(base)
    return M.build()

def ladder(H, k, Es, graph, maxstage=6):
    res = []
    for st in range(maxstage + 1):
        if st >= 5:
            r = 'unsat'
            for Eq in range(1, H + 1):
                if str(setup(H, k, Es, graph, st, Eq).check()) == 'sat': r = f'sat(E_q={Eq})'; break
        else:
            r = str(setup(H, k, Es, graph, st).check())
        res.append(r)
        if r == 'unsat': break
    return res

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'classify':
        for k in (2, 3):
            gs = digraphs(k); print(f"k={k}: {len(gs)} loopless digraphs with all out-degrees ≥ 1 (up to iso)")
            for G in gs: print("   ", sorted(G))
    elif mode == 'ladder':
        H = int(sys.argv[2])
        jobs = [(k, Es, G) for k, Es in [(2, (2, 2)), (2, (2, 3)), (2, (3, 3)), (3, (2, 2, 2))] for G in digraphs(k)]
        sel = [int(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else range(len(jobs))
        for idx in sel:
            k, Es, G = jobs[idx]
            if True:
                print(f"H={H} k={k} E={Es} graph={sorted(G)}: {ladder(H, k, Es, G)}", flush=True)
    elif mode == 'minh':
        jobs = [(k, Es, G) for k, Es in [(2, (2, 2)), (2, (2, 3)), (2, (3, 3)), (3, (2, 2, 2))] for G in digraphs(k)]
        sel = [int(x) for x in sys.argv[2].split(',')] if len(sys.argv) > 2 else range(len(jobs))
        for idx in sel:
            k, Es, G = jobs[idx]; best = None
            for H in range(1, 7):
                if any(str(setup(H, k, Es, G, 6, Eq).check()) == 'sat' for Eq in range(1, H + 1)): best = H; break
            print(f"k={k} E={Es} graph={sorted(G)}: least edge-height with the full ladder S0–S6 SAT = {best}", flush=True)
    elif mode == 'controls':
        G2 = {(0, 1), (1, 0)}
        def loop(M, rows, orb, wname): M.S.add(M.le[orb[0][2], rows[0]])
        print(f"control loop e_0 ≤ g_0 (no_loop), H=6: {setup(6, 2, (2, 2), G2, 0, extra=loop).check()}")
        def deep(M, rows, orb, wname): M.S.add(M.eq('c', 'W21'))
        print(f"control pivot W(2,1), E=(3,3), H=3 (orbit_support_bound: t+|S| = 4 > 3): {setup(3, 2, (3, 3), G2, 2, extra=deep).check()}")
        print(f"same pivot at H=4 (bound 4 ≤ 4): {setup(4, 2, (3, 3), G2, 2, extra=deep).check()}")
        print(f"control Situation II stage 2 at H=2 (|S|+1 ≤ H fails): {setup(2, 2, (2, 2), G2, 2).check()}")
        print(f"Situation II stage 2 at H=3: {setup(3, 2, (2, 2), G2, 2).check()}")
