"""Repeated cycle-to-new-maximum generation: minimal edge-height of partial models (log §34.3z¹¹⁷, brief A3).

Preorder model with exact meets on the named elements and rank-bounded height, F partial (orbit cells only), monotone
between all named cells, no witness on every cross cell. SAT = partial model, not a counterexample.
Start: rows r_0..r_{k-1} ∈ D, pairwise incomparable and maximal among named D-elements, every orbit u_r with first
entry at 2 (u_r(1) ∉ D, e_r = u_r(2) ∈ D), axis-capture graph fixed (a two-cycle for k = 2, a three-cycle for k = 3),
so the family is in Situation II. Step s = 1..n: the current family R (initial rows and q_1..q_{s-1}) is in Situation
II (every entry point below some row of R); an interior pivot c_s = ⋀ of ≥ 2 interior axis points u_r(1), r ∈ R, lies
in D below no row of R; a new row q_s ∈ D with c_s ≤ q_s, incomparable with R and maximal among named D-elements; q_s
gets the orbit u_{q_s}(1) ∉ D, u_{q_s}(2) ∈ D, whose entry point is below some row of R ∪ {q_s} other than q_s.
Alternative I is not imposed (it only adds constraints; omitting it keeps SAT meaningful as a partial model).
Output: the least H ≤ Hmax for which n steps are SAT.
  python3 axis_iterate.py k n_max Hmax"""
import sys, itertools
from z3 import *

def model(k, n, H, entry=2):
    rows = [f"r{i}" for i in range(k)] + [f"q{s}" for s in range(1, n + 1)]
    E = ['bot', 'top'] + rows + [f"{r}_1" for r in rows] + [f"{r}_2" for r in rows]
    fam = {s: rows[:k + s - 1] for s in range(1, n + 1)}           # family at step s
    meets = {}
    for s in range(1, n + 1):
        R = fam[s]
        for sz in range(2, len(R) + 1):
            for sub in itertools.combinations(R, sz):
                if sub not in meets: meets[sub] = "M_" + "_".join(sub); E.append(meets[sub])
    S = Solver()
    le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}; D = {a: Bool(f"D|{a}") for a in E}
    rk = {a: Int(f"rk|{a}") for a in E}
    for a in E:
        S.add(le[a, a], le['bot', a], le[a, 'top'], rk[a] >= 0, rk[a] <= H)
        for b in E:
            for c in E: S.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
            S.add(Implies(And(le[a, b], D[b]), D[a]))
            S.add(Implies(And(le[a, b], Not(le[b, a])), rk[a] < rk[b]))
    S.add(D['bot'], Not(D['top']))
    eq = lambda a, b: And(le[a, b], le[b, a])
    for sub, z in meets.items():
        q = [f"{r}_1" for r in sub]
        S.add([le[z, x] for x in q]); S.add([Implies(And([le[w, x] for x in q]), le[w, z]) for w in E])
    cells = {}
    for r in rows:
        cells[(r, 'top')] = f"{r}_1"; cells[(r, f"{r}_1")] = f"{r}_2"
        S.add(D[r], Not(D[f"{r}_1"]), D[f"{r}_2"])
    for (r, x), v in cells.items():
        S.add(Implies(And(D[r], Not(D[x])), And(Not(le[v, r]), Not(le[x, v]))))
        for (r2, x2), v2 in cells.items():
            if (r, x) != (r2, x2): S.add(Implies(And(le[r, r2], le[x, x2]), le[v, v2]))
    init = rows[:k]
    cyc = [(0, 1), (1, 0)] if k == 2 else [(0, 1), (1, 2), (2, 0)]
    for i in range(k):
        for j in range(k):
            if i != j: S.add(le[f"{init[i]}_2", init[j]] if (i, j) in cyc else Not(le[f"{init[i]}_2", init[j]]))
    def maximal(r):
        for x in E:
            if x != r: S.add(Implies(And(D[x], le[r, x]), le[x, r]))
    for a in init:
        maximal(a)
        for b in init:
            if a != b: S.add(Not(le[a, b]))
    for s in range(1, n + 1):
        R = fam[s]; q = f"q{s}"
        for r in R: S.add(Or([le[f"{r}_2", r2] for r2 in R if r2 != r]))      # Situation II for R
        piv = [meets[sub] for sub in meets if set(sub) <= set(R)]
        c = Bool(f"dummy{s}")
        S.add(Or([And(D[m], *[Not(le[m, r]) for r in R], le[m, q]) for m in piv]))   # pivot c_s ≤ q_s
        S.add([And(Not(le[q, r]), Not(le[r, q])) for r in R]); maximal(q)
        S.add(Or([le[f"{q}_2", r2] for r2 in R]))                               # q's entry captured by R
    return S

if __name__ == '__main__':
    k, nmax, Hmax = (int(x) for x in sys.argv[1:4])
    for n in range(0, nmax + 1):
        best = None
        for H in range(1, Hmax + 1):
            if str(model(k, n, H).check()) == 'sat': best = H; break
        print(f"k={k}, {n} new-maximum steps: least edge-height of a partial model = {best}", flush=True)
