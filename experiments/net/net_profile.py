"""The meet-row net profile (log §34.3z⁸⁵), z3.

Named partial model: generators, ALL nonempty meet rows m_A as glbs, the h_A-orbit of ⊤ for every A
(o_{A,0} = ⊤, o_{A,k+1} = F(m_A, o_{A,k}), outside D for k ≤ τ(A), entry o_{A,τ(A)+1} ∈ D), F on every row ×
every named orbit column, monotone and witness-free. NO sandwich constraint. Question: which entry-time profiles are
consistent? Net facts proved in Lean (Net.lean) are then automatic consequences of the encoding.
k = 1: one row; k = 2: rows p1, p2, m12; k = 3 (argument k3): seven rows, sample profiles.
With argument sandwich, FGTwo/anchor sandwich at ⊤ is added (k = 2: m12-entry below neither generator)."""
import itertools, sys
from z3 import *
K = 3 if 'k3' in sys.argv else (1 if 'k1' in sys.argv else 2)
SAND = 'sandwich' in sys.argv
IDX = [str(i) for i in range(1, K + 1)]
SETS = [frozenset(c) for n in range(1, K + 1) for c in itertools.combinations(IDX, n)]
name = lambda A: 'm' + ''.join(sorted(A))
def run(tau):
    rows = [name(A) for A in SETS]
    cols = ['top'] + [f"o{name(A)}_{k}" for A in SETS for k in range(1, tau[A] + 1)]
    val = {(r, c): f"F[{r},{c}]" for r in rows for c in cols}
    E = ['bot'] + rows + cols + list(val.values())
    s = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    for a in E:
        s.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            for c in E: s.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
    P = [name(frozenset([i])) for i in IDX]
    inD = {a: Or([le[a, q] for q in P]) for a in E}
    for a, b in itertools.permutations(P, 2): s.add(Not(le[a, b]))
    for A in SETS:
        if len(A) > 1:
            z = name(A); xs = [name(frozenset([i])) for i in A]
            s.add([le[z, x] for x in xs]); s.add([Implies(And([le[w, x] for x in xs]), le[w, z]) for w in E])
    if K == 3:
        for i in IDX:
            o = [k for k in IDX if k != i]; s.add(Not(le[name(frozenset(o)), name(frozenset([i]))]))  # strict crossing
    s.add([inD[r] for r in rows]); s.add([Not(inD[c]) for c in cols])
    for (r, c), v in val.items():
        for (r2, c2), v2 in val.items():
            if (r, c) != (r2, c2): s.add(Implies(And(le[r, r2], le[c, c2]), le[v, v2]))
        s.add(Not(le[v, r]), Not(le[c, v]))
    eq = lambda a, b: And(le[a, b], le[b, a])
    ends = {}
    for A in SETS:
        pts = ['top'] + [f"o{name(A)}_{k}" for k in range(1, tau[A] + 1)]
        for k in range(len(pts) - 1): s.add(eq(pts[k + 1], val[name(A), pts[k]]))
        ends[A] = val[name(A), pts[-1]]; s.add(inD[ends[A]])
    if SAND and K == 2:
        s.add(Not(le[ends[frozenset(IDX)], 'm1']), Not(le[ends[frozenset(IDX)], 'm2']))
    return s.check()
if K <= 2:
    for t in itertools.product([1, 2, 3], repeat=len(SETS)):
        tau = dict(zip(SETS, t))
        if any(tau[B] > tau[A] for A in SETS for B in SETS if A < B): continue     # net_time_mono
        print(f"k={K}{' +sandwich' if SAND else ''} tau={ {''.join(sorted(A)): tau[A] for A in SETS} }: {run(tau)}", flush=True)
else:
    for t in [1, 2]:
        for tb in [1, 2]:
            tau = {A: (tb if len(A) == 3 else t) for A in SETS}
            if tb > t: continue
            print(f"k=3 tau(singletons, pairs)={t}, tau(123)={tb}: {run(tau)}", flush=True)
