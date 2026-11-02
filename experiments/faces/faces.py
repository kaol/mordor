"""Face-wise provenance profiles (log §34.3z⁹¹), z3.

K generators (antichain; pairwise meets m_ij as glbs, strict crossing m_jk ≰ p_i; anchors c_i = ⋁_j m_ij as lubs;
optionally the triple meets). Anchor orbits from ⊤ of length n_i: w_i = h_i^{n_i}(⊤) is the last outside point,
e_i = F(c_i, w_i) ∈ D with e_i ≤ p_{λ_i} and e_i ≰ p_i (anchor_sandwich at ⊤; further labels free).
A dependent set J: v_J = ⋀_{j∈J} w_j ∈ D, every proper nonempty face v_S (S ⊂ J) outside D (named glbs, used as
columns). F on every row × column (⊤, orbit points, faces), monotone and witness-free; nothing on D × D.
Each case: λ (a function with λ_i ≠ i), J, orbit lengths."""
import itertools, sys
from z3 import *

def run(K, lam, J, n, triple=True, b_top=None):
    I = list(range(1, K + 1))
    P = [f"p{i}" for i in I]
    pairs = list(itertools.combinations(I, 2))
    M = {f"m{a}{b}": [f"p{a}", f"p{b}"] for a, b in pairs}
    if triple and K >= 3:
        for T in itertools.combinations(I, 3): M["m" + "".join(map(str, T))] = [f"p{t}" for t in T]
    C = {f"c{i}": [f"m{min(i,j)}{max(i,j)}" for j in I if j != i] for i in I}
    rows = P + list(M) + list(C)
    orb = {i: ['top'] + [f"o{i}_{k}" for k in range(1, n[i] + 1)] for i in I}
    w = {i: orb[i][-1] for i in I}
    faces = [frozenset(S) for r in range(2, len(J) + 1) for S in itertools.combinations(sorted(J), r)]
    fname = {S: "v" + "".join(map(str, sorted(S))) for S in faces}
    cols = ['top'] + [x for i in I for x in orb[i][1:]] + [fname[S] for S in faces if S != frozenset(J)]
    val = {(a, c): f"F[{a},{c}]" for a in rows for c in cols}
    E = list(dict.fromkeys(['bot'] + rows + cols + [fname[frozenset(J)]] + list(val.values())))
    s = Solver(); le = {(a, b): Bool(f"le|{a}|{b}") for a in E for b in E}
    for a in E:
        s.add(le[a, a], le['bot', a], le[a, 'top'])
        for b in E:
            for c in E: s.add(Implies(And(le[a, b], le[b, c]), le[a, c]))
    inD = {a: Or([le[a, q] for q in P]) for a in E}
    for a, b in itertools.permutations(P, 2): s.add(Not(le[a, b]))
    def glb(z, xs): s.add([le[z, x] for x in xs]); s.add([Implies(And([le[u, x] for x in xs]), le[u, z]) for u in E])
    def lub(z, xs): s.add([le[x, z] for x in xs]); s.add([Implies(And([le[x, u] for x in xs]), le[z, u]) for u in E])
    for k, v in M.items(): glb(k, v)
    for k, v in C.items(): lub(k, v)
    for a, b in pairs:
        for i in I:
            if i not in (a, b): s.add(Not(le[f"m{a}{b}", f"p{i}"]))
    s.add([inD[a] for a in rows]); s.add([Not(inD[c]) for c in cols])
    for (a, c), x in val.items():
        for (a2, c2), x2 in val.items():
            if (a, c) != (a2, c2): s.add(Implies(And(le[a, a2], le[c, c2]), le[x, x2]))
        s.add(Not(le[x, a]), Not(le[c, x]))
    eq = lambda a, b: And(le[a, b], le[b, a])
    for i in I:
        for k in range(n[i]): s.add(eq(orb[i][k + 1], val[f"c{i}", orb[i][k]]))
        e = val[f"c{i}", w[i]]
        s.add(inD[e], le[e, f"p{lam[i]}"], Not(le[e, f"p{i}"]))
    for S in faces:
        glb(fname[S], [w[i] for i in S])
        s.add(inD[fname[S]] if S == frozenset(J) else Not(inD[fname[S]]))
    if b_top is not None:
        bJ = "m" + "".join(map(str, sorted(J)))
        s.add(inD[val[bJ, 'top']] if b_top else Not(inD[val[bJ, 'top']]))
    return s.check()

cases3 = [
    ("3-cycle 1->2->3->1, J = {1,2,3} Hamiltonian", 3, {1: 2, 2: 3, 3: 1}, [1, 2, 3]),
    ("3-cycle 1->2->3->1, J = {1,2} (label of 2 escapes J)", 3, {1: 2, 2: 3, 3: 1}, [1, 2]),
    ("2-cycle 1<->2 with tail 3->1, J = {1,2}", 3, {1: 2, 2: 1, 3: 1}, [1, 2]),
]
for name, K, lam, J in (cases3 if 'k3' in sys.argv or len(sys.argv) == 1 else []):
    for nn in [1, 2]:
        n = {i: nn for i in range(1, K + 1)}
        print(f"k={K} {name}, orbit lengths {nn}: {run(K, lam, J, n)}", flush=True)
if 'btop' in sys.argv:
    for bt in [True, False]:
        print(f"k=3 Hamiltonian 3-cycle, orbit lengths 2, F(m123, top) {'in' if bt else 'outside'} D: "
              f"{run(3, {1: 2, 2: 3, 3: 1}, [1, 2, 3], {1: 2, 2: 2, 3: 2}, b_top=bt)}", flush=True)
if 'k4' in sys.argv:
    for name, lam, J in [("4-cycle 1->2->3->4->1, J = {1,2,3,4}", {1: 2, 2: 3, 3: 4, 4: 1}, [1, 2, 3, 4]),
                         ("4-cycle, J = {1,3}", {1: 2, 2: 3, 3: 4, 4: 1}, [1, 3])]:
        print(f"k=4 {name}, orbit lengths 1: {run(4, lam, J, {i: 1 for i in range(1, 5)}, triple=False)}", flush=True)
