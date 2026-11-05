"""Label abstraction of the asynchronous meet grid (log §34.3z¹⁰⁵), z3 (pure booleans, no lattice).

Three generators, a common contracting column s, generator orbits u_i(t) = T_i^t(s) with last outside index n_i.
Grid columns W(t) = ⋀ u_i(t_i), 0 ≤ t_i ≤ n_i + 1 (W(t) with t_j = 0 off T is the subset meet W_T). Rows m_T, T ≠ ∅.
Variables: D(t), labels L(t, k) ⇔ W(t) ≤ g_k; cell labels lab(T, t, k) ⇔ F(m_T, W(t)) ≤ g_k.
Sound consequences of the lattice model (every lattice model induces an abstract model):
  labels: D(t) ⇔ ∃k L(t,k); t ≤ t' ⇒ L(t) ⊆ L(t')                         (W antitone)
  axes:   D(t_i e_i) false for t_i ≤ n_i; D(t) true if some t_i = n_i + 1      (orbit facts)
  cells:  T ⊆ T', t ≤ t' ⇒ lab(T,t) ⊆ lab(T',t')                          (monotone F)
  step:   L(π_T(t) + 1_T) ⊆ lab(T, t)        (F(m_T, W(t)) ≤ ⋀_{i∈T} u_i(t_i+1), asynchronous_meet_step)
  exact:  lab({i}, t e_i) = L((t+1) e_i)       (F(g_i, u_i(t)) = u_i(t+1))
  NW:     ¬D(t) ⇒ T ⊄ lab(T, t)               (no witness at the row m_T, column W(t) outside D)
UNSAT here is a theorem about all such lattices (no chain condition); SAT is only a relaxation model."""
import itertools, sys
from z3 import *
K = (0, 1, 2)
SUBS = [frozenset(c) for r in (1, 2, 3) for c in itertools.combinations(K, r)]

def model(n, extra=None):
    G = list(itertools.product(*[range(n[i] + 2) for i in K]))
    le = lambda a, b: all(x <= y for x, y in zip(a, b))
    s = Solver()
    L = {(t, k): Bool(f"L{t}{k}") for t in G for k in K}
    D = {t: Or([L[(t, k)] for k in K]) for t in G}
    lab = {(T, t, k): Bool(f"c{sorted(T)}{t}{k}") for T in SUBS for t in G for k in K}
    for t in G:
        for t2 in G:
            if t != t2 and le(t, t2):
                s.add([Implies(L[(t, k)], L[(t2, k)]) for k in K])
    for t in G:
        if any(t[i] == n[i] + 1 for i in K): s.add(D[t])
        nz = [i for i in K if t[i] > 0]
        if len(nz) <= 1 and all(t[i] <= n[i] for i in K): s.add(Not(D[t]))
    for T in SUBS:
        for t in G:
            for T2 in SUBS:
                if T <= T2:
                    for t2 in G:
                        if le(t, t2) and (T, t) != (T2, t2):
                            s.add([Implies(lab[(T, t, k)], lab[(T2, t2, k)]) for k in K])
            tgt = tuple((t[i] + 1) if i in T else 0 for i in K)
            if all(tgt[i] <= n[i] + 1 for i in K):
                s.add([Implies(L[(tgt, k)], lab[(T, t, k)]) for k in K])
            s.add(Implies(Not(D[t]), Not(And([lab[(T, t, k)] for k in T]))))
    for i in K:
        for a in range(n[i] + 1):
            t = tuple(a if j == i else 0 for j in K); t1 = tuple(a + 1 if j == i else 0 for j in K)
            s.add([lab[(frozenset([i]), t, k)] == L[(t1, k)] for k in K])
    if extra: extra(s, G, L, D, lab)
    return s, G, L, D, lab

if __name__ == '__main__':
    for n in [(1, 1, 1), (1, 1, 2), (1, 2, 2), (2, 2, 2), (1, 1, 3), (1, 2, 3), (2, 2, 3), (0, 1, 1), (0, 1, 2), (0, 2, 2)]:
        s, G, L, D, lab = model(n)
        r = s.check()
        out = f"last outside indices n = {n} (entry lengths {tuple(x + 1 for x in n)}), grid {len(G)} columns: {r}"
        if r == sat:
            mo = s.model()
            B = [t for t in G if is_true(mo.eval(D[t], model_completion=True))]
            mins = [t for t in B if all(t[i] <= n[i] for i in K) and not any(b != t and all(b[i] <= t[i] for i in K) for b in B)]
            out += f" | minimal mixed boundary points ≤ n: {mins}"
        print(out, flush=True)
