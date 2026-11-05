"""Reduced combinatorial form of the asynchronous meet grid (log §34.3z¹⁰⁵), general k.

Grid G = ∏_i [0, n_i + 1], labelling L : G → P(K) (L(t) ∋ k ⇔ W(t) ≤ g_k), with
  (i)   t ≤ t' ⇒ L(t) ⊆ L(t')
  (ii)  L(t) ≠ ∅ when some t_i = n_i + 1;  L(a e_i) = ∅ for a ≤ n_i
  (iii) L(t) = ∅, T ≠ ∅, π_T(t) + 1_T ∈ G  ⇒  T ⊄ L(π_T(t) + 1_T)
(iii) is no witness at the row m_T and the outside column W(t), with F(m_T, W(t)) ≤ W(π_T(t) + 1_T)
(`asynchronous_meet_step`); the other cell constraints of `abstract_grid.py` are implied by monotonicity of L."""
import itertools, sys
from z3 import *

def solve(n, drop=()):
    k = len(n); K = range(k)
    SUBS = [frozenset(c) for r in range(1, k + 1) for c in itertools.combinations(K, r)]
    G = list(itertools.product(*[range(n[i] + 2) for i in K]))
    s = Solver()
    L = {(t, j): Bool(f"L{t}{j}") for t in G for j in K}
    D = {t: Or([L[(t, j)] for j in K]) for t in G}
    for t in G:
        for i in K:  # cover relations suffice for monotonicity
            if t[i] < n[i] + 1:
                t2 = tuple(t[x] + (1 if x == i else 0) for x in K)
                if 'mono' not in drop: s.add([Implies(L[(t, j)], L[(t2, j)]) for j in K])
        if any(t[i] == n[i] + 1 for i in K): s.add(D[t])
        if sum(1 for i in K if t[i] > 0) <= 1 and all(t[i] <= n[i] for i in K): s.add(Not(D[t]))
        for T in SUBS:
            if ('nw', len(T)) in drop or ('nwT', T) in drop: continue
            tgt = tuple((t[i] + 1) if i in T else 0 for i in K)
            if all(tgt[i] <= n[i] + 1 for i in K):
                s.add(Implies(Not(D[t]), Not(And([L[(tgt, j)] for j in T]))))
    return s.check()

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'k3'
    if mode == 'k2':
        for n in itertools.product(range(5), repeat=2):
            if n[0] <= n[1]: print(f"k=2 n={n}: {solve(n)}", flush=True)
    elif mode == 'k3':
        bad = []
        for n in itertools.product(range(5), repeat=3):
            if n[0] <= n[1] <= n[2]:
                r = solve(n); print(f"k=3 n={n}: {r}", flush=True)
                if r != unsat: bad.append(n)
        print("k=3 non-UNSAT profiles:", bad)
    elif mode == 'ablate':
        for n in [(1, 1, 2), (2, 2, 2)]:
            for d in [(), ('mono',), (('nw', 1),), (('nw', 2),), (('nw', 3),)]:
                print(f"k=3 n={n} without {d or 'nothing'}: {solve(n, d)}", flush=True)
    elif mode == 'k4':
        for n in itertools.product(range(3), repeat=4):
            if n[0] <= n[1] <= n[2] <= n[3]: print(f"k=4 n={n}: {solve(n)}", flush=True)
