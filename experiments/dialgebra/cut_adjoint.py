"""Round 25 (§33.3): the Cut Lemma is self-dual per F.

Φ(D) = ↓(D ∪ a(D) ∪ b⁻¹(D)) on down-sets, Ψ(U) = ↑(U ∪ b(U) ∪ a⁻¹(U)) on up-sets. For a down-set D and an up-set U,
Φ(D) ∩ U = ∅ ⟺ D ∩ Ψ(U) = ∅ (both say D ∩ U = ∅, a(D) ∩ U = ∅, b(U) ∩ D = ∅), i.e. Φ ⊣ c∘Ψ∘c with c = complement.
Iterating: R_k ∩ U_j = ∅ ⟺ R_{k+j} ≠ L ⟺ U_{k+j} ≠ L, where R_k = Φ^k(↓⊥), U_j = Ψ^j(↑⊤).
Only monotonicity of a, b is used; checked on all of Mon(L)² for every lattice of size 4 and 5."""
import os, sys, itertools
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'gpu'))
import numpy as np, lattices


def check(L, A, B):
    n = L.n; R = range(n); leq = L.leq
    down = lambda S: frozenset(z for z in R if any(leq[z, s] for s in S))
    up = lambda S: frozenset(z for z in R if any(leq[s, z] for s in S))
    cnt = 0
    for a, b in zip(A.tolist(), B.tolist()):
        Rs, Us = [down({L.bot})], [up({L.top})]
        for _ in range(2 * n + 2):
            D = Rs[-1]; Rs.append(down(D | {a[x] for x in D} | {y for y in R if b[y] in D}))
            U = Us[-1]; Us.append(up(U | {b[x] for x in U} | {y for y in R if a[y] in U}))
        N = len(Rs) - 1
        for k, j in itertools.product(range(N + 1), repeat=2):
            if k + j > N: continue
            lhs = not (Rs[k] & Us[j])
            assert lhs == (len(Rs[k + j]) < n) == (len(Us[k + j]) < n), (L.name, a, b, k, j)
        cnt += 1
    return cnt


if __name__ == '__main__':
    # The argument uses only monotonicity of a and b, so the check runs over all of Mon(L)² (realizable or not).
    for L in [lattices.parse('B2')] + [L for n in (4, 5) for L in lattices.all_lattices(n)]:
        Mon = np.array(L.mon); idx = np.array(list(itertools.product(range(len(Mon)), repeat=2)))
        print(f"{L.name:6} |Mon| = {len(Mon)}: all {check(L, Mon[idx[:, 0]], Mon[idx[:, 1]])} monotone pairs (a, b): "
              f"R_k ∩ U_j = ∅ ⟺ R_(k+j) ≠ L ⟺ U_(k+j) ≠ L", flush=True)
