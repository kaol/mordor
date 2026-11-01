"""Human-readable form of the z3 refutation of the entry pattern τ = (1, 2, 2) at ⊤ once x = w₂ ⊓ w₃ ∈ D
(log §34.3z⁷⁷; x ∈ D is Profile.lastpoints_no_common_lower, w₁ = ⊤).

Label sources (every v ≥ the column considered):
  * c₁: τ₁ = 1, so F(c₁, v) ≤ F(c₁, ⊤) ≤ p_{σ1} at every column, σ1 ≠ 1 (anchor_sandwich at ⊤);
  * c₂ at w₂, c₃ at w₃: the entries e₂ ≤ p_{σ2}, e₃ ≤ p_{σ3}, σi ≠ i;
  * m₂₃ ≤ c₂ ⊓ c₃: F(m₂₃, v) ≤ F(c₂, ⊤) ⊓ F(c₃, ⊤) = w₂ ⊓ w₃ = x ≤ p_k for k ∈ K = Λ(x), with K ⊉ {2, 3}
    (no witness at (m₂₃, ⊤)).
Singleton σ's are the worst case (larger labels only add bounds). For each assignment the script looks for a closed
meet family (Profile.no_closed_meet_family) at one of the columns ⊤, w₂, w₃. Prints the surviving assignments."""
import itertools
I = [1, 2, 3]
subsets = [frozenset(c) for n in (2, 3) for c in itertools.combinations(I, n)]
def closed(lam):
    fam = set(subsets)
    while True:
        bad = {A for A in fam if not any(B <= lam[A] for B in fam)}
        if not bad: return bool(fam)
        fam -= bad
nonempty = [frozenset(c) for n in (1, 2, 3) for c in itertools.combinations(I, n)]
surv, total = [], 0
for s1, s2, s3 in itertools.product([2, 3], [1, 3], [1, 2]):
    for K in nonempty:
        if K >= {2, 3}: continue
        total += 1
        def lam(col):
            L = {}
            for A in subsets:
                S = set()
                if 1 in A: S.add(s1)
                if A >= {2, 3}: S |= K
                if col == 'w2' and 2 in A: S.add(s2)
                if col == 'w3' and 3 in A: S.add(s3)
                L[A] = frozenset(S)
            return L
        if not any(closed(lam(c)) for c in ['top', 'w2', 'w3']): surv.append((s1, s2, s3, sorted(K)))
print(f"{total} assignments, {len(surv)} without a closed meet family: {surv}")
