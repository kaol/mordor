import Mordor.Height5
import Mordor.Reach

/-!
# The Cut Lemma on lattices with a rank ≤ 5, e.g. subspace lattices of dimension ≤ 5 (log §34.3z¹³)

If a complete lattice carries a strictly monotone rank `r : α → ℕ` bounded by 5, it has no chain of seven elements, so
`cut_height5` applies. The subspace lattice `Submodule K V` of a space of dimension ≤ 5 is the instance
`r = finrank K ·` (strictly monotone by Mathlib's `Submodule.finrank_lt_finrank_of_lt`; that instance is not compiled
here because Mathlib's linear-algebra oleans are not built in this checkout).

Consequence for "bridges" that would encode an analytic positivity statement as a Cut configuration on a subspace
lattice (the RH brief of §34.3z¹³): for *every* monotone `F`, `R(F)` is everything (`R_univ`), and every down-set
containing `⊥` closed under `a F` and `(b F)⁻¹` is everything (`closed_eq_univ`). So no proper down-set, in particular
not the positivity down-set `{U | Q|_U ⪰ 0}` of an indefinite form, is closed for any `F`. An implication "negative
direction ⟹ closed proper down-set" is therefore equivalent to the absence of negative directions.
-/

namespace Mordor.Ranked
open Ground

variable {α : Type*} [CompleteLattice α]

/-- A strict chain of `k + 1` elements ending at `x` forces `k ≤ r x` for a strictly monotone `r`. -/
theorem chain_le_rank {r : α → ℕ} (hr : StrictMono r) : ∀ (k : ℕ) (x : α), chainTo x k → k ≤ r x
  | 0, _, _ => Nat.zero_le _
  | k + 1, _, ⟨y, hyx, hy⟩ => Nat.succ_le_of_lt ((chain_le_rank hr k y hy).trans_lt (hr hyx))

theorem noChain {r : α → ℕ} (hr : StrictMono r) (h : ∀ x, r x ≤ 5) : NoChain α 6 := fun x hx => by
  have := (chain_le_rank hr 6 x hx).trans (h x)
  omega

/-- **Cut with a rank ≤ 5**: every monotone `F` reaches everything. -/
theorem R_univ {r : α → ℕ} (hr : StrictMono r) (h : ∀ x, r x ≤ 5) (G : α →o α →o α) : R G = Set.univ :=
  cutMaps_iff_R.mp (cutMaps_of_cells (cut_height5' (noChain hr h) G))

/-- **No closed proper down-set**, whatever monotone `F` is built. -/
theorem closed_eq_univ {r : α → ℕ} (hr : StrictMono r) (h : ∀ x, r x ≤ 5) (G : α →o α →o α) {D : Set α}
    (hD : Closed G D) : D = Set.univ :=
  Set.eq_univ_of_univ_subset ((R_univ hr h G).symm ▸ R_subset hD)

end Mordor.Ranked
