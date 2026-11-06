import Mordor.FinGenAll
import Mordor.GoodWordPivot

/-!
# Fresh-word pivot revision: why monotonicity cannot force pivot progress (round 26, §34.3z¹⁰⁹)

`FinGen.exists_pivot` (extracted from `captured`): a witness-free response table on finite `P`, `U` has a pivot cell
`(A, B)`, nonempty and **balanced** (`|A| = |B|`), whose value avoids every `p ∈ P` and lies above no `u ∈ U`.

The brief's Lemma A asks, after adding a captor `p ≥ z*` (resp. `u ≤ z*`), for a fresh good word whose pivot `z'` is
`≥ z*` (resp. `≤ z*`). The only comparisons monotonicity of `F` forces between cell values are along the cell order
`(A, B) ≤ (A', B') :⇔ A' ⊆ A ∧ B ⊆ B'` (`z` is monotone for it); no chain through boundary representatives exists,
since that would need some `p ≤ u`.

* `balanced_comparable_eq`: two balanced cells comparable in the cell order are equal.
* `pivot_progress_not_forced`: so if `z* ≤ p` and the new pivot avoids `p`, the new pivot cell is never above the old
  one in the cell order — in either direction of the brief (dually for a `U`-captor).
* `fresh_strict_up`, `fresh_strict_down`: *if* a comparison `z* ≤ z'` (resp. `z' ≤ z*`) holds, it is strict.
Hence Lemma A can only hold through comparabilities of `F`-values that the finite data do not force; the z3 models of
`experiments/infcapture/fresh_word.py` realize instances where none holds and Lemma A fails.
-/

namespace Mordor.GoodWordRevision

/-- **Balanced cells comparable in the cell order are equal.** -/
theorem balanced_comparable_eq {ι κ : Type*} {A A' : Finset ι} {B B' : Finset κ} (hA : A' ⊆ A) (hB : B ⊆ B')
    (hbal : A.card = B.card) (hbal' : A'.card = B'.card) : A' = A ∧ B = B' := by
  have h1 := Finset.card_le_card hA; have h2 := Finset.card_le_card hB
  exact ⟨Finset.eq_of_subset_of_card_le hA (by omega), Finset.eq_of_subset_of_card_le hB (by omega)⟩

/-- **Pivot progress is never forced by the cell order** (`P`-captor case). If the old pivot cell `(A, B)` has
value `≤ p` and the new pivot cell `(A', B')` has value `≰ p`, the new cell is not above the old one. -/
theorem pivot_progress_not_forced {α ι κ : Type*} [Preorder α] (z : Finset ι × Finset κ → α) {p : α}
    {A A' : Finset ι} {B B' : Finset κ} (hbal : A.card = B.card) (hbal' : A'.card = B'.card)
    (hold : z (A, B) ≤ p) (hnew : ¬ z (A', B') ≤ p) : ¬ (A' ⊆ A ∧ B ⊆ B') := fun ⟨hA, hB⟩ => by
  obtain ⟨rfl, rfl⟩ := balanced_comparable_eq hA hB hbal hbal'
  exact hnew hold

/-- The same for a `U`-captor `u ≤ z*`: the new cell is not below the old one. -/
theorem pivot_regress_not_forced {α ι κ : Type*} [Preorder α] (z : Finset ι × Finset κ → α) {u : α}
    {A A' : Finset ι} {B B' : Finset κ} (hbal : A.card = B.card) (hbal' : A'.card = B'.card)
    (hold : u ≤ z (A, B)) (hnew : ¬ u ≤ z (A', B')) : ¬ (A ⊆ A' ∧ B' ⊆ B) := fun ⟨hA, hB⟩ => by
  obtain ⟨rfl, rfl⟩ := balanced_comparable_eq hA hB hbal' hbal
  exact hnew hold

/-- **Strict progress, if a comparison holds** (`P`-captor). -/
theorem fresh_strict_up {α : Type*} [PartialOrder α] {z z' p : α} (hcap : z ≤ p) (hnew : ¬ z' ≤ p) (h : z ≤ z') :
    z < z' := lt_of_le_of_ne h fun he => hnew (he ▸ hcap)

/-- **Strict progress, if a comparison holds** (`U`-captor). -/
theorem fresh_strict_down {α : Type*} [PartialOrder α] {z z' u : α} (hcap : u ≤ z) (hnew : ¬ u ≤ z')
    (h : z' ≤ z) : z' < z := lt_of_le_of_ne h fun he => hnew (he ▸ hcap)

end Mordor.GoodWordRevision
