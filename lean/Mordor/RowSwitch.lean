import Mordor.Lag

/-!
# Row switching at an A2 entry (round 26, §34.3z⁸⁸)

Response to the brief "row switching at an A2 entry". A *pair state* `(x, y, t)`: `x ≠ y`, `t ∉ D`,
`F (pₓ ⊓ p_y) t ≤ p_y`.

* `switched_row_escape`: `z = F p_y t` is below neither `pₓ` nor `p_y`, and `t ≰ z`.
* `switched_meet_strict`, `switched_meet_entry`: `t ⊓ z < t`, and the pair entry is inherited by `t ⊓ z`.
* `third_petal_switch`: if `z ≤ p_k`, then `k ≠ x, y` and `(y, k, t)` is again a pair state, at the **same** column.
* `switch_bounded`: at a fixed column, switching cannot continue forever: the generators `y` of valid states at `t`
  would form a closed row set (`no_closed_rows`). So some valid state has `F p_y t ∉ D`.
* `switch_terminal` (DCC): every pair state leads, by switches at a column and strict clipped descents, to a terminal
  state `(x', y', t')`, `t' ≤ t`, with `F p_{y'} t' ∉ D` and `t' ⊓ F p_{y'} t' ∈ D`. This is the frontier terminal
  pattern of §34.3z⁸⁴ with the row fixed at `p_{y'}` (class L of §34.3z⁸⁶), carrying the pair entry
  `F (p_{x'} ⊓ p_{y'}) t' ≤ p_{y'}`.
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF nw in
theorem switched_row_escape {x y : ι} {t : α} (ht : ¬ ∃ i, t ≤ p i) (he : F (p x ⊓ p y) t ≤ p y) :
    ¬ F (p y) t ≤ p x ∧ ¬ F (p y) t ≤ p y ∧ ¬ t ≤ F (p y) t := by
  have hle : F (p x ⊓ p y) t ≤ F (p y) t := hF _ _ _ _ inf_le_right le_rfl
  refine ⟨fun h => (nw _ ⟨x, inf_le_left⟩ t ht).1 (le_inf (hle.trans h) he), (nw _ ⟨y, le_rfl⟩ t ht).1,
    (nw _ ⟨y, le_rfl⟩ t ht).2⟩

include nw in
theorem switched_meet_strict {y : ι} {t : α} (ht : ¬ ∃ i, t ≤ p i) : t ⊓ F (p y) t < t :=
  meet_proj_lt p nw ⟨y, le_rfl⟩ ht

include hF in
theorem switched_meet_entry {x y : ι} {t : α} (he : F (p x ⊓ p y) t ≤ p y) :
    F (p x ⊓ p y) (t ⊓ F (p y) t) ≤ p y :=
  (hF _ _ _ _ le_rfl inf_le_left).trans he

include hF nw in
/-- **Third-petal switch**, at the same column. -/
theorem third_petal_switch {x y k : ι} {t : α} (ht : ¬ ∃ i, t ≤ p i) (he : F (p x ⊓ p y) t ≤ p y)
    (hk : F (p y) t ≤ p k) : k ≠ x ∧ k ≠ y ∧ F (p y ⊓ p k) t ≤ p k := by
  obtain ⟨h1, h2, -⟩ := switched_row_escape hF p nw ht he
  exact ⟨fun e => h1 (e ▸ hk), fun e => h2 (e ▸ hk), (hF _ _ _ _ inf_le_left le_rfl).trans hk⟩

include hF nw in
/-- **Switching at a column is bounded**: some valid pair state at `t` has its switched row value outside `D`. -/
theorem switch_bounded {t : α} (ht : ¬ ∃ i, t ≤ p i) {x₀ y₀ : ι} (hxy₀ : x₀ ≠ y₀)
    (he₀ : F (p x₀ ⊓ p y₀) t ≤ p y₀) :
    ∃ x y, x ≠ y ∧ F (p x ⊓ p y) t ≤ p y ∧ ¬ ∃ k, F (p y) t ≤ p k := by
  classical
  by_contra hall
  push_neg at hall
  let S : Finset ι := Finset.univ.filter (fun y => ∃ x, x ≠ y ∧ F (p x ⊓ p y) t ≤ p y)
  refine no_closed_rows hF p ht nw S ⟨y₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, x₀, hxy₀, he₀⟩⟩ fun y hy => ?_
  obtain ⟨x, hxy, he⟩ := (Finset.mem_filter.1 hy).2
  obtain ⟨k, hk⟩ := hall x y hxy he
  obtain ⟨-, hky, hk'⟩ := third_petal_switch hF p nw ht he hk
  exact ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ _, y, hky.symm, hk'⟩, hk⟩

include hF nw in
/-- **Terminal state of the switching system** (DCC). -/
theorem switch_terminal [WellFoundedLT α] :
    ∀ t, (¬ ∃ i, t ≤ p i) → ∀ x y, x ≠ y → F (p x ⊓ p y) t ≤ p y →
      ∃ t' x' y', t' ≤ t ∧ (¬ ∃ i, t' ≤ p i) ∧ x' ≠ y' ∧ F (p x' ⊓ p y') t' ≤ p y' ∧
        (¬ ∃ k, F (p y') t' ≤ p k) ∧ ∃ k, t' ⊓ F (p y') t' ≤ p k := by
  intro t
  induction t using WellFoundedLT.induction with
  | _ t ih =>
    intro ht x₀ y₀ hxy₀ he₀
    obtain ⟨x, y, hxy, he, hout⟩ := switch_bounded hF p nw ht hxy₀ he₀
    by_cases hd : ∃ k, t ⊓ F (p y) t ≤ p k
    · exact ⟨t, x, y, le_rfl, ht, hxy, he, hout, hd⟩
    · obtain ⟨t', x', y', h1, h2⟩ :=
        ih _ (switched_meet_strict p nw ht) hd x y hxy (switched_meet_entry hF p he)
      exact ⟨t', x', y', h1.trans inf_le_left, h2⟩

end Mordor.Profile
