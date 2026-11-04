import Mordor.ExtremalSupport

/-!
# The response palette (round 26, §34.3z¹⁰⁴)

Response to the brief "missing-petal filtration and paired orbit endpoints". `D = ⋃ᵢ ↓gᵢ` (`κ` finite),
`m = ⨅ g`. The palette of a column is `Π(y) = {i | F m y ≤ gᵢ}`, the label set of the meet row; `labels x y` is the
label set of the row `x`.

* `palette_proper` (no witness at `m`), `palette_response_subset` (`m ≤ x`), `palette_antitone` (column monotonicity).
* `palette_filtration`: along a descending column sequence the palettes increase.
* `palette_changes_bound`: the number of change times `n < N` (`Π(yₙ) ≠ Π(yₙ₊₁)`) is at most `|κ| - 1`, using only
  `y_N ∉ D` (no entry information); it is `count_strict_increases` for the monotone `n ↦ |Π(yₙ)|`.
A palette change is an event about the meet row only; it is unrelated to any row orbit entering `D`.
-/

namespace Mordor.Profile

set_option linter.unusedSectionVars false

/-- A monotone `f : ℕ → ℕ` increases strictly at most `f N - f 0` times before `N`. -/
theorem count_strict_increases (f : ℕ → ℕ) (hf : Monotone f) (N : ℕ) :
    ((Finset.range N).filter fun n => f n < f (n + 1)).card + f 0 ≤ f N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    have hN : f N ≤ f (N + 1) := hf (Nat.le_succ N)
    split_ifs with h
    · have := Finset.card_insert_le N ((Finset.range N).filter fun n => f n < f (n + 1)); omega
    · omega

section Palette

variable {α : Type*} [CompleteLattice α] {κ : Type*} [Fintype κ] [DecidableEq κ]

open Classical in
/-- Label set of the row `x` at the column `y`. -/
noncomputable def labels (F : α → α → α) (g : κ → α) (x y : α) : Finset κ :=
  Finset.univ.filter fun i => F x y ≤ g i

/-- The palette: label set of the meet row `⨅ g`. -/
noncomputable def palette (F : α → α → α) (g : κ → α) (y : α) : Finset κ := labels F g (Finset.univ.inf g) y

theorem mem_labels {F : α → α → α} {g : κ → α} {x y : α} {i : κ} : i ∈ labels F g x y ↔ F x y ≤ g i := by
  classical
  unfold labels; simp

variable {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (g : κ → α)
  (nw' : ∀ x, (∃ i, x ≤ g i) → ∀ y, ¬ (∃ i, y ≤ g i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include nw' in
/-- **The palette of an outside column is proper.** -/
theorem palette_proper [Nonempty κ] {y : α} (hy : ¬ ∃ i, y ≤ g i) : palette F g y ≠ Finset.univ := by
  intro h
  obtain ⟨i₀⟩ := ‹Nonempty κ›
  refine (nw' _ ⟨i₀, Finset.inf_le (Finset.mem_univ i₀)⟩ y hy).1 (Finset.le_inf fun i _ => ?_)
  have : i ∈ palette F g y := h ▸ Finset.mem_univ i
  exact mem_labels.1 this

include nw' in
theorem palette_card_lt [Nonempty κ] {y : α} (hy : ¬ ∃ i, y ≤ g i) :
    (palette F g y).card < Fintype.card κ :=
  (Finset.card_lt_iff_ne_univ _).2 (palette_proper g nw' hy)

include hF in
/-- **Rows above the meet only use palette labels.** -/
theorem palette_response_subset {x y : α} (hx : Finset.univ.inf g ≤ x) : labels F g x y ⊆ palette F g y :=
  fun _ hi => mem_labels.2 ((hF _ _ _ _ hx le_rfl).trans (mem_labels.1 hi))

include hF in
/-- **Palettes are antitone in the column.** -/
theorem palette_antitone {y y' : α} (h : y ≤ y') : palette F g y' ⊆ palette F g y :=
  fun _ hi => mem_labels.2 ((hF _ _ _ _ le_rfl h).trans (mem_labels.1 hi))

include hF in
/-- **Palette filtration** along a descending column sequence. -/
theorem palette_filtration {y : ℕ → α} (hy : Antitone y) : Monotone fun n => palette F g (y n) :=
  fun _ _ h => palette_antitone hF g (hy h)

include hF nw' in
/-- **At most `|κ| - 1` palette changes** before a time `N` with `y_N ∉ D`. -/
theorem palette_changes_bound [Nonempty κ] {y : ℕ → α} (hy : Antitone y) (N : ℕ) (hN : ¬ ∃ i, y N ≤ g i) :
    ((Finset.range N).filter fun n => palette F g (y n) ≠ palette F g (y (n + 1))).card ≤ Fintype.card κ - 1 := by
  have hmono := palette_filtration hF g hy
  have hf : Monotone fun n => (palette F g (y n)).card := fun a b h => Finset.card_le_card (hmono h)
  have hcount := count_strict_increases _ hf N
  have hsub : ((Finset.range N).filter fun n => palette F g (y n) ≠ palette F g (y (n + 1))) ⊆
      (Finset.range N).filter fun n => (palette F g (y n)).card < (palette F g (y (n + 1))).card := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hmono (Nat.le_succ n), hn.2⟩)⟩
  have hlt := palette_card_lt g nw' hN
  have := Finset.card_le_card hsub
  simp only at hcount
  omega

end Palette

end Mordor.Profile
