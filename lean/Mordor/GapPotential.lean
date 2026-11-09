import Mordor.SeparatorAncestry

/-!
# The gap potential and edge-height bounds (round 26, §34.3z¹²⁵)

ChatGPT brief "interface preservation and separator ancestry", Programme B.

* `height H x`: the length of a longest strict chain below `x` in an order with `NoChain α (H + 1)` (edge-height
  `≤ H`); `chainTo_height`, `le_height`, `height_le`, `height_strictMono`.
* `cut_of_gap_parent` (**gap parent property ⇒ Cut**): if a run of the separator process has the property that every
  bad pair of a non-stuck stage has *some* bad parent at the previous stage with strictly larger rank gap
  `height y − height x`, then `F` has a witness. The bound is `2H + 1` stages (`potential_parent_stage_bound` with
  `φ = height y + (H − height x)`), and `cut_of_terminal_run` turns the terminal or stuck stage into a witness.
  The statement holds for any `H` (heights are capped at `H`); it is meaningful when `NoChain α (H + 1)`, where
  `height H` is a strictly monotone rank (`height_strictMono`). With `H = 6` it is Cut at edge-height 6, conditional on
  the parent property (∃-gap-RP, a conjecture).
-/

namespace Mordor.GapPotential
open Mordor.Ground Mordor.SeparatorStages

set_option linter.unusedSectionVars false

variable {α : Type*} [PartialOrder α] {H : ℕ} (hn : NoChain α (H + 1))

theorem chainTo_mono' : ∀ (n m : ℕ) (x : α), chainTo x n → m ≤ n → chainTo x m
  | _, 0, _, _, _ => trivial
  | 0, _ + 1, _, _, h => absurd h (by omega)
  | n + 1, m + 1, x, ⟨y, hy, hc⟩, h => ⟨y, hy, chainTo_mono' n m y hc (by omega)⟩

/-- The height of `x` (longest chain below `x`), at most `H`. -/
noncomputable def height (H : ℕ) (x : α) : ℕ := by
  classical exact Nat.findGreatest (fun k => chainTo x k) H

theorem height_le (x : α) : height H x ≤ H := by classical unfold height; exact Nat.findGreatest_le _

theorem chainTo_height (x : α) : chainTo x (height H x) := by
  classical
  unfold height
  exact Nat.findGreatest_spec (P := fun k => chainTo x k) (Nat.zero_le H) trivial

theorem le_height {x : α} {k : ℕ} (hk : k ≤ H) (h : chainTo x k) : k ≤ height H x := by
  classical
  unfold height; exact Nat.le_findGreatest hk h

include hn in
theorem height_strictMono : StrictMono (height (α := α) H) := by
  intro x y hxy
  have hc : chainTo y (height H x + 1) := ⟨x, hxy, chainTo_height x⟩
  have hle : height H x + 1 ≤ H := by
    by_contra h
    exact hn y (chainTo_mono' (height H x + 1) (H + 1) y hc (by omega))
  exact le_height hle hc

variable {β : Type*} [Lattice β] [BoundedOrder β] [DecidableEq β] [DecidableLE β] {F : β → β → β} {D : Set β}

/-- **Gap parent property ⇒ Cut.** -/
theorem cut_of_gap_parent (H : ℕ) (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) {T : ℕ → Finset β} (hr : Run F D T)
    (hgap : ∀ n x' y', Bad F D (T (n + 1)) x' y' → (∃ a b, Bad F D (T (n + 1)) a b ∧ b ≤ F a b) ∨
      ∃ x y, Bad F D (T n) x y ∧ height H y' + (H - height H x') < height H y + (H - height H x)) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  let φ : Finset β → β → β → ℕ := fun _ x y => height H y + (H - height H x)
  have hB : ∀ n x y, Bad F D (T n) x y → φ (T n) x y ≤ 2 * H := fun n x y _ => by
    have := height_le (H := H) y; have := height_le (H := H) x; simp only [φ]; omega
  rcases Mordor.SeparatorAncestry.potential_parent_stage_bound φ T hB hgap with ⟨n, -, a, b, hab, hst⟩ | hterm
  · exact ⟨a, hab.2.1, b, hab.2.2.2.1, Or.inr hst⟩
  · obtain ⟨x, hx, y, hy, hw⟩ := cut_of_terminal_run hF hD hbot htop hr (Or.inl hterm)
    exact ⟨x, hx, y, hy, hw⟩

end Mordor.GapPotential
