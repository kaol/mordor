import Mordor.RowSwitch

/-!
# The top-orbit envelope of a row-switch terminal state (round 26, §34.3z⁸⁹)

Response to the brief "globalize the row-switch terminal state".

* `orbit_le_top_orbit`: `h^[r] s ≤ h^[r] ⊤` for every start; so if the former is outside `D`, so is the latter.
* `terminal_below_top_orbit` (DCC): a pair state for the **original** pair `(x, y)` at a column `t₀ ≤ h^[r] ⊤`, where
  `h = F (pₓ ⊓ p_y)` (e.g. the last outside point of an A2 second orbit at depth `r`), runs through `switch_terminal` to a
  terminal state `(x', y', t')`, recorded separately, with `t' ≤ v = h^[r] ⊤ ∉ D`. The envelope is monotonicity: it
  holds for every column of depth `r` in any `h`-orbit.
* `terminal_entry_row_output`: with `e = F m t' ≤ p_y`, `q = F p_y t' ∉ D`, `t' ≤ v ∉ D`, the entry value used as a row
  gives `Q = F p_y v ∉ D`, `R = F e v ≤ Q`, `R ≰ e`, `v ≰ R`, so `v ⊓ R < v`.
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

theorem orbit_le_top_orbit {α : Type*} [Lattice α] [BoundedOrder α] {h : α → α} (hh : Monotone h) (s : α)
    (r : ℕ) : h^[r] s ≤ h^[r] ⊤ :=
  (hh.iterate r) le_top

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF nw in
/-- **The terminal state lies under the top orbit of the original pair row.** -/
theorem terminal_below_top_orbit [WellFoundedLT α] {x y : ι} (hxy : x ≠ y) {s : α} {r : ℕ}
    (ht₀ : ¬ ∃ i, (F (p x ⊓ p y))^[r] s ≤ p i)
    (he₀ : F (p x ⊓ p y) ((F (p x ⊓ p y))^[r] s) ≤ p y) :
    (¬ ∃ i, (F (p x ⊓ p y))^[r] ⊤ ≤ p i) ∧
    ∃ t' x' y', t' ≤ (F (p x ⊓ p y))^[r] s ∧ t' ≤ (F (p x ⊓ p y))^[r] ⊤ ∧ (¬ ∃ i, t' ≤ p i) ∧ x' ≠ y' ∧
      F (p x' ⊓ p y') t' ≤ p y' ∧ (¬ ∃ k, F (p y') t' ≤ p k) ∧ ∃ k, t' ⊓ F (p y') t' ≤ p k := by
  have hmono : Monotone (F (p x ⊓ p y)) := fun _ _ h => hF _ _ _ _ le_rfl h
  have henv := orbit_le_top_orbit hmono s r
  refine ⟨fun ⟨i, hi⟩ => ht₀ ⟨i, henv.trans hi⟩, ?_⟩
  obtain ⟨t', x', y', h1, h2⟩ := switch_terminal hF p nw _ ht₀ x y hxy he₀
  exact ⟨t', x', y', h1, h1.trans henv, h2⟩

include hF nw in
/-- **The terminal entry value as a row.** -/
theorem terminal_entry_row_output {x y : ι} {t' v : α} (htv : t' ≤ v) (hv : ¬ ∃ i, v ≤ p i)
    (he : F (p x ⊓ p y) t' ≤ p y) (hq : ¬ ∃ k, F (p y) t' ≤ p k) :
    (¬ ∃ k, F (p y) v ≤ p k) ∧ F (F (p x ⊓ p y) t') v ≤ F (p y) v ∧
      ¬ F (F (p x ⊓ p y) t') v ≤ F (p x ⊓ p y) t' ∧ ¬ v ≤ F (F (p x ⊓ p y) t') v ∧
      v ⊓ F (F (p x ⊓ p y) t') v < v := by
  have hqQ : F (p y) t' ≤ F (p y) v := hF _ _ _ _ le_rfl htv
  have heD : ∃ i, F (p x ⊓ p y) t' ≤ p i := ⟨y, he⟩
  obtain ⟨n1, n2⟩ := nw _ heD v hv
  exact ⟨fun ⟨k, hk⟩ => hq ⟨k, hqQ.trans hk⟩, hF _ _ _ _ he le_rfl, n1, n2, meet_proj_lt p nw heD hv⟩

end Mordor.Profile
