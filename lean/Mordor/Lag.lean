import Mordor.Net

/-!
# Lagged comparison of two starting columns (round 26, §34.3z⁸⁷)

Response to the brief "cross-orbit comparison without contraction". `h` monotone, `D` down-closed.

* `iterate_succ_le_of_map_le` (L): `h s ≤ s'` gives `h^[n+1] s ≤ h^[n] s'` for all `n`. No contraction.
* `lagged_time`, `lagged_label`: if the `h`-orbit of `s` enters at step `n + 1` and that of `s'` at step `n' + 1`, then
  `n ≤ n' + 1`; in the case `n = n' + 1` (A1, entry one step earlier) the endpoint from `s'` is above the endpoint from
  `s`, so its labels are among those of `s`'s endpoint. Otherwise (A2) the column `h^[n] s'` is outside `D` and above the
  endpoint from `s`.
* `upper_bound_kills_A2`: with the sandwich's upper bound `h^[n] s' ≤ h^[n] s` (e.g. from `s' ≤ s`), A2 at the entry
  time of `s` is impossible. This is the only place contraction enters `FGTwo.sandwich`.
* `lastpoint_meet` (M) and `lastpoint_meet_same`: for two starts whose `F (pᵢ ⊓ pⱼ)`-orbits enter below `pᵢ` and `pⱼ`
  respectively, the meet of the last points is in `D`; with equal labels the meet, if outside, has an immediate entry
  into that petal. Both are monotonicity at the single column `w_s ⊓ w_t`.
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

section Lag
variable {α : Type*} [Lattice α] {h : α → α} {InD : α → Prop}

/-- **(L)** -/
theorem iterate_succ_le_of_map_le (hh : Monotone h) {s s' : α} (hstep : h s ≤ s') (n : ℕ) :
    h^[n + 1] s ≤ h^[n] s' := by
  rw [Function.iterate_succ_apply]; exact (hh.iterate n) hstep

theorem lagged_time (hh : Monotone h) (hdown : ∀ x y, x ≤ y → InD y → InD x) {s s' : α} (hstep : h s ≤ s')
    {n n' : ℕ} (hE : EntersAt h InD s n) (hE' : EntersAt h InD s' n') : n ≤ n' + 1 := by
  by_contra hlt
  exact hE.1 (n' + 2) (by omega) (hdown _ _ (by
    have := iterate_succ_le_of_map_le hh hstep (n' + 1); simpa using this) hE'.2)

/-- In the A1 case the second endpoint lies above the first. -/
theorem lagged_label (hh : Monotone h) {s s' : α} (hstep : h s ≤ s') (n : ℕ) :
    h^[n + 2] s ≤ h^[n + 1] s' :=
  iterate_succ_le_of_map_le hh hstep (n + 1)

/-- **The upper bound kills A2.** If `s` enters at step `n + 1` and `h^[n] s' ≤ h^[n] s`, then `h^[n+1] s'` is in `D`:
the second orbit has entered by then. -/
theorem upper_bound_kills_A2 (hh : Monotone h) (hdown : ∀ x y, x ≤ y → InD y → InD x) {s s' : α} {n : ℕ}
    (hE : EntersAt h InD s n) (hup : h^[n] s' ≤ h^[n] s) : InD (h^[n + 1] s') := by
  rw [Function.iterate_succ_apply']
  exact hdown _ _ (hh hup) (by rw [← Function.iterate_succ_apply' h n s]; exact hE.2)

end Lag

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF nw in
/-- **(M)** Opposite labels: the meet of the last points lies in `D`. -/
theorem lastpoint_meet {i j : ι} {ws wt : α} (hs : F (p i ⊓ p j) ws ≤ p i)
    (ht : F (p i ⊓ p j) wt ≤ p j) : ∃ k, ws ⊓ wt ≤ p k := by
  by_contra hz
  have h1 : F (p i ⊓ p j) (ws ⊓ wt) ≤ p i := (hF _ _ _ _ le_rfl inf_le_left).trans hs
  have h2 : F (p i ⊓ p j) (ws ⊓ wt) ≤ p j := (hF _ _ _ _ le_rfl inf_le_right).trans ht
  exact (nw _ ⟨i, inf_le_left⟩ _ hz).1 (le_inf h1 h2)

include hF in
/-- Equal labels: the meet, if outside, enters that petal at once. -/
theorem lastpoint_meet_same {i j : ι} {ws wt : α} (hs : F (p i ⊓ p j) ws ≤ p i) :
    F (p i ⊓ p j) (ws ⊓ wt) ≤ p i :=
  (hF _ _ _ _ le_rfl inf_le_left).trans hs

end Mordor.Profile
