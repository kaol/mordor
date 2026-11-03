import Mordor.ReciprocalOrbits

/-!
# Global reciprocal aggregation (round 26, §34.3z¹⁰⁰)

Response to the brief "global reciprocal aggregation and common fixed-point boundaries". `D` a witness-free down-set
with `⊥ ∈ D`, `⊤ ∉ D`; `F` monotone; `Φ y = ⨆_{x ∈ D} F x y`, `Ψ x = ⨅_{y ∉ D} F x y`.

* `aggregate_row_mono`, `aggregate_column_mono`.
* `aggregate_row_preserves_complement` (ACC): `y ∉ D → Φ y ∉ D` (the column orbit along `y` leaves `D`).
* `aggregate_column_preserves_D` (DCC): `x ∈ D → Ψ x ∈ D` (the row orbit along `x` enters `D`).
* `aggregate_row_fixedpoint` (DCC + ACC): the `Φ`-iteration from `⊤` stabilizes at `s = Φ s ∉ D`, so `F x s ≤ s`
  for every `x ∈ D`. `aggregate_column_fixedpoint` (ACC + DCC): from `⊥`, `r = Ψ r ∈ D`, `r ≤ F r y` for every
  `y ∉ D`.
* `common_boundary_strict`: `r < F r s < s`.
* `finite_row_response_support`, `finite_column_response_support`: finite supports `s = ⨆_{p∈P} F p s`,
  `r = ⨅_{q∈Q} F r q`; `no_singleton_support`: no single row (column) supports `s` (`r`).
* `rectangularization_dichotomy`: `p ⊔ r ∈ D` (then `F p s ≤ F (p ⊔ r) s ≤ s`) or `p ⊔ r ∉ D`; dually for `q ⊓ s`.
* The pair can be **degenerate**: `⊤` is already a common contracting column and `⊥` a common expanding row, and if
  `Φ ⊤ = ⊤`, `Ψ ⊥ = ⊥` then `s = ⊤`, `r = ⊥` (`degenerate_boundary`).
-/

namespace Mordor.Profile

set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] {F : α → α → α} {InD : α → Prop}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
  (hdown : ∀ x y, x ≤ y → InD y → InD x)
  (nw : ∀ x, InD x → ∀ y, ¬ InD y → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

/-- The aggregate row map. -/
noncomputable def Φagg (F : α → α → α) (InD : α → Prop) (y : α) : α := ⨆ x : {x // InD x}, F x y
/-- The aggregate column map. -/
noncomputable def Ψagg (F : α → α → α) (InD : α → Prop) (x : α) : α := ⨅ y : {y // ¬ InD y}, F x y

include hF in
theorem aggregate_row_mono : Monotone (Φagg F InD) := fun _ _ h =>
  iSup_mono fun _ => hF _ _ _ _ le_rfl h

include hF in
theorem aggregate_column_mono : Monotone (Ψagg F InD) := fun _ _ h =>
  iInf_mono fun _ => hF _ _ _ _ h le_rfl

include hF hdown nw in
/-- **Lemma A** (ACC). -/
theorem aggregate_row_preserves_complement [WellFoundedGT α] (hbot : InD ⊥) {y : α} (hy : ¬ InD y) :
    ¬ InD (Φagg F InD y) := by
  obtain ⟨N, hN, hlt⟩ := column_orbit_exits hF nw hy
  cases N with
  | zero => exact absurd (by simpa [colOrbit] using hbot) hN
  | succ n =>
    have hstep : colOrbit F y (n + 1) = F (colOrbit F y n) y := by
      unfold colOrbit; rw [Function.iterate_succ_apply']
    intro h
    exact hN (hdown _ _ (hstep ▸ le_iSup (fun x : {x // InD x} => F x y) ⟨_, hlt n (Nat.lt_succ_self n)⟩) h)

include hF hdown nw in
/-- **Lemma B** (DCC). -/
theorem aggregate_column_preserves_D [WellFoundedLT α] (htop : ¬ InD ⊤) {x : α} (hx : InD x) :
    InD (Ψagg F InD x) := by
  obtain ⟨M, hM, hlt⟩ := row_orbit_enters hF nw hx
  cases M with
  | zero => exact absurd (by simpa [rowOrbit] using hM) htop
  | succ n =>
    have hstep : rowOrbit F x (n + 1) = F x (rowOrbit F x n) := by
      unfold rowOrbit; rw [Function.iterate_succ_apply']
    exact hdown _ _ (hstep ▸ iInf_le (fun y : {y // ¬ InD y} => F x y) ⟨_, hlt n (Nat.lt_succ_self n)⟩) hM

include hF hdown nw in
/-- **The common contracting column** (ACC for Lemma A, DCC for stabilization). -/
theorem aggregate_row_fixedpoint [WellFoundedGT α] [WellFoundedLT α] (hbot : InD ⊥) (htop : ¬ InD ⊤) :
    ∃ s, ¬ InD s ∧ Φagg F InD s = s ∧ ∀ x, InD x → F x s ≤ s := by
  set Φ := Φagg F InD
  have hmono : Monotone Φ := aggregate_row_mono hF
  have hanti : Antitone fun n => Φ^[n] ⊤ := Monotone.antitone_iterate_of_map_le hmono le_top
  have hout : ∀ n, ¬ InD (Φ^[n] ⊤) := fun n => by
    induction n with
    | zero => simpa using htop
    | succ n ih => rw [Function.iterate_succ_apply']; exact aggregate_row_preserves_complement hF hdown nw hbot ih
  obtain ⟨_, ⟨N, rfl⟩, hmin⟩ := (wellFounded_lt (α := α)).has_min (Set.range fun n => Φ^[n] ⊤) ⟨_, 0, rfl⟩
  have e := eq_of_le_of_not_lt (hanti (Nat.le_succ N)) (hmin _ ⟨N + 1, rfl⟩)
  have hfix : Φ (Φ^[N] ⊤) = Φ^[N] ⊤ := by rw [← Function.iterate_succ_apply' Φ N ⊤]; exact e
  refine ⟨_, hout N, hfix, fun x hx => ?_⟩
  exact (le_iSup (fun x : {x // InD x} => F x (Φ^[N] ⊤)) ⟨x, hx⟩).trans hfix.le

include hF hdown nw in
/-- **The common expanding row** (DCC for Lemma B, ACC for stabilization). -/
theorem aggregate_column_fixedpoint [WellFoundedGT α] [WellFoundedLT α] (hbot : InD ⊥) (htop : ¬ InD ⊤) :
    ∃ r, InD r ∧ Ψagg F InD r = r ∧ ∀ y, ¬ InD y → r ≤ F r y := by
  set Ψ := Ψagg F InD
  have hmono : Monotone Ψ := aggregate_column_mono hF
  have hasc : Monotone fun n => Ψ^[n] ⊥ := Monotone.monotone_iterate_of_le_map hmono bot_le
  have hin : ∀ n, InD (Ψ^[n] ⊥) := fun n => by
    induction n with
    | zero => simpa using hbot
    | succ n ih => rw [Function.iterate_succ_apply']; exact aggregate_column_preserves_D hF hdown nw htop ih
  obtain ⟨_, ⟨N, rfl⟩, hmax⟩ := (wellFounded_gt (α := α)).has_min (Set.range fun n => Ψ^[n] ⊥) ⟨_, 0, rfl⟩
  have e := eq_of_le_of_not_lt (hasc (Nat.le_succ N)) (hmax _ ⟨N + 1, rfl⟩)
  have hfix : Ψ (Ψ^[N] ⊥) = Ψ^[N] ⊥ := by rw [← Function.iterate_succ_apply' Ψ N ⊥]; exact e.symm
  refine ⟨_, hin N, hfix, fun y hy => ?_⟩
  exact hfix.symm.le.trans (iInf_le (fun y : {y // ¬ InD y} => F (Ψ^[N] ⊥) y) ⟨y, hy⟩)

include nw in
/-- **The strict interior response** `r < F r s < s`. -/
theorem common_boundary_strict {r s : α} (hr : InD r) (hs : ¬ InD s) (hrs : r ≤ F r s) (hsr : F r s ≤ s) :
    r < F r s ∧ F r s < s :=
  ⟨lt_of_le_of_ne hrs fun e => (nw r hr s hs).1 e.ge, lt_of_le_of_ne hsr fun e => (nw r hr s hs).2 e.ge⟩

/-- **Finite row-response support** (ACC). -/
theorem finite_row_response_support [WellFoundedGT α] (s : α) :
    ∃ P : Finset {x // InD x}, Φagg F InD s = P.sup fun x => F x s :=
  iSup_finite_support _

/-- **Finite column-response support** (DCC). -/
theorem finite_column_response_support [WellFoundedLT α] (r : α) :
    ∃ Q : Finset {y // ¬ InD y}, Ψagg F InD r = Q.inf fun y => F r y :=
  iInf_finite_support _

include nw in
/-- **No single row supports `s`, no single column supports `r`.** -/
theorem no_singleton_support {r s : α} (hr : InD r) (hs : ¬ InD s) :
    (∀ p, InD p → F p s ≠ s) ∧ (∀ q, ¬ InD q → F r q ≠ r) :=
  ⟨fun p hp e => (nw p hp s hs).2 e.ge, fun q hq e => (nw r hr q hq).1 e.le⟩

include hF in
/-- **Rectangularization dichotomy.** -/
theorem rectangularization_dichotomy {r s p q : α} (hsc : ∀ x, InD x → F x s ≤ s)
    (hre : ∀ y, ¬ InD y → r ≤ F r y) :
    (InD (p ⊔ r) ∧ F p s ≤ F (p ⊔ r) s ∧ F (p ⊔ r) s ≤ s ∨ ¬ InD (p ⊔ r)) ∧
    (¬ InD (q ⊓ s) ∧ r ≤ F r (q ⊓ s) ∧ F r (q ⊓ s) ≤ F r q ∨ InD (q ⊓ s)) := by
  constructor
  · by_cases h : InD (p ⊔ r)
    · exact Or.inl ⟨h, hF _ _ _ _ le_sup_left le_rfl, hsc _ h⟩
    · exact Or.inr h
  · by_cases h : InD (q ⊓ s)
    · exact Or.inr h
    · exact Or.inl ⟨h, hre _ h, hF _ _ _ _ le_rfl inf_le_left⟩

/-- **The pair can be degenerate.** `⊤` is a common contracting column and `⊥` a common expanding row for every `F`;
if `Φ ⊤ = ⊤` and `Ψ ⊥ = ⊥` the iterations stop at once and `(r, s) = (⊥, ⊤)`. -/
theorem degenerate_boundary (F : α → α → α) :
    (∀ x, F x ⊤ ≤ ⊤) ∧ (∀ y, ⊥ ≤ F ⊥ y) := ⟨fun _ => le_top, fun _ => bot_le⟩

end Mordor.Profile
