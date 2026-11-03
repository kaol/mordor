import Mordor.FiniteSupport
import Mordor.Reach
import Mordor.Stable

/-!
# The dual finite-support boundary (round 26, §34.3z⁹⁸)

Response to the brief "dual finite-support boundary and joint activation".

* `no_least_outside` (ACC): a witness-free proper cut `D ∋ ⊥` has **no least outside element**. If `t` were one,
  `F (·) t` would map `D` into `D` (an outside value is `≥ t`, a witness), and its ascending orbit from `⊥` would
  stabilize at `x = F x t ∈ D`, a witness. This is the dual of the one-generator case (`Dᶜ = ↑t` co-principal).
* `R_nowit`: `R(F)` is a witness-free cut (`le_a`, `b_le` and the closure rules).
* `inf_compl_R_mem` (ACC): hence `⋀ (L \ R) ∈ R` whenever `R ≠ L`: the brief's target lemma, without normalization
  and without the `b`-preimage rule.
* `minimal_join_support`, `minimal_meet_support` (ACC, DCC): finite `P ⊆ R` minimal with `⋁ P ∉ R`, finite
  `Q ⊆ Rᶜ` minimal with `⋀ Q ∈ R`; every nonempty proper subface stays on its side (`join_face_membership`,
  `meet_face_membership`), and both have two distinct members.
-/

namespace Mordor.Profile

set_option linter.unusedSectionVars false

section General
variable {α : Type*} [CompleteLattice α] {F : α → α → α} {InD : α → Prop}

/-- **No least outside element** (ACC). -/
theorem no_least_outside [WellFoundedGT α] (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (nw : ∀ x, InD x → ∀ y, ¬ InD y → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (hbot : InD ⊥) {t : α} (ht : ¬ InD t)
    (hleast : ∀ y, ¬ InD y → t ≤ y) : False := by
  set f : α → α := fun x => F x t
  have hmono : Monotone f := fun _ _ h => hF _ _ _ _ h le_rfl
  have hin : ∀ n, InD (f^[n] ⊥) := by
    intro n
    induction n with
    | zero => simpa using hbot
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      by_contra hout
      exact (nw _ ih t ht).2 (hleast _ hout)
  have hasc : Monotone fun n => f^[n] ⊥ := Monotone.monotone_iterate_of_le_map hmono bot_le
  obtain ⟨_, ⟨N, rfl⟩, hmax⟩ := (wellFounded_gt (α := α)).has_min (Set.range fun n => f^[n] ⊥) ⟨_, 0, rfl⟩
  have hfix : f (f^[N] ⊥) = f^[N] ⊥ := by
    rw [← Function.iterate_succ_apply' f N ⊥]
    exact (eq_of_le_of_not_lt (hasc (Nat.le_succ N)) (hmax _ ⟨N + 1, rfl⟩)).symm
  exact (nw _ (hin N) t ht).1 hfix.le

end General

section R
variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

/-- `R(F)` is witness-free. -/
theorem R_nowit {x y : α} (hx : x ∈ R F) (hy : y ∉ R F) : ¬ F x y ≤ x ∧ ¬ y ≤ F x y := by
  obtain ⟨hD, -, ha, hb⟩ := (R_closed (F := F))
  exact ⟨fun h => hy (hb y (hD (b_le h) hx)), fun h => hy (hD (le_a h) (ha x hx))⟩

/-- **The infimum of the complement of `R` lies in `R`** (ACC). (Trivial if `R = L`, where `sInf ∅ = ⊤ ∈ R`.) -/
theorem inf_compl_R_mem [WellFoundedGT α] : sInf (R F)ᶜ ∈ R F := by
  by_contra ht
  obtain ⟨hD, h0, -, -⟩ := (R_closed (F := F))
  exact no_least_outside (F := fun x y => F x y) (InD := (· ∈ R F))
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x hx y hy => R_nowit hx hy) h0 ht
    (fun y hy => sInf_le hy)

/-- **Minimal join support** (ACC): a finite `P ⊆ R` with `⋁ P ∉ R`, minimal, so every nonempty proper subface
is in `R` (`R` is a down-set and the subface join is below `⋁ P` only up to membership, by minimality). -/
theorem minimal_join_support [WellFoundedGT α] [WellFoundedLT α] (hne : R F ≠ Set.univ) :
    ∃ P : Finset α, (↑P ⊆ R F) ∧ P.sup id ∉ R F ∧ ∀ A ⊆ P, A ≠ P → A.sup id ∈ R F := by
  classical
  have hs : sSup (R F) ∉ R F := fun h => hne ((sSup_R_mem_iff (F := F)).1 h)
  obtain ⟨t, ht, hst⟩ := sSup_finite_support (R F)
  obtain ⟨P, ⟨hPt, hP⟩, hmin⟩ := (wellFounded_lt (α := Finset α)).has_min
    {P : Finset α | P ⊆ t ∧ P.sup id ∉ R F} ⟨t, Finset.Subset.refl t, hst ▸ hs⟩
  refine ⟨P, fun x hx => ht (hPt hx), hP, fun A hAP hA => ?_⟩
  by_contra hAR
  exact hmin A ⟨hAP.trans hPt, hAR⟩ (Finset.ssubset_iff_subset_ne.2 ⟨hAP, hA⟩)

/-- **Minimal meet support** (DCC, ACC for `inf_compl_R_mem`): a finite `Q ⊆ Rᶜ` with `⋀ Q ∈ R`, minimal. -/
theorem minimal_meet_support [WellFoundedGT α] [WellFoundedLT α] :
    ∃ Q : Finset α, (↑Q ⊆ (R F)ᶜ) ∧ Q.inf id ∈ R F ∧ ∀ B ⊆ Q, B ≠ Q → B.inf id ∉ R F := by
  classical
  have ht0 := inf_compl_R_mem (F := F)
  obtain ⟨t, ht, hst⟩ := sInf_finite_support (R F)ᶜ
  obtain ⟨Q, ⟨hQt, hQ⟩, hmin⟩ := (wellFounded_lt (α := Finset α)).has_min
    {Q : Finset α | Q ⊆ t ∧ Q.inf id ∈ R F} ⟨t, Finset.Subset.refl t, hst ▸ ht0⟩
  refine ⟨Q, fun x hx => ht (hQt hx), hQ, fun B hBQ hB hBR => ?_⟩
  exact hmin B ⟨hBQ.trans hQt, hBR⟩ (Finset.ssubset_iff_subset_ne.2 ⟨hBQ, hB⟩)

end R
end Mordor.Profile
