import Mordor.PairedEndpoints
import Mathlib.Data.Fintype.Option

/-!
# No equal-time-two entry of three generator orbits (round 26, §34.3z¹⁰⁴)

Found by z3 while testing the brief's endpoint-meet experiment: with the pairwise and triple meets of the generator
endpoints added as columns, the generator-orbit profile `(2, 2, 2)` from a common contracting column became UNSAT.

**Theorem** (`no_equal_time_two`, three generators, no chain condition). Let `s ∉ D` with `F gᵢ s ≤ s` for all `i`.
It is impossible that every `uᵢ = F gᵢ s` is outside `D` while every `yᵢ = F gᵢ uᵢ` is inside `D`.

Proof. Write `v_T = ⨅_{j∈T} uⱼ`, `m_T = ⨅_{j∈T} gⱼ`. Two monotonicity facts carry everything:
`F m_T s ≤ v_T` (each `F m_T s ≤ F gⱼ s`), and for `i ∈ T` and a column `c ≤ uᵢ`, `F m_T c ≤ yᵢ ≤ g_{σ i}`
(`σ i ≠ i` a label of `yᵢ`, by no witness). The triple meet `v_{123}` is in `D` (`column_lemma`: every generator takes
it into `D`); give it a label `t`, and give each pairwise meet `v_P` a label if it lies in `D`. No witness at the rows
`m₁₂₃` (columns `uᵢ`, outside `v_P`) and `m_P` (columns `uₗ`, `l ∈ P`; and `v_P` when outside) then excludes every
label assignment: a finite check (`eq2_comb`, `decide`).
-/

namespace Mordor.Profile

set_option linter.unusedSectionVars false

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
/-- The label combinatorics of `no_equal_time_two`. -/
theorem eq2_comb : ∀ (σ : Fin 3 → Fin 3) (t : Fin 3) (d : Fin 3 → Option (Fin 3)), (∀ i, σ i ≠ i) →
    (∀ i, ¬ ∀ a, a = t ∨ a = σ i ∨ ∃ k, d k = some a) →
    (∀ k τ, d k = some τ → ∀ l, l ≠ k → ¬ ∀ a, a ≠ k → (a = τ ∨ a = σ l)) →
    (∀ k, d k = none → ¬ ∀ a, a ≠ k → ∃ i, i ≠ k ∧ a = σ i) →
    (∀ k, d k = none → ¬ ∀ a, a = t ∨ (∃ i, i ≠ k ∧ a = σ i) ∨ ∃ k', d k' = some a) → False := by
  decide

/-- **No equal-time-two entry** of three generator orbits from a common contracting column. -/
theorem no_equal_time_two {α : Type*} [CompleteLattice α] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (g : Fin 3 → α)
    (nw' : ∀ x, (∃ i, x ≤ g i) → ∀ y, ¬ (∃ i, y ≤ g i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {s : α} (hgs : ∀ i, F (g i) s ≤ s) (hout : ∀ i, ¬ ∃ k, F (g i) s ≤ g k)
    (hin : ∀ i, ∃ k, F (g i) (F (g i) s) ≤ g k) : False := by
  classical
  set u : Fin 3 → α := fun i => F (g i) s with hu_def
  have hus : ∀ i, u i ≤ s := hgs
  have hσ' : ∀ i, ∃ k, k ≠ i ∧ F (g i) (u i) ≤ g k := fun i => by
    obtain ⟨k, hk⟩ := hin i
    exact ⟨k, fun h => (nw' (g i) ⟨i, le_rfl⟩ (u i) (hout i)).1 (h ▸ hk), hk⟩
  choose σ hσne hσ using hσ'
  have M1 : ∀ T : Finset (Fin 3), F (T.inf g) s ≤ T.inf u := fun T =>
    Finset.le_inf fun j hj => hF _ _ _ _ (Finset.inf_le hj) le_rfl
  have My : ∀ (T : Finset (Fin 3)) i, i ∈ T → ∀ c, c ≤ u i → F (T.inf g) c ≤ g (σ i) := fun T i hi c hc =>
    (hF _ _ _ _ (Finset.inf_le hi) hc).trans (hσ i)
  have hv3 : ∃ t, Finset.univ.inf u ≤ g t := by
    by_contra h
    obtain ⟨j, hj⟩ := Mordor.Crossing.column_lemma hF g h nw'
    exact hj ⟨σ j, (hF _ _ _ _ le_rfl (Finset.inf_le (Finset.mem_univ j))).trans (hσ j)⟩
  obtain ⟨t, ht⟩ := hv3
  let d : Fin 3 → Option (Fin 3) := fun k =>
    if h : ∃ τ, (Finset.univ.erase k).inf u ≤ g τ then some (Classical.choose h) else none
  have hdsome : ∀ k τ, d k = some τ → (Finset.univ.erase k).inf u ≤ g τ := by
    intro k τ h
    by_cases hh : ∃ τ, (Finset.univ.erase k).inf u ≤ g τ
    · have : d k = some (Classical.choose hh) := dif_pos hh
      rw [this, Option.some.injEq] at h
      exact h ▸ Classical.choose_spec hh
    · have : d k = none := dif_neg hh
      rw [this] at h; cases h
  have hdnone : ∀ k, d k = none → ¬ ∃ τ, (Finset.univ.erase k).inf u ≤ g τ := by
    intro k h hh
    have : d k = some (Classical.choose hh) := dif_pos hh
    rw [this] at h; cases h
  have M3s : ∀ c, c ≤ s → ∀ a, (∃ k, d k = some a) → F (Finset.univ.inf g) c ≤ g a := by
    rintro c hc a ⟨k, hk⟩
    exact (hF _ _ _ _ (Finset.inf_mono (Finset.subset_univ (Finset.univ.erase k))) hc).trans
      ((M1 _).trans (hdsome k a hk))
  have M3t : ∀ c, c ≤ s → F (Finset.univ.inf g) c ≤ g t := fun c hc =>
    (hF _ _ _ _ le_rfl hc).trans ((M1 Finset.univ).trans ht)
  have hm3 : ∃ i, Finset.univ.inf g ≤ g i := ⟨0, Finset.inf_le (Finset.mem_univ 0)⟩
  have hmem : ∀ {i k : Fin 3}, i ≠ k → i ∈ Finset.univ.erase k := fun h => Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩
  refine eq2_comb σ t d hσne ?_ ?_ ?_ ?_
  · intro i hcov
    refine (nw' _ hm3 (u i) (hout i)).1 (Finset.le_inf fun a _ => ?_)
    rcases hcov a with h | h | h
    · rw [h]; exact M3t (u i) (hus i)
    · rw [h]; exact My Finset.univ i (Finset.mem_univ i) (u i) le_rfl
    · exact M3s (u i) (hus i) a h
  · intro k τ hk l hlk hcov
    refine (nw' _ ⟨l, Finset.inf_le (hmem hlk)⟩ (u l) (hout l)).1 (Finset.le_inf fun a ha => ?_)
    rcases hcov a (Finset.ne_of_mem_erase ha) with h | h
    · rw [h]; exact (hF _ _ _ _ le_rfl (hus l)).trans ((M1 _).trans (hdsome k _ hk))
    · rw [h]; exact My _ l (hmem hlk) (u l) le_rfl
  · intro k hk hcov
    obtain ⟨j, hj⟩ := exists_ne k
    refine (nw' _ ⟨j, Finset.inf_le (hmem hj)⟩ _ (hdnone k hk)).1 (Finset.le_inf fun a ha => ?_)
    obtain ⟨i, hik, h⟩ := hcov a (Finset.ne_of_mem_erase ha)
    rw [h]; exact My _ i (hmem hik) _ (Finset.inf_le (hmem hik))
  · intro k hk hcov
    obtain ⟨j, hj⟩ := exists_ne k
    have hvs : (Finset.univ.erase k).inf u ≤ s := (Finset.inf_le (hmem hj)).trans (hus j)
    refine (nw' _ hm3 _ (hdnone k hk)).1 (Finset.le_inf fun a _ => ?_)
    rcases hcov a with h | ⟨i, hik, h⟩ | h
    · rw [h]; exact M3t _ hvs
    · rw [h]; exact My Finset.univ i (Finset.mem_univ i) _ (Finset.inf_le (hmem hik))
    · exact M3s _ hvs a h

end Mordor.Profile
