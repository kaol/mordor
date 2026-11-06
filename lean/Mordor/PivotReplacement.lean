import Mordor.LocalizedCut

/-!
# Pivot replacement, stable cores and join compression (round 26, §34.3z¹¹³)

Response to the brief "relative pivot refinement, new-row generation and global stabilization". Rows `gᵢ ∈ D`,
orbits `uᵢ(n) = (F gᵢ)^[n] s₀` from a column `s₀` contracting for every row, pivot `c = W t`
(`LocalizedCut.relative_grid_pivot`).

* `far_face_meet_is_uncaptured` (Alternative II): `p_T = ⨅_{i∈T} uᵢ(tᵢ)` is in `D`, above `c`, captured by no row
  that does not capture `c`, and `F(m_T, c) ≤ p_T` (asynchronous step + antitone orbits; no Sperner internals).
* `alt1_replacement` (Alternative I): `h = F(m_T, c)` is in `D` and below every `gᵢ`, `i ∈ T`;
  **`alt1_not_expanding`**: `¬ c ≤ F(μ, c)` for every `μ ≤ m_T` — expansion at a pivot would capture it.
* `unified_replacement`: in both cases some `h ∈ D` has `F(m_T, c) ≤ h`.
* `antitone_stabilizes` (DCC) and `stable_core`: once the row aggregate `μ` is stable, `μ ≤ c`, `μ ≤ h`,
  `F(μ, c) ≤ h`.
* **`join_compression`** (ACC): if each new pivot is uncaptured by the running join of the earlier pivots whenever
  that join lies in `D` (i.e. the join is added as a row), then some finite running join lies **outside** `D`.
  So Case I of the brief is impossible for the join-compression refinement; a finite family of `D`-valued pivots with
  outside join is forced. `alt1_not_expanding` shows why this does not yet give a witness at `(μ, ⋁ c)`.
-/

namespace Mordor.PivotReplacement
open Finset Mordor.AsyncGrid

set_option linter.unusedSectionVars false

section Pivot

variable {α : Type*} [Lattice α] [OrderTop α] {k : ℕ} {F : α → α → α}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)

include hF hD in
/-- **Alternative II: the far-face meet is an uncaptured `D`-valued row above the pivot.** -/
theorem far_face_meet_is_uncaptured (g : Fin k → α) {s₀ : α} (hgs : ∀ i, F (g i) s₀ ≤ s₀) (t : Fin k → ℕ)
    (T : Finset (Fin k)) (hT : T.Nonempty) (hII : ∀ i ∈ T, (F (g i))^[t i] s₀ ∈ D) :
    T.inf (fun i => (F (g i))^[t i] s₀) ∈ D ∧
      W (fun i m => (F (g i))^[m] s₀) t ≤ T.inf (fun i => (F (g i))^[t i] s₀) ∧
      (∀ r, ¬ W (fun i m => (F (g i))^[m] s₀) t ≤ r → ¬ T.inf (fun i => (F (g i))^[t i] s₀) ≤ r) ∧
      F (T.inf g) (W (fun i m => (F (g i))^[m] s₀) t) ≤ T.inf (fun i => (F (g i))^[t i] s₀) := by
  obtain ⟨i₀, hi₀⟩ := hT
  have hc : W (fun i m => (F (g i))^[m] s₀) t ≤ T.inf (fun i => (F (g i))^[t i] s₀) :=
    Finset.le_inf fun i _ => W_le _ t i
  refine ⟨hD _ _ (Finset.inf_le hi₀) (hII i₀ hi₀), hc, fun r hunc h => hunc (hc.trans h), ?_⟩
  refine (asynchronous_meet_step hF g T t).trans (Finset.le_inf fun i hi => ?_)
  exact (Finset.inf_le (f := fun i => (F (g i))^[t i + 1] s₀) hi).trans
    (Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) (hgs i) (Nat.le_succ _))

include hD in
/-- **Alternative I: the contracting response is a `D`-valued row below the support rows.** -/
theorem alt1_replacement (g : Fin k → α) (hg : ∀ i, g i ∈ D) (T : Finset (Fin k)) (hT : T.Nonempty) {c : α}
    (hI : F (T.inf g) c ≤ T.inf g) : F (T.inf g) c ∈ D ∧ ∀ i ∈ T, F (T.inf g) c ≤ g i := by
  obtain ⟨i₀, hi₀⟩ := hT
  exact ⟨hD _ _ (hI.trans (Finset.inf_le hi₀)) (hg i₀), fun i hi => hI.trans (Finset.inf_le hi)⟩

include hF in
/-- **Expansion at an Alternative-I pivot is impossible**: it would capture the pivot. -/
theorem alt1_not_expanding (g : Fin k → α) (T : Finset (Fin k)) (hT : T.Nonempty) {c μ : α}
    (hI : F (T.inf g) c ≤ T.inf g) (hunc : ∀ i, ¬ c ≤ g i) (hμ : μ ≤ T.inf g) : ¬ c ≤ F μ c := by
  intro h
  obtain ⟨i₀, hi₀⟩ := hT
  exact hunc i₀ (h.trans ((hF _ _ _ _ hμ le_rfl).trans (hI.trans (Finset.inf_le hi₀))))

include hF hD in
/-- **Unified replacement**: both alternatives give `h ∈ D` with `F(m_T, c) ≤ h`. -/
theorem unified_replacement (g : Fin k → α) (hg : ∀ i, g i ∈ D) {s₀ : α} (hgs : ∀ i, F (g i) s₀ ≤ s₀)
    (t : Fin k → ℕ) (T : Finset (Fin k)) (hT : T.Nonempty)
    (halt : F (T.inf g) (W (fun i m => (F (g i))^[m] s₀) t) ≤ T.inf g ∨ ∀ i ∈ T, (F (g i))^[t i] s₀ ∈ D) :
    ∃ h ∈ D, F (T.inf g) (W (fun i m => (F (g i))^[m] s₀) t) ≤ h := by
  rcases halt with h | h
  · exact ⟨_, (alt1_replacement hD g hg T hT h).1, le_rfl⟩
  · obtain ⟨hpD, -, -, hb⟩ := far_face_meet_is_uncaptured hF hD g hgs t T hT h
    exact ⟨_, hpD, hb⟩

end Pivot

section Stable

variable {α : Type*} [Lattice α]

/-- **DCC stabilizes antitone sequences** (e.g. the row aggregates of an increasing family). -/
theorem antitone_stabilizes [WellFoundedLT α] {f : ℕ → α} (hf : Antitone f) : ∃ N, ∀ n ≥ N, f n = f N := by
  obtain ⟨_, ⟨N, rfl⟩, hmin⟩ := (wellFounded_lt (α := α)).has_min (Set.range f) ⟨_, 0, rfl⟩
  exact ⟨N, fun n hn => eq_of_le_of_not_lt (hf hn) (hmin _ ⟨n, rfl⟩)⟩

/-- **Stable core inequalities.** -/
theorem stable_core {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {μ m c h : α}
    (hμm : μ ≤ m) (hmc : F m c ≤ h) : F μ c ≤ h :=
  (hF _ _ _ _ hμm le_rfl).trans hmc

/-- **Join compression** (ACC). Running joins `Jₙ = c₀ ⊔ ⋯ ⊔ cₙ`; if every new pivot is uncaptured by the
running join whenever that join is in `D` (it has been added as a row), some running join is outside `D`. -/
theorem join_compression [WellFoundedGT α] {D : Set α} (c : ℕ → α)
    (hunc : ∀ n, (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one c ∈ D →
      ¬ c (n + 1) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one c) :
    ∃ n, (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one c ∉ D := by
  let J : ℕ → α := fun n => (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one c
  have hJ : Monotone J := fun a b hab =>
    Finset.sup'_mono c (Finset.range_subset_range.2 (by omega)) _
  obtain ⟨N, hN⟩ := WellFoundedGT.monotone_chain_condition (⟨J, hJ⟩ : ℕ →o α)
  refine ⟨N, fun hD => hunc N hD ?_⟩
  have hle : c (N + 1) ≤ J (N + 1) := Finset.le_sup' c (Finset.mem_range.2 (by omega))
  have heq : J N = J (N + 1) := hN (N + 1) (Nat.le_succ N)
  exact hle.trans heq.symm.le

end Stable

end Mordor.PivotReplacement
