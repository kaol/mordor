import Mordor.AsyncMeetGrid

/-!
# First-entry boundaries of orbit grids, and the first ideal-orbit stage (round 26, §34.3z¹¹⁰)

Response to the brief "first-entry frontiers, orbit transitions and finite-support escape". Rows `gᵢ ∈ D`, a start
column `s₀` contracting for every row (e.g. `⊤`), orbits `uᵢ(n) = (F gᵢ)^[n] s₀`, grid columns `W t = ⨅ᵢ uᵢ(tᵢ)`.

* `exists_min_boundary`: below every `D`-valued grid point there is a first-entry point `r` (all immediate
  predecessors `W(r - eᵢ)`, `rᵢ ≥ 1`, outside `D`).
* **`cube_escape`**: for an outside grid point `s` and nonempty `T`, the meet of *any* finite family of elements above
  `W(π_T s + 1_T)` (e.g. capturers of all boundary points `≤ π_T s + 1_T`) is not below `m_T = ⨅_T g`. This is the
  correct higher-dimensional form of `Rectangle.capturer_meet_escapes`; it needs a **common outside lower point** `s`.
* `grid_constraint`: the capturer-covering case — `T ⊆` labels of `W(π_T s + 1_T)` is impossible. This is exactly
  constraint (iii) of the grid abstraction (§34.3z¹⁰⁵), i.e. the brief's boundary-cube statements add nothing beyond it.
* **`first_stage_iff`**: the brief's work package B target, `rk G 1 = a ⊥ ⊔ ⨆{y | b y ≤ ⊥} ∈ R(G)` for every `G`,
  is *equivalent* to Cut for every `F` on the lattice (`cutMaps_of_rk_one`, normal form §34.3z⁴²); not a weaker stage.
-/

namespace Mordor.FirstEntry
open Finset Mordor.AsyncGrid

set_option linter.unusedSectionVars false

section Grid

variable {α : Type*} [Lattice α] [OrderTop α] {k : ℕ}

/-- **First-entry points exist below every `D`-valued grid point.** -/
theorem exists_min_boundary {D : Set α} (u : Fin k → ℕ → α) {t : Fin k → ℕ} (ht : W u t ∈ D) :
    ∃ r ≤ t, W u r ∈ D ∧ ∀ i, 1 ≤ r i → W u (Function.update r i (r i - 1)) ∉ D := by
  obtain ⟨r, ⟨hrt, hrD⟩, hmin⟩ := (wellFounded_lt (α := Fin k → ℕ)).has_min {r | r ≤ t ∧ W u r ∈ D} ⟨t, le_rfl, ht⟩
  refine ⟨r, hrt, hrD, fun i hi hD' => hmin _ ⟨?_, hD'⟩ ?_⟩
  · intro j; by_cases hj : j = i
    · subst hj; simp only [Function.update_self]; exact le_trans (Nat.sub_le _ _) (hrt j)
    · simp [hj]; exact hrt j
  · refine lt_of_le_of_ne (fun j => ?_) fun he => ?_
    · by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    · have := congr_fun he i; simp at this; omega

variable {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set α}
  (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF in
/-- The meet-row value at an outside column lies below the advanced grid point `π_T s + 1_T`. -/
theorem meet_row_below_advanced (g : Fin k → α) {s₀ : α} (hgs : ∀ i, F (g i) s₀ ≤ s₀) (T : Finset (Fin k))
    (hT : T.Nonempty) (s : Fin k → ℕ) :
    F (T.inf g) (W (fun i m => (F (g i))^[m] s₀) s) ≤
      W (fun i m => (F (g i))^[m] s₀) (fun i => if i ∈ T then s i + 1 else 0) := by
  refine (asynchronous_meet_step hF g T s).trans (Finset.le_inf fun i _ => ?_)
  by_cases hi : i ∈ T
  · simp only [if_pos hi]; exact Finset.inf_le (f := fun i => (F (g i))^[s i + 1] s₀) hi
  · simp only [if_neg hi, Function.iterate_zero, id]
    obtain ⟨i₀, hi₀⟩ := hT
    exact (Finset.inf_le (f := fun i => (F (g i))^[s i + 1] s₀) hi₀).trans
      (Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) (hgs i₀) (Nat.zero_le _))

include hF hD nw in
/-- **Cube escape.** Every finite family of elements above the advanced grid point of an outside column has its meet
outside `↓ m_T`. -/
theorem cube_escape (g : Fin k → α) (hg : ∀ i, g i ∈ D) {s₀ : α} (hgs : ∀ i, F (g i) s₀ ≤ s₀)
    (T : Finset (Fin k)) (hT : T.Nonempty) {s : Fin k → ℕ} (hs : W (fun i m => (F (g i))^[m] s₀) s ∉ D)
    {n : ℕ} (c : Fin n → α)
    (hc : ∀ j, W (fun i m => (F (g i))^[m] s₀) (fun i => if i ∈ T then s i + 1 else 0) ≤ c j) :
    ¬ univ.inf c ≤ T.inf g := by
  intro h
  obtain ⟨i₀, hi₀⟩ := hT
  have hmD : T.inf g ∈ D := hD _ _ (Finset.inf_le hi₀) (hg i₀)
  exact (nw _ hmD _ hs).1 ((meet_row_below_advanced hF g hgs T ⟨i₀, hi₀⟩ s).trans
    ((Finset.le_inf fun j _ => hc j).trans h))

include hF hD nw in
/-- **Capturer covering is impossible** (constraint (iii) of the grid abstraction). -/
theorem grid_constraint (g : Fin k → α) (hg : ∀ i, g i ∈ D) {s₀ : α} (hgs : ∀ i, F (g i) s₀ ≤ s₀)
    (T : Finset (Fin k)) (hT : T.Nonempty) {s : Fin k → ℕ} (hs : W (fun i m => (F (g i))^[m] s₀) s ∉ D)
    (hcov : ∀ i ∈ T, W (fun i m => (F (g i))^[m] s₀) (fun i => if i ∈ T then s i + 1 else 0) ≤ g i) : False := by
  obtain ⟨i₀, hi₀⟩ := hT
  have hmD : T.inf g ∈ D := hD _ _ (Finset.inf_le hi₀) (hg i₀)
  exact (nw _ hmD _ hs).1 ((meet_row_below_advanced hF g hgs T ⟨i₀, hi₀⟩ s).trans (Finset.le_inf hcov))

end Grid

section FirstStage

variable {α : Type*} [CompleteLattice α] [WellFoundedLT α]

/-- **The first ideal-orbit stage is the conjecture.** -/
theorem first_stage_iff : (∀ G : α →o α →o α, rk G 1 ∈ R G) ↔ ∀ G : α →o α →o α, CutMaps G := by
  refine ⟨fun h G => cutMaps_of_rk_one h G, fun h G => ?_⟩
  rw [cutMaps_iff_R.1 (h G)]; trivial

end FirstStage

end Mordor.FirstEntry
