import Mordor.GridRefinement

/-!
# Weak-witness normalization and the relative grid pivot (round 26, §34.3z¹¹²)

Response to the brief "relative Cut and persistent refuge".

* `weak_witness_normalize` (DCC): a weak row-side witness `F(x₀ ⊓ m, y) ≤ x₀` (`x₀ ∈ D`) descends to a fixed response
  `x = F(x ⊓ m, y)`, `x ≤ x₀`, `x ∈ D`; `weak_witness_escapes`: with no witness, `x ≰ m` (this is no witness at the
  cell `(x ⊓ m, y)`).
* **`relative_grid_pivot`** (DCC): the finite grid Sperner argument (`FinGen.cut_finite` on the grid lattice) run
  *without* the full-capture hypothesis. For any finite rows `gᵢ ∈ D` there is a `D`-valued grid column `c = W t`
  captured by no `gᵢ`, and a nonempty `T` with
    `F(m_T, c) ≤ m_T`   (a row contraction at a `D`-valued column)   or   `uᵢ(tᵢ) ∈ D` for all `i ∈ T`
  (`c` lies past the entry points of the `T`-orbits). This is the relative form of the parity argument: it locates
  the uncaptured column, which `uncaptured_column_exists` only asserts. Both alternatives are needed (z3).
* `interior_row_contraction`: if every column past an orbit entry is captured, there is an *interior* uncaptured
  `D`-valued column `c` (every coordinate before its orbit's entry) with `F(m_T, c) ≤ m_T` for some nonempty `T`.
-/

namespace Mordor.LocalizedCut
open Finset Mordor.AsyncGrid

set_option linter.unusedSectionVars false

section Normalize

variable {α : Type*} [Lattice α] [WellFoundedLT α] {F : α → α → α}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)

include hF hD in
/-- **Normalization of a weak row-side witness.** -/
theorem weak_witness_normalize {m x₀ y : α} (hx₀ : x₀ ∈ D) (h0 : F (x₀ ⊓ m) y ≤ x₀) :
    ∃ x ≤ x₀, x ∈ D ∧ F (x ⊓ m) y = x := by
  let h : α → α := fun x => F (x ⊓ m) y
  have hmono : Monotone h := fun a b hab => hF _ _ _ _ (inf_le_inf_right m hab) le_rfl
  have hanti : Antitone fun n => h^[n] x₀ := Monotone.antitone_iterate_of_map_le hmono h0
  obtain ⟨_, ⟨M, rfl⟩, hmin⟩ := (wellFounded_lt (α := α)).has_min (Set.range fun n => h^[n] x₀) ⟨_, 0, rfl⟩
  have e := eq_of_le_of_not_lt (hanti (Nat.le_succ M)) (hmin _ ⟨M + 1, rfl⟩)
  have hle : h^[M] x₀ ≤ x₀ := hanti (Nat.zero_le M)
  refine ⟨h^[M] x₀, hle, hD _ _ hle hx₀, ?_⟩
  have : h^[M + 1] x₀ = h (h^[M] x₀) := Function.iterate_succ_apply' h M x₀
  show h (h^[M] x₀) = h^[M] x₀
  rw [← this]; exact e

/-- With no witness, the fixed response escapes the row cap. -/
theorem weak_witness_escapes (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {m x y : α} (hxD : x ∈ D)
    (hy : y ∉ D) (hfix : F (x ⊓ m) y = x) (hxm : x ≤ m) : False := by
  have hrow : x ⊓ m = x := inf_eq_left.2 hxm
  exact (nw x hxD y hy).1 (by rw [hrow] at hfix; exact hfix.le)

end Normalize

section Pivot

/-- **The relative grid pivot.** -/
theorem relative_grid_pivot {α : Type*} [Lattice α] [BoundedOrder α] [WellFoundedLT α] {k : ℕ} (hk : 0 < k)
    {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set α}
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (htop : ⊤ ∉ D) (g : Fin k → α) (hg : ∀ i, g i ∈ D)
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) :
    ∃ t : Fin k → ℕ, W (fun i m => (F (g i))^[m] ⊤) t ∈ D ∧ (∀ i, ¬ W (fun i m => (F (g i))^[m] ⊤) t ≤ g i) ∧
      ∃ T : Finset (Fin k), T.Nonempty ∧
        (F (T.inf g) (W (fun i m => (F (g i))^[m] ⊤) t) ≤ T.inf g ∨ ∀ i ∈ T, (F (g i))^[t i] ⊤ ∈ D) := by
  classical
  by_contra hno
  have hent : ∀ i, ∃ n, (∀ m ≤ n, (F (g i))^[m] ⊤ ∉ D) ∧ F (g i) ((F (g i))^[n] ⊤) ∈ D :=
    fun i => Mordor.FGTwo.orbit_end (InD := (· ∈ D)) hF (hg i) nw ⊤ htop le_top
  choose n _ hin using hent
  set u : Fin k → ℕ → α := fun i m => (F (g i))^[m] ⊤ with hu
  have hanti : ∀ i, Antitone (u i) := fun i =>
    Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) le_top
  have huN : ∀ i, u i (n i + 1) ∈ D := fun i => by
    simp only [hu]; rw [Function.iterate_succ_apply']; exact hin i
  let P := ∀ i : Fin k, Fin (n i + 2)
  let Wt : P → α := fun t => W u fun i => (t i : ℕ)
  have Wt_anti : ∀ a b : P, a ≤ b → Wt b ≤ Wt a := fun a b h =>
    grid_antitone hanti fun i => (Fin.le_iff_val_le_val.1 (h i))
  let top : P := fun i => ⟨n i + 1, by omega⟩
  -- the far corner: if it is uncaptured it is itself the conclusion (T = univ)
  have hcornerD : Wt top ∈ D := hD _ _ (W_le u _ ⟨0, hk⟩) (huN ⟨0, hk⟩)
  have hcorner : ∃ j, Wt top ≤ g j := by
    by_contra hc; push_neg at hc
    exact hno ⟨fun i => (top i : ℕ), hcornerD, hc, univ, ⟨⟨0, hk⟩, mem_univ _⟩, Or.inr fun i _ => huN i⟩
  let LS : P → Finset (Fin k) := fun t => univ.filter fun j => Wt t ≤ g j
  have mem_LS : ∀ t j, j ∈ LS t ↔ Wt t ≤ g j := fun t j => by simp [LS]
  let step : P → P → P := fun x y i => if i ∈ LS x then sc (y i) else 0
  let FΛ : Pᵒᵈ → Pᵒᵈ → Pᵒᵈ := fun x y => OrderDual.toDual (step (OrderDual.ofDual x) (OrderDual.ofDual y))
  let DΛ : Set Pᵒᵈ := {x | ∃ j, Wt (OrderDual.ofDual x) ≤ g j}
  have hmono : ∀ x x' y y' : Pᵒᵈ, x ≤ x' → y ≤ y' → FΛ x y ≤ FΛ x' y' := by
    intro x x' y y' hx hy i
    show step (OrderDual.ofDual x') (OrderDual.ofDual y') i ≤ step (OrderDual.ofDual x) (OrderDual.ofDual y) i
    simp only [step]
    by_cases h' : i ∈ LS (OrderDual.ofDual x')
    · have h : i ∈ LS (OrderDual.ofDual x) :=
        (mem_LS _ _).2 ((Wt_anti _ _ hx).trans ((mem_LS _ _).1 h'))
      rw [if_pos h', if_pos h]
      exact sc_mono (hy i)
    · rw [if_neg h']; exact Fin.zero_le _
  have hdownΛ : ∀ x y : Pᵒᵈ, x ≤ y → y ∈ DΛ → x ∈ DΛ := fun x y h ⟨j, hj⟩ =>
    ⟨j, (Wt_anti _ _ h).trans hj⟩
  have hbot : (⊥ : Pᵒᵈ) ∈ DΛ := hcorner
  have htopΛ : (⊤ : Pᵒᵈ) ∉ DΛ := by
    rintro ⟨j, hj⟩
    apply htop (hD _ _ (le_trans (le_of_eq ?_) hj) (hg j))
    show ⊤ = univ.inf fun i => u i (((⊥ : P) i : Fin (n i + 2)) : ℕ)
    symm; apply eq_top_iff.2; exact Finset.le_inf fun i _ => by simp [hu]; rfl
  obtain ⟨x, hx, y, hy, hw⟩ := Mordor.FinGen.cut_finite FΛ hmono DΛ hdownΛ hbot htopΛ
  set a := OrderDual.ofDual x
  set b := OrderDual.ofDual y
  obtain ⟨j0, hj0⟩ := hx
  have hj0T : j0 ∈ LS a := (mem_LS _ _).2 hj0
  have hunc : ∀ i, ¬ Wt b ≤ g i := fun i h => hy ⟨i, h⟩
  set T := LS a
  have hTne : T.Nonempty := ⟨j0, hj0T⟩
  -- the meet-row value at `b` lies below the step point
  have hcell : F (T.inf g) (Wt b) ≤ Wt (step a b) := by
    refine Finset.le_inf fun i _ => ?_
    by_cases hi : i ∈ T
    · have hs := asynchronous_meet_step hF g (s := ⊤) T (fun i => (b i : ℕ))
      refine (hs.trans (Finset.inf_le hi)).trans ?_
      have hsc : ((step a b i : Fin (n i + 2)) : ℕ) ≤ (b i : ℕ) + 1 := by
        have hs : step a b i = sc (b i) := if_pos hi
        rw [hs]; unfold sc; split_ifs <;> simp
      exact hanti i hsc
    · have h0 : step a b i = 0 := if_neg hi
      show F (T.inf g) (Wt b) ≤ u i ((step a b i : Fin (n i + 2)) : ℕ)
      rw [h0]; simp [hu]
  by_cases hbD : Wt b ∈ D
  · rcases hw with hw | hw
    · -- `a ≤ step a b`: the row contraction at the uncaptured column `W b`
      have hle : a ≤ step a b := hw
      have hTm : Wt (step a b) ≤ T.inf g :=
        Finset.le_inf fun j hj => (Wt_anti _ _ hle).trans ((mem_LS _ _).1 hj)
      exact hno ⟨fun i => (b i : ℕ), hbD, hunc, T, hTne, Or.inl (hcell.trans hTm)⟩
    · -- `step a b ≤ b`: on `T`, `b` sits at the clipped maximum `n i + 1`
      have hle : step a b ≤ b := hw
      refine hno ⟨fun i => (b i : ℕ), hbD, hunc, T, hTne, Or.inr fun i hi => ?_⟩
      have h1 := Fin.le_iff_val_le_val.1 (hle i)
      have hval : ((step a b i : Fin (n i + 2)) : ℕ) = if (b i : ℕ) < n i + 1 then (b i : ℕ) + 1 else b i := by
        have hs : step a b i = sc (b i) := if_pos hi
        rw [hs]; unfold sc; split_ifs <;> simp
      rw [hval] at h1
      have hb : (b i : ℕ) = n i + 1 := by have := (b i).isLt; split_ifs at h1 <;> omega
      show u i (b i : ℕ) ∈ D
      rw [hb]; exact huN i
  · -- `W b ∉ D`: the argument of `cut_of_grid_capture` gives a witness
    have hbn : ∀ i, (b i : ℕ) < n i + 1 := fun i => by
      by_contra hge
      have heq : (b i : ℕ) = n i + 1 := by have := (b i).isLt; omega
      exact hbD (hD _ _ ((W_le u _ i).trans (by rw [heq])) (huN i))
    have hstepval : ∀ i ∈ T, ((step a b i : Fin (n i + 2)) : ℕ) = b i + 1 := fun i hi => by
      have hs : step a b i = sc (b i) := if_pos hi
      rw [hs]; exact sc_val (hbn i)
    rcases hw with hw | hw
    · have hle : a ≤ step a b := hw
      have hTm : Wt (step a b) ≤ T.inf g :=
        Finset.le_inf fun j hj => (Wt_anti _ _ hle).trans ((mem_LS _ _).1 hj)
      exact (nw _ (hD _ _ (Finset.inf_le hj0T) (hg j0)) _ hbD).1 (hcell.trans hTm)
    · have hle : step a b ≤ b := hw
      have := Fin.le_iff_val_le_val.1 (hle j0)
      rw [hstepval j0 hj0T] at this
      omega

/-- **Faces captured ⇒ a row contraction at an interior uncaptured column.** If every `D`-valued grid column that
lies past some orbit entry (`uᵢ(tᵢ) ∈ D` for some `i`) is captured, the relative pivot is of the first kind. -/
theorem interior_row_contraction {α : Type*} [Lattice α] [BoundedOrder α] [WellFoundedLT α] {k : ℕ} (hk : 0 < k)
    {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set α}
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (htop : ⊤ ∉ D) (g : Fin k → α) (hg : ∀ i, g i ∈ D)
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (hfaces : ∀ t : Fin k → ℕ, (∃ i, (F (g i))^[t i] ⊤ ∈ D) →
      ∃ j, W (fun i m => (F (g i))^[m] ⊤) t ≤ g j) :
    ∃ t : Fin k → ℕ, W (fun i m => (F (g i))^[m] ⊤) t ∈ D ∧ (∀ i, ¬ W (fun i m => (F (g i))^[m] ⊤) t ≤ g i) ∧
      (∀ i, (F (g i))^[t i] ⊤ ∉ D) ∧
      ∃ T : Finset (Fin k), T.Nonempty ∧ F (T.inf g) (W (fun i m => (F (g i))^[m] ⊤) t) ≤ T.inf g := by
  obtain ⟨t, htD, hunc, T, hT, halt⟩ := relative_grid_pivot hk hF hD htop g hg nw
  have hint : ∀ i, (F (g i))^[t i] ⊤ ∉ D := fun i hi => by
    obtain ⟨j, hj⟩ := hfaces t ⟨i, hi⟩; exact hunc j hj
  refine ⟨t, htD, hunc, hint, T, hT, ?_⟩
  rcases halt with h | h
  · exact h
  · obtain ⟨i, hi⟩ := hT; exact absurd (h i hi) (hint i)

end Pivot

end Mordor.LocalizedCut
