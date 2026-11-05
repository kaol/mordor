import Mordor.AsyncMeetGrid

/-!
# Infinite boundaries: extremal representatives, duality, and one-sided grid capture (round 26, §34.3z¹⁰⁶)

Response to the brief "infinite boundary capture and the Sperner extension". `D` is a down-set with `⊥ ∈ D`,
`⊤ ∉ D`; `P = Max D`, `U = Min Dᶜ`.

* `exists_maximal_above` (ACC), `exists_minimal_below` (DCC), `maximal_pairwise_join_outside`,
  `minimal_pairwise_meet_inside`, `cell_cross`: the boundary facts of the brief.
* `no_witness_of_captured`: a finite pair `P₀ ⊆ D`, `U₀ ⊆ Dᶜ` capturing its response table contradicts no witness
  (`FinGen.captured`). This is the brief's finite-capture target, formalized as a sufficient condition.
* **`cut_of_grid_capture`** (DCC): a *one-sided, single-grid* capture suffices. For finitely many rows `gᵢ ∈ D`
  (not necessarily generating `D`), if every `D`-valued meet `W(t) = ⨅ᵢ (F gᵢ)^[tᵢ] ⊤` of their orbit points lies
  below some `gᵢ`, the cut has a witness. Only the `D` side and only the grid columns need capturing — not the
  `Dᶜ` side, and not the response table. `cut_fingen_dcc` is the case where `g` generates `D`.
* `uncaptured_column_exists`: under a counterexample every finite row family leaves a `D`-valued grid column
  uncaptured, so the refinement never stabilizes; termination of the refinement is equivalent to Cut for that `F`.
* **`cut_cofingen_acc`** (ACC): the order dual of `cut_fingen_dcc` — if `Dᶜ = ⋃ⱼ ↑uⱼ` is finitely generated, the
  cut has a witness. **`cut_chainfinite_of_finite_side`**: in a chain-finite lattice, Cut holds whenever `D` or its
  complement is finitely generated (e.g. `Max D` or `Min Dᶜ` finite).
-/

namespace Mordor.InfCapture
open Finset Mordor.AsyncGrid

set_option linter.unusedSectionVars false

section Boundary

variable {α : Type*} [Lattice α] {D : Set α}

/-- Every element of `D` lies below a maximal element of `D` (ACC). -/
theorem exists_maximal_above [WellFoundedGT α] {x : α} (hx : x ∈ D) :
    ∃ p ∈ D, x ≤ p ∧ ∀ q ∈ D, p ≤ q → q = p := by
  obtain ⟨p, ⟨hpD, hxp⟩, hmax⟩ := (wellFounded_gt (α := α)).has_min {q | q ∈ D ∧ x ≤ q} ⟨x, hx, le_rfl⟩
  exact ⟨p, hpD, hxp, fun q hq hpq => by
    by_contra hne
    exact hmax q ⟨hq, hxp.trans hpq⟩ (lt_of_le_of_ne hpq fun h => hne h.symm)⟩

/-- Every element outside `D` lies above a minimal element of `Dᶜ` (DCC). -/
theorem exists_minimal_below [WellFoundedLT α] {y : α} (hy : y ∉ D) :
    ∃ u ∉ D, u ≤ y ∧ ∀ v ∉ D, v ≤ u → v = u := by
  obtain ⟨u, ⟨huD, huy⟩, hmin⟩ := (wellFounded_lt (α := α)).has_min {v | v ∉ D ∧ v ≤ y} ⟨y, hy, le_rfl⟩
  exact ⟨u, huD, huy, fun v hv hvu => by
    by_contra hne
    exact hmin v ⟨hv, hvu.trans huy⟩ (lt_of_le_of_ne hvu hne)⟩

/-- Distinct maximal elements of `D` have their join outside `D`. -/
theorem maximal_pairwise_join_outside {p q : α} (hp : ∀ r ∈ D, p ≤ r → r = p) (hq : ∀ r ∈ D, q ≤ r → r = q)
    (hpq : p ≠ q) : p ⊔ q ∉ D := fun h =>
  hpq ((hp _ h le_sup_left).symm.trans (hq _ h le_sup_right))

/-- Distinct minimal elements of `Dᶜ` have their meet in `D`. -/
theorem minimal_pairwise_meet_inside {u v : α} (hu : ∀ w ∉ D, w ≤ u → w = u) (hv : ∀ w ∉ D, w ≤ v → w = v)
    (huv : u ≠ v) : u ⊓ v ∈ D := by
  by_contra h
  exact huv ((hu _ h inf_le_left).symm.trans (hv _ h inf_le_right))

/-- The inputs of every response cell form a cross pair. -/
theorem cell_cross [OrderTop α] [OrderBot α] (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) {k l : ℕ} {p : Fin k → α}
    {u : Fin l → α} (hp : ∀ i, p i ∈ D) (hu : ∀ j, u j ∉ D) {A : Finset (Fin k)} {B : Finset (Fin l)}
    (hA : A.Nonempty) (hB : B.Nonempty) : A.inf p ∈ D ∧ B.sup u ∉ D := by
  obtain ⟨i, hi⟩ := hA; obtain ⟨j, hj⟩ := hB
  exact ⟨hD _ _ (Finset.inf_le hi) (hp i), fun h => hu j (hD _ _ (Finset.le_sup hj) h)⟩

end Boundary

section Capture

variable {α : Type*} [Lattice α] [BoundedOrder α]

/-- **A finitely captured response table contradicts no witness** (`FinGen.captured`). -/
theorem no_witness_of_captured {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) {k l : ℕ} (hk : 0 < k) (hl : 0 < l) {p : Fin k → α}
    {u : Fin l → α} (hp : ∀ i, p i ∈ D) (hu : ∀ j, u j ∉ D)
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (capD : ∀ A : Finset (Fin k), ∀ B : Finset (Fin l), A.Nonempty → B.Nonempty →
      F (A.inf p) (B.sup u) ∈ D → ∃ i, F (A.inf p) (B.sup u) ≤ p i)
    (capU : ∀ A : Finset (Fin k), ∀ B : Finset (Fin l), A.Nonempty → B.Nonempty →
      F (A.inf p) (B.sup u) ∉ D → ∃ j, u j ≤ F (A.inf p) (B.sup u)) : False := by
  refine Mordor.FinGen.captured hk hl hF capD capU (fun A B hA hB h => ?_) (fun A B hA hB h => ?_)
  · obtain ⟨hAD, hBD⟩ := cell_cross hD hp hu hA hB
    exact (nw _ hAD _ hBD).1 (Finset.le_inf h)
  · obtain ⟨hAD, hBD⟩ := cell_cross hD hp hu hA hB
    exact (nw _ hAD _ hBD).2 (Finset.sup_le h)

/-- **One-sided grid capture suffices** (DCC). -/
theorem cut_of_grid_capture [WellFoundedLT α] {k : ℕ} (hk : 0 < k) {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (htop : ⊤ ∉ D) (g : Fin k → α) (hg : ∀ i, g i ∈ D)
    (hcap : ∀ t : Fin k → ℕ, W (fun i m => (F (g i))^[m] ⊤) t ∈ D → ∃ i, W (fun i m => (F (g i))^[m] ⊤) t ≤ g i) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  classical
  by_contra hno
  have nw : ∀ x, x ∈ D → ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y :=
    fun x hx y hy => ⟨fun h => hno ⟨x, hx, y, hy, Or.inl h⟩, fun h => hno ⟨x, hx, y, hy, Or.inr h⟩⟩
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
  have hcapW : ∀ t : P, Wt t ∈ D → ∃ i, Wt t ≤ g i := fun t h => hcap _ h
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
  have hbot : (⊥ : Pᵒᵈ) ∈ DΛ := by
    refine hcapW _ (hD _ _ ((W_le u _ ⟨0, hk⟩).trans (le_of_eq ?_)) (huN ⟨0, hk⟩))
    congr 1
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
  have hb : Wt b ∉ D := fun h => hy (hcapW _ h)
  have hbn : ∀ i, (b i : ℕ) < n i + 1 := fun i => by
    by_contra hge
    have heq : (b i : ℕ) = n i + 1 := by have := (b i).isLt; omega
    exact hb (hD _ _ ((W_le u _ i).trans (by rw [heq])) (huN i))
  have hstepval : ∀ i ∈ LS a, ((step a b i : Fin (n i + 2)) : ℕ) = b i + 1 := fun i hi => by
    simp only [step, if_pos hi]; exact sc_val (hbn i)
  rcases hw with hw | hw
  · have hle : a ≤ step a b := hw
    set T := LS a
    have hcell : F (T.inf g) (Wt b) ≤ Wt (step a b) := by
      refine Finset.le_inf fun i _ => ?_
      by_cases hi : i ∈ T
      · have := asynchronous_meet_step hF g (s := ⊤) T (fun i => (b i : ℕ))
        refine (this.trans (Finset.inf_le hi)).trans (le_of_eq ?_)
        simp only [hu]; rw [hstepval i hi]
      · have h0 : step a b i = 0 := if_neg hi
        show F (T.inf g) (Wt b) ≤ u i ((step a b i : Fin (n i + 2)) : ℕ)
        rw [h0]; simp [hu]
    have hTm : Wt (step a b) ≤ T.inf g :=
      Finset.le_inf fun j hj => (Wt_anti _ _ hle).trans ((mem_LS _ _).1 hj)
    exact (nw _ (hD _ _ (Finset.inf_le hj0T) (hg j0)) _ hb).1 (hcell.trans hTm)
  · have hle : step a b ≤ b := hw
    have := Fin.le_iff_val_le_val.1 (hle j0)
    rw [hstepval j0 hj0T] at this
    omega

/-- **The dual of `cut_fingen_dcc`** (ACC): a cut whose complement is finitely generated has a witness. -/
theorem cut_cofingen_acc [WellFoundedGT α] {k : ℕ} (hk : 0 < k) {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (u : Fin k → α) (hbot : ¬ ∃ j, u j ≤ ⊥) :
    ∃ x, (¬ ∃ j, u j ≤ x) ∧ ∃ y, (∃ j, u j ≤ y) ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  let G : αᵒᵈ → αᵒᵈ → αᵒᵈ := fun Y X => OrderDual.toDual (F (OrderDual.ofDual X) (OrderDual.ofDual Y))
  have hG : ∀ y y' x x' : αᵒᵈ, y ≤ y' → x ≤ x' → G y x ≤ G y' x' := fun y y' x x' hy hx =>
    hF _ _ _ _ hx hy
  obtain ⟨Y, ⟨i, hYi⟩, X, hX, hw⟩ :=
    cut_fingen_dcc (α := αᵒᵈ) hk hG (fun j => OrderDual.toDual (u j)) (fun ⟨j, hj⟩ => hbot ⟨j, hj⟩)
  refine ⟨OrderDual.ofDual X, fun ⟨j, hj⟩ => hX ⟨j, hj⟩, OrderDual.ofDual Y, ⟨i, hYi⟩, ?_⟩
  rcases hw with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- **Chain-finite Cut when one side is finitely generated.** -/
theorem cut_chainfinite_of_finite_side [WellFoundedLT α] [WellFoundedGT α] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbotD : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (hfin : (∃ k, ∃ g : Fin k → α, (∀ i, g i ∈ D) ∧ ∀ x ∈ D, ∃ i, x ≤ g i) ∨
      (∃ l, ∃ u : Fin l → α, (∀ j, u j ∉ D) ∧ ∀ y ∉ D, ∃ j, u j ≤ y)) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  rcases hfin with ⟨k, g, hg, hgen⟩ | ⟨l, u, hu, hgen⟩
  · have hk : 0 < k := by
      obtain ⟨i, _⟩ := hgen ⊥ hbotD; exact Fin.pos i
    refine cut_of_grid_capture hk hF hD htop g hg fun t ht => hgen _ ht
  · have hl : 0 < l := by
      obtain ⟨j, _⟩ := hgen ⊤ htop; exact Fin.pos j
    have memD : ∀ z, z ∈ D ↔ ¬ ∃ j, u j ≤ z := fun z =>
      ⟨fun hz ⟨j, hj⟩ => hu j (hD _ _ hj hz), fun h => by by_contra hz; exact h (hgen z hz)⟩
    obtain ⟨x, hx, y, hy, hw⟩ := cut_cofingen_acc hl hF u ((memD ⊥).1 hbotD)
    exact ⟨x, (memD x).2 hx, y, fun h => (memD y).1 h hy, hw⟩

/-- **Under a counterexample, grid refinement never stabilizes.** If `F` has no witness, then for every finite
nonempty family of rows `gᵢ ∈ D` some `D`-valued grid column lies below none of them; adding a maximal element above
it (`exists_maximal_above`) is the next refinement step. So a termination proof for the refinement *is* a proof of
Cut for that `F`: it must use `F`, not only the chain conditions. -/
theorem uncaptured_column_exists [WellFoundedLT α] {k : ℕ} (hk : 0 < k) {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (htop : ⊤ ∉ D) (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (g : Fin k → α) (hg : ∀ i, g i ∈ D) :
    ∃ t : Fin k → ℕ, W (fun i m => (F (g i))^[m] ⊤) t ∈ D ∧ ∀ i, ¬ W (fun i m => (F (g i))^[m] ⊤) t ≤ g i := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx, y, hy, hw⟩ := cut_of_grid_capture hk hF hD htop g hg h
  rcases hw with hw | hw
  · exact (nw x hx y hy).1 hw
  · exact (nw x hx y hy).2 hw

end Capture

end Mordor.InfCapture
