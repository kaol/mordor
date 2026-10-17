import Mordor.Derived
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# The Cut Lemma and semi-commutation (log §30.3–§30.4)

`CutCells F`: every nonempty proper down-set `D` has `x ∈ D`, `y ∉ D` with `F x y ≤ x` or `y ≤ F x y` (§30.4).
`CutMaps F`: no nonempty proper down-set is closed under `a` and under `b⁻¹`. The two are equivalent per `F`.

**Theorem `semi_of_cut`.** For a single `F` on any complete lattice, `CutMaps F` and `b ∘ a ≤ a ∘ b` give `m = n`.
This sharpens §30.4, which reduced to the polar interval `[m, n]` and so needed the Cut Lemma on every interval:
the sink set `D = {x | ∃ k, bᵏ x ≤ m}` is already a proper down-set of `L` closed under `a` and `b⁻¹`.

**Theorem `cut_finite_chain`.** On a finite chain the Cut Lemma holds (the cell `F (max D) (min Dᶜ)`), hence
semi-commutation forces `μν = νμ` (§30.3) and so does commutation (the Finite Commutation Lemma, §20.5).
-/

namespace Mordor
variable {α : Type*} [CompleteLattice α]

def IsDown (D : Set α) : Prop := ∀ ⦃x y⦄, x ≤ y → y ∈ D → x ∈ D

def CutCells (F : α →o α →o α) : Prop :=
  ∀ D : Set α, IsDown D → D.Nonempty → (∃ u, u ∉ D) → ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y)

def CutMaps (F : α →o α →o α) : Prop :=
  ∀ D : Set α, IsDown D → D.Nonempty → (∀ x ∈ D, a F x ∈ D) → (∀ y, b F y ∈ D → y ∈ D) → ∀ u, u ∈ D

variable {F : α →o α →o α}

theorem cutMaps_of_cells (h : CutCells F) : CutMaps F := by
  intro D hD hne ha hb u
  by_contra hu
  obtain ⟨x, hx, y, hy, hc | hc⟩ := h D hD hne ⟨u, hu⟩
  · exact hy (hb y (hD (b_le hc) hx))
  · exact hy (hD (le_a hc) (ha x hx))

theorem cutCells_of_maps (h : CutMaps F) : CutCells F := by
  intro D hD hne ⟨u, hu⟩
  by_contra hno
  push_neg at hno
  apply hu
  refine h D hD hne (fun x hx => ?_) (fun y hy => ?_) u
  · by_contra hax
    exact absurd (row_a x).ge (hno x hx (a F x) hax).2
  · by_contra hyD
    exact absurd (col_b y).le (hno (b F y) hy y hyD).1

theorem cutCells_iff_maps : CutCells F ↔ CutMaps F := ⟨cutMaps_of_cells, cutCells_of_maps⟩

/-- **Cut ⟹ semi-CL, per `F`, on `L` itself.** -/
theorem semi_of_cut (hcut : CutMaps F) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  let D : Set α := {x | ∃ k, (b F)^[k] x ≤ m F}
  have hD : IsDown D := fun x y hxy ⟨k, hk⟩ => ⟨k, ((b F).monotone.iterate k hxy).trans hk⟩
  have hb : ∀ y, b F y ∈ D → y ∈ D := fun y ⟨k, hk⟩ => ⟨k + 1, by rwa [Function.iterate_succ_apply]⟩
  have ha : ∀ k x, (b F)^[k] x ≤ m F → a F x ∈ D := by
    intro k
    induction k with
    | zero => intro x hx; exact ⟨0, ((a F).mono hx).trans a_m.le⟩
    | succ k ih =>
      intro x hx
      rw [Function.iterate_succ_apply] at hx
      exact hb _ (hD (hsemi x) (ih _ hx))
  have hn : n F ∈ D := hcut D hD ⟨m F, 0, le_rfl⟩ (fun x ⟨k, hk⟩ => ha k x hk) hb (n F)
  obtain ⟨k, hk⟩ := hn
  rw [Function.iterate_fixed b_n] at hk
  exact le_antisymm m_le_n hk

/-- **The Cut Lemma on a finite chain.** -/
theorem cut_finite_chain {β : Type*} [CompleteLinearOrder β] [Finite β] (G : β →o β →o β) : CutCells G := by
  intro D hD hne ⟨u, hu⟩
  have hd : sSup D ∈ D := hne.csSup_mem D.toFinite
  have hU : (Dᶜ).Nonempty := ⟨u, hu⟩
  have he : sInf Dᶜ ∈ Dᶜ := hU.csInf_mem (Dᶜ).toFinite
  refine ⟨sSup D, hd, sInf Dᶜ, he, ?_⟩
  rcases le_or_gt (G (sSup D) (sInf Dᶜ)) (sSup D) with h | h
  · exact Or.inl h
  · right
    apply sInf_le
    intro hc
    exact absurd (le_sSup hc) (not_le.mpr h)

/-- **Semi-Commutation Lemma (§30.3).** On a finite chain, `b ∘ a ≤ a ∘ b` forces `μX. νY. F = νY. μX. F`. -/
theorem semi_finite_chain {β : Type*} [CompleteLinearOrder β] [Finite β] (G : β →o β →o β)
    (hsemi : ∀ x, b G (a G x) ≤ a G (b G x)) : m G = n G :=
  semi_of_cut (cutMaps_of_cells (cut_finite_chain G)) hsemi

/-- **Finite Commutation Lemma (§20.5).** On a finite chain, `a ∘ b = b ∘ a` forces `μX. νY. F = νY. μX. F`. -/
theorem fcl {β : Type*} [CompleteLinearOrder β] [Finite β] (G : β →o β →o β)
    (hcomm : ∀ x, a G (b G x) = b G (a G x)) : m G = n G :=
  semi_finite_chain G fun x => (hcomm x).ge

end Mordor
