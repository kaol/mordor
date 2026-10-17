import Mordor.PrincipalCut

/-!
# Reachability: the gap is joins (log §31.1)

`R F` is the least down-set containing `⊥`, closed under `a` and under `b⁻¹`.
* `cutMaps_iff_R`: the Cut Lemma for `F` holds iff `R F = univ`.
* `R_univ_of_joinClosed`: on a complete lattice without infinite ascending or descending chains (every finite
  lattice, and the infinite chain-finite frontier D_ω, E_ω, M_ω × C₂ of §31.6), if `R F` is closed under binary
  joins then `R F = univ`.
  So the Cut Lemma for `F` is equivalent to join-closure of `R F`: the principal (ideal) case is settled by
  `cut_principal_down`, and joins are the entire gap.
-/

namespace Mordor
variable {α : Type*} [CompleteLattice α] (F : α →o α →o α)

/-- The closure conditions of a cut counterexample. -/
def Closed (D : Set α) : Prop := IsDown D ∧ ⊥ ∈ D ∧ (∀ x ∈ D, a F x ∈ D) ∧ ∀ y, b F y ∈ D → y ∈ D

/-- `R(F)`: the least closed set. -/
def R : Set α := ⋂₀ {D | Closed F D}

variable {F}

theorem R_closed : Closed F (R F) := by
  refine ⟨fun x y hxy hy => ?_, ?_, fun x hx => ?_, fun y hy => ?_⟩
  · exact Set.mem_sInter.2 fun D hD => hD.1 hxy (Set.mem_sInter.1 hy D hD)
  · exact Set.mem_sInter.2 fun D hD => hD.2.1
  · exact Set.mem_sInter.2 fun D hD => hD.2.2.1 x (Set.mem_sInter.1 hx D hD)
  · exact Set.mem_sInter.2 fun D hD => hD.2.2.2 y (Set.mem_sInter.1 hy D hD)

theorem R_subset {D : Set α} (hD : Closed F D) : R F ⊆ D := Set.sInter_subset_of_mem hD

/-- **Cut Lemma for `F` ⟺ `R(F) = L`.** -/
theorem cutMaps_iff_R : CutMaps F ↔ R F = Set.univ := by
  constructor
  · intro h
    obtain ⟨hD, h0, ha, hb⟩ := (R_closed (F := F))
    exact Set.eq_univ_of_forall (h _ hD ⟨⊥, h0⟩ ha hb)
  · intro h D hD ⟨x, hx⟩ ha hb u
    have h0 : ⊥ ∈ D := hD bot_le hx
    exact R_subset ⟨hD, h0, ha, hb⟩ (h ▸ Set.mem_univ u)

/-- **The gap is joins.** On a finite lattice, a join-closed `R(F)` is everything. -/
theorem R_univ_of_joinClosed [WellFoundedGT α] [WellFoundedLT α] (hj : ∀ x ∈ R F, ∀ y ∈ R F, x ⊔ y ∈ R F) :
    R F = Set.univ := by
  obtain ⟨hD, h0, ha, hb⟩ := (R_closed (F := F))
  -- a nonempty join-closed set with a maximal element (ACC) contains its join
  have hsup : sSup (R F) ∈ R F := by
    obtain ⟨x, hxR, hmax⟩ := (wellFounded_gt (α := α)).has_min (R F) ⟨⊥, h0⟩
    have hgreat : ∀ y ∈ R F, y ≤ x := fun y hy =>
      le_sup_right.trans (eq_of_le_of_not_lt le_sup_left (hmax _ (hj x hxR y hy))).ge
    have : sSup (R F) = x := le_antisymm (sSup_le hgreat) (le_sSup hxR)
    rwa [this]
  by_contra hne
  have hd : sSup (R F) ≠ ⊤ := by
    intro htop; apply hne; exact Set.eq_univ_of_forall fun u => hD le_top (htop ▸ hsup)
  obtain ⟨x, hx, y, hy, hc | hc⟩ := cut_principal_down F (sSup (R F)) hd
  · -- F x y ≤ x ∈ R: b y ≤ x, so b y ∈ R, so y ∈ R, so y ≤ sSup R
    exact hy (le_sSup (hb y (hD (b_le hc) (hD hx hsup))))
  · -- y ≤ F x y: y ≤ a x ∈ R, so y ∈ R
    exact hy (le_sSup (hD (le_a hc) (ha x (hD hx hsup))))

/-- **The Cut Lemma for `F` ⟺ join-closure of `R(F)`**, on complete lattices with ACC and DCC. -/
theorem cutMaps_iff_joinClosed [WellFoundedGT α] [WellFoundedLT α] :
    CutMaps F ↔ ∀ x ∈ R F, ∀ y ∈ R F, x ⊔ y ∈ R F := by
  refine ⟨fun h x _ y _ => ?_, fun h => cutMaps_iff_R.mpr (R_univ_of_joinClosed h)⟩
  rw [cutMaps_iff_R.mp h]; trivial

end Mordor
