import Mordor.TwoSided
import Mathlib.Data.Multiset.DershowitzManna

/-!
# Crossing-interval refinement and anchor envelopes (round 26, §34.3z¹²⁴)

ChatGPT brief "Stage 2: new proof strategies for the chain-finite Commutation Lemma", Strategies A and B.
Finite supremum / infimum support is already `Stable.sSup_finite_support` / `sInf_finite_support` (Mathlib's
`CompleteLattice.WellFoundedGT.isSupFiniteCompact`); nothing new is needed.

**Strategy B.**
* `intervalKey (s, t) = (toDual s, t)`; `IntervalLT I J`: `J.1 ≤ I.1 ≤ I.2 ≤ J.2` with one strict endpoint. It is a
  subrelation of the product order on `αᵒᵈ × α` (`intervalLT_key`), hence well-founded under ACC + DCC
  (`intervalLT_wellFounded`).
* `refine_dm`: replacing one interval of a multiset by finitely many strictly smaller ones is a Dershowitz–Manna step
  on keys, and that order is well-founded (`Multiset.wellFounded_isDershowitzMannaLT`).

**Strategy A.**
* `envelope H C F x y = ⨆_{h ∈ H, h ≤ x} ⨅_{c ∈ C, y ≤ c} F h c`: `envelope_mono` (monotone) and `envelope_anchor`
  (equal to `F` on anchor cells `H × C`). Witness preservation off the anchors is not a consequence: see §34.3z¹²⁴.
-/

namespace Mordor.IntervalRefinement
open Multiset

set_option linter.unusedSectionVars false

section B

variable {α : Type*} [PartialOrder α]

/-- Strict containment of intervals `[s', t'] ⊊ [s, t]` (as pairs). -/
def IntervalLT (I J : α × α) : Prop := J.1 ≤ I.1 ∧ I.2 ≤ J.2 ∧ (J.1 ≠ I.1 ∨ I.2 ≠ J.2)

def intervalKey (I : α × α) : αᵒᵈ × α := (OrderDual.toDual I.1, I.2)

theorem intervalLT_key {I J : α × α} (h : IntervalLT I J) : intervalKey I < intervalKey J := by
  obtain ⟨h1, h2, h3⟩ := h
  refine lt_of_le_of_ne ⟨h1, h2⟩ fun he => ?_
  have e1 : I.1 = J.1 := congrArg (fun p : αᵒᵈ × α => OrderDual.ofDual p.1) he
  have e2 : I.2 = J.2 := congrArg Prod.snd he
  rcases h3 with h3 | h3
  · exact h3 e1.symm
  · exact h3 e2

/-- **Well-foundedness** of strict interval containment on chain-finite orders. -/
theorem intervalLT_wellFounded [WellFoundedLT α] [WellFoundedGT α] :
    WellFounded (IntervalLT : α × α → α × α → Prop) :=
  Subrelation.wf (fun h => intervalLT_key h) (InvImage.wf intervalKey wellFounded_lt)

/-- **Dershowitz–Manna refinement step.** Replacing `I` by a multiset `N` of strictly smaller intervals decreases the
multiset of keys in the Dershowitz–Manna order, which is well-founded. -/
theorem refine_dm (Z N : Multiset (α × α)) (I : α × α) (hN : ∀ J ∈ N, IntervalLT J I) :
    IsDershowitzMannaLT ((Z + N).map intervalKey) ((Z + {I}).map intervalKey) := by
  refine ⟨Z.map intervalKey, N.map intervalKey, {intervalKey I}, by simp, by simp, by simp, ?_⟩
  intro y hy
  obtain ⟨J, hJ, rfl⟩ := Multiset.mem_map.1 hy
  exact ⟨intervalKey I, Multiset.mem_singleton_self _, intervalLT_key (hN J hJ)⟩

theorem dm_wellFounded [WellFoundedLT α] [WellFoundedGT α] :
    WellFounded (IsDershowitzMannaLT : Multiset (αᵒᵈ × α) → Multiset (αᵒᵈ × α) → Prop) :=
  wellFounded_isDershowitzMannaLT

end B

section A

variable {α : Type*} [CompleteLattice α]

/-- The anchor envelope of the brief. -/
noncomputable def envelope (H C : Set α) (F : α → α → α) (x y : α) : α :=
  ⨆ h ∈ {h | h ∈ H ∧ h ≤ x}, ⨅ c ∈ {c | c ∈ C ∧ y ≤ c}, F h c

theorem envelope_mono (H C : Set α) (F : α → α → α) {x x' y y' : α} (hx : x ≤ x') (hy : y ≤ y') :
    envelope H C F x y ≤ envelope H C F x' y' := by
  unfold envelope
  refine iSup₂_le fun h hh => le_iSup₂_of_le h ⟨hh.1, hh.2.trans hx⟩ ?_
  exact le_iInf₂ fun c hc => iInf₂_le c ⟨hc.1, hy.trans hc.2⟩

/-- On anchor cells the envelope is `F`. -/
theorem envelope_anchor (H C : Set α) {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {x y : α} (hx : x ∈ H) (hy : y ∈ C) : envelope H C F x y = F x y := by
  unfold envelope
  apply le_antisymm
  · exact iSup₂_le fun h hh => (iInf₂_le y ⟨hy, le_rfl⟩).trans (hF _ _ _ _ hh.2 le_rfl)
  · exact le_iSup₂_of_le x ⟨hx, le_rfl⟩ (le_iInf₂ fun c hc => hF _ _ _ _ le_rfl hc.2)

end A

end Mordor.IntervalRefinement
