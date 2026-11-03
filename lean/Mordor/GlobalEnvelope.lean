import Mordor.BranchFrontier
import Mathlib.Order.CompleteLattice.Basic

/-!
# Global frontier envelopes and the mixed-type squeeze (round 26, §34.3z⁹⁶)

Response to the brief "global frontier envelopes". `α` a complete lattice, `D` a down-set (`InD`), `F` monotone, no
witness. A family of frontier pairs `(x v, y v)`, `v : V` (nonempty): `z v = F (x v) (y v)`,
`y v ⊓ z v ∈ D`, `x v ⊔ z v ∉ D`.

* `envelope`: `d = ⨅ v, x v ⊓ (y v ⊓ z v) ∈ D`, `u = ⨆ v, y v ⊔ (x v ⊔ z v) ∉ D`, and `d ≤ x v, y v, z v ≤ u`.
  Lattice facts only (no `F` beyond `z`'s definition).
* `mixed_squeeze`: with `L = d ⊔ ⨆_{v∈A} F d (y v)` and `U = u ⊓ ⨅_{w∈B} F (x w) u`: `d < L ≤ U < u`
  (`L ≤ U` uses `d ≤ a_w ≤ z_w ≤ F (x_w) u`). **The type hypotheses of the brief are not needed**: any nonempty `A`,
  `B` and any cross pairs (not only frontier pairs) will do. It is a frontier step at `(d, u)`.
* `squeeze_cross_pair`: one of `(L, U)`, `(d, L)`, `(U, u)` is a cross pair, each strictly below `(d, u)` in the product
  order (row up, column down).
* For one generator type A never occurs (`principal_join_closed`), so the mixed squeeze is vacuous there; the
  one-generator case must come from the monochromatic type-B tree.
-/

namespace Mordor.Profile

set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] {InD : α → Prop} {F : α → α → α}
  (hdown : ∀ x y, x ≤ y → InD y → InD x)
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
  (nw : ∀ x, InD x → ∀ y, ¬ InD y → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
  {V : Type*} (x y : V → α)

include hdown in
/-- **The global envelope.** -/
theorem envelope [Nonempty V] (hx : ∀ v, InD (x v))
    (hy : ∀ v, ¬ InD (y v)) :
    InD (⨅ v, x v ⊓ (y v ⊓ F (x v) (y v))) ∧ ¬ InD (⨆ v, y v ⊔ (x v ⊔ F (x v) (y v))) ∧
    ∀ v, (⨅ v, x v ⊓ (y v ⊓ F (x v) (y v))) ≤ x v ⊓ (y v ⊓ F (x v) (y v)) ∧
      x v ⊔ (y v ⊔ F (x v) (y v)) ≤ ⨆ v, y v ⊔ (x v ⊔ F (x v) (y v)) := by
  obtain ⟨v₀⟩ := ‹Nonempty V›
  refine ⟨hdown _ _ ((iInf_le _ v₀).trans inf_le_left) (hx v₀), fun h => hy v₀ (hdown _ _ ((le_sup_left).trans
    (le_iSup (fun v => y v ⊔ (x v ⊔ F (x v) (y v))) v₀)) h), fun v => ⟨iInf_le _ v, ?_⟩⟩
  exact (sup_le (le_sup_left.trans le_sup_right) (sup_le le_sup_left (le_sup_right.trans le_sup_right))).trans
    (le_iSup (fun v => y v ⊔ (x v ⊔ F (x v) (y v))) v)

include hdown hF nw in
/-- **The mixed-type squeeze**, in its true generality: it holds for **any** nonempty index sets `A`, `B` of **any**
family of cross pairs. Neither the types (`z ∈ D` on `A`, `z ∉ D` on `B`) nor the frontier property are used: the
types only make `F d (y v) ∈ D` and `F (x w) u ∉ D`. It is the frontier step `cross_frontier_step` at the envelope
pair `(d, u)`. -/
theorem mixed_squeeze (hx : ∀ v, InD (x v)) (hy : ∀ v, ¬ InD (y v)) (A B : Set V) {vA wB : V} (hvA : vA ∈ A) (hwB : wB ∈ B) :
    let d := ⨅ v, x v ⊓ (y v ⊓ F (x v) (y v))
    let u := ⨆ v, y v ⊔ (x v ⊔ F (x v) (y v))
    let L := d ⊔ ⨆ v ∈ A, F d (y v)
    let U := u ⊓ ⨅ w ∈ B, F (x w) u
    d < L ∧ L ≤ U ∧ U < u := by
  intro d u L U
  have hdx : ∀ v, d ≤ x v := fun v => (iInf_le _ v).trans inf_le_left
  have hda : ∀ v, d ≤ y v ⊓ F (x v) (y v) := fun v => (iInf_le _ v).trans inf_le_right
  have hyu : ∀ v, y v ≤ u := fun v => le_sup_left.trans (le_iSup (fun v => y v ⊔ (x v ⊔ F (x v) (y v))) v)
  have hzu : ∀ v, F (x v) (y v) ≤ u := fun v =>
    (le_sup_right.trans le_sup_right).trans (le_iSup (fun v => y v ⊔ (x v ⊔ F (x v) (y v))) v)
  have hdD : InD d := hdown _ _ (hdx wB) (hx wB)
  have huD : ¬ InD u := fun h => hy wB (hdown _ _ (hyu wB) h)
  refine ⟨lt_of_le_of_ne le_sup_left fun e => ?_, sup_le (le_inf ?_ ?_) (iSup₂_le fun v hv => le_inf ?_ ?_),
    lt_of_le_of_ne inf_le_left fun e => ?_⟩
  · -- `F d (y vA) ≤ d` contradicts no witness at `(d, y vA)`
    have h1 : F d (y vA) ≤ L := le_sup_of_le_right (le_iSup₂_of_le vA hvA le_rfl)
    rw [← e] at h1
    exact (nw d hdD _ (hy vA)).1 h1
  · exact (hdx wB).trans ((le_sup_left.trans le_sup_right).trans (le_iSup (fun v => y v ⊔ (x v ⊔ F (x v) (y v))) wB))
  · exact le_iInf₂ fun w _ => ((hda w).trans inf_le_right).trans (hF _ _ _ _ le_rfl (hyu w))
  · exact (hF _ _ _ _ (hdx v) le_rfl).trans (hzu v)
  · exact le_iInf₂ fun w _ => hF _ _ _ _ (hdx w) (hyu v)
  · -- `u ≤ F (x wB) u` contradicts no witness at `(x wB, u)`
    have h1 : U ≤ ⨅ w ∈ B, F (x w) u := inf_le_right
    rw [e] at h1
    exact (nw _ (hx wB) u huD).2 (h1.trans (iInf₂_le wB hwB))

/-- **Cross-pair extraction** from `d < L ≤ U < u` with `d ∈ D`, `u ∉ D`. -/
theorem squeeze_cross_pair {d L U u : α} (hdD : InD d) (huD : ¬ InD u)
    (hdL : d < L) (hLU : L ≤ U) (hUu : U < u) :
    (InD L ∧ ¬ InD U ∧ d < L ∧ U < u) ∨ (InD d ∧ ¬ InD L ∧ L < u) ∨ (InD U ∧ ¬ InD u ∧ d < U) := by
  by_cases hL : InD L
  · by_cases hU : InD U
    · exact Or.inr (Or.inr ⟨hU, huD, hdL.trans_le hLU⟩)
    · exact Or.inl ⟨hL, hU, hdL, hUu⟩
  · exact Or.inr (Or.inl ⟨hdD, hL, hLU.trans_lt hUu⟩)

end Mordor.Profile
