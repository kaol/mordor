import Mordor.SecondEntry

/-!
# Parent ancestry of top-layer elements (round 26, §34.3z¹⁶⁶)

ChatGPT brief "Parent ancestry and mixed-edge descent" (HEAD ef4e007).

* `a_parent_lift` (the brief's lemma, with `≤` in place of `=`): an A-parent `x ≤ a(p)`, `p ∈ R_j`, of a
  height-`(j+2)` element `z` of a tight `R_{j+2}` lifts to the A-parent `a(p) ∈ R_{j+1}`, and `z = a(a(p))`.
* `a_ancestry`, `aIter_mem`, `pureA_rigid`: iterated lifting. An A-ancestry `x ≤ a^[i] q`, `q ∈ R_j`, gives
  `z ≤ a^[i+1] q` with `a^[i] q ∈ R_{j+i}`; a pure A-ancestry from `R_0` means `z ≤ a^[k+1] ⊥`, impossible for
  `z ≠ ⊥` when `a ⊥ = ⊥` (rigid maps).
* `mixedParentSquare` (the brief's lemma; only `p ≤ F p x` is used): `p ⋖ x ≤ z`, `p ≤ F p x`, `b z = x`
  ⟹ `F p z = x`; `b_chain_relay`: for a B-chain `b x = p`, `b z = x` with `p ⋖ x ≤ z`, `F p z = x`.
* `TopParent`, `topParent_secondEntry`, `topParent_of_noLate`, `noLate_one`, `topParent_iff_secondEntry_one`:
  TopParent adds to SecondEntry exactly a statement about *late* elements (elements new at stage `k` of height
  `< k`): without late elements the two coincide, and at `k = 1` there are none, so there TopParent *is*
  SecondEntry.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} [CompleteLattice α] {F : α →o α →o α}

/-- **A-parent lifting.** -/
theorem a_parent_lift {j H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (j + 2), height H z ≤ j + 2)
    {p x z : α} (hp : p ∈ Rk F j) (hxa : x ≤ a F p) (hz : height H z = j + 2) (hA : z ≤ F x z) :
    a F p ∈ Rk F (j + 1) ∧ z = a F (a F p) ∧ F (a F p) z = z := by
  have h1 : a F p ∈ Rk F (j + 1) := mem_succ_of_a hp le_rfl
  have hle : z ≤ a F (a F p) := le_a (hA.trans ((F.mono hxa) z))
  have e : z = a F (a F p) := by
    by_contra hne
    have := height_strictMono hn (lt_of_le_of_ne hle hne)
    have := hall _ (mem_succ_of_a h1 le_rfl); omega
  refine ⟨h1, e, ?_⟩; rw [e]; exact row_a (a F p)

/-- Iterates of `a` climb the stages. -/
theorem aIter_mem {j : ℕ} {q : α} (hq : q ∈ Rk F j) : ∀ i, (a F)^[i] q ∈ Rk F (j + i)
  | 0 => hq
  | i + 1 => by
      rw [Function.iterate_succ_apply']
      exact mem_succ_of_a (aIter_mem hq i) le_rfl

/-- **A-ancestry.** An upper cell of a row below `a^[i] q` puts the column below `a^[i+1] q`. -/
theorem a_ancestry {x z q : α} {i : ℕ} (hxa : x ≤ (a F)^[i] q) (hA : z ≤ F x z) : z ≤ (a F)^[i + 1] q := by
  rw [Function.iterate_succ_apply']; exact le_a (hA.trans ((F.mono hxa) z))

/-- **Pure A-ancestry is void for rigid maps** (`a ⊥ = ⊥`). -/
theorem pureA_rigid (hr : a F ⊥ = ⊥) : ∀ i, (a F)^[i] (⊥ : α) = ⊥
  | 0 => rfl
  | i + 1 => by rw [Function.iterate_succ_apply', pureA_rigid hr i, hr]

/-- **Mixed parent square.** -/
theorem mixedParentSquare {p x z : α} (hcov : p ⋖ x) (hxz : x ≤ z) (hpx : p ≤ F p x) (hb : b F z = x) :
    F p z = x := by
  have hlo : p ≤ F p z := hpx.trans ((F p).mono hxz)
  have hhi : F p z ≤ x := ((F.mono hcov.le) z).trans (hb ▸ (col_b z).le)
  rcases hcov.eq_or_eq hlo hhi with e | e
  · exact absurd (hb ▸ b_le e.le) (not_le_of_gt hcov.lt)
  · exact e

/-- **B-chain relay.** -/
theorem b_chain_relay {p x z : α} (hcov : p ⋖ x) (hxz : x ≤ z) (hbx : b F x = p) (hbz : b F z = x) :
    F p z = x :=
  mixedParentSquare hcov hxz (hbx ▸ (col_b x).ge) hbz

/-- TopParent: a second top of `R_{k+1}` with a fixed-edge parent of height `k` in `R_k`. -/
def TopParent (F : α →o α →o α) (H k : ℕ) (m : α) : Prop :=
  ∃ z x, z ≠ m ∧ height H z = k + 1 ∧ z ∈ Rk F (k + 1) ∧ x ∈ Rk F k ∧ height H x = k ∧ (F x z = x ∨ F x z = z)

theorem topParent_secondEntry {H k : ℕ} {m : α} (h : TopParent F H k m) : SecondEntry F H k m := by
  obtain ⟨z, x, hzm, hz, hzR, -⟩ := h; exact ⟨z, hzm, hz, hzR⟩

/-- **Without late elements TopParent is SecondEntry.** If every element new at stage `j + 1` has height `j + 1`,
SecondEntry at stage `j + 1` gives TopParent (the parent is new by `top_parent_new`). -/
theorem topParent_of_noLate {j H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    (hall : ∀ z ∈ Rk F (j + 2), height H z ≤ j + 2)
    (hnolate : ∀ x ∈ Rk F (j + 1), x ∉ Rk F j → height H x = j + 1) {m : α}
    (h : SecondEntry F H (j + 1) m) : TopParent F H (j + 1) m := by
  obtain ⟨z, hzm, hz, hzR⟩ := h
  obtain ⟨x, hx, he⟩ := (topLayerEntry_iff_fixed_edge hn hk hall hz).1 hzR
  have hcell : F x z ≤ x ∨ z ≤ F x z := he.imp (fun e => e.le) (fun e => e.ge)
  exact ⟨z, x, hzm, hz, hzR, hx, hnolate x hx (top_parent_new hk hz hcell), he⟩

/-- No late elements at stage `1`. -/
theorem noLate_one {H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F 1, height H z ≤ 1) :
    ∀ x ∈ Rk F 1, x ∉ Rk F 0 → height H x = 1 := by
  intro x hx h0
  have hb : (⊥ : α) < x := bot_lt_iff_ne_bot.2 fun e => h0 (e ▸ bot_mem_Rk 0)
  have := height_strictMono hn hb; have := hk x hx; omega

/-- **At `k = 1` TopParent is SecondEntry.** -/
theorem topParent_iff_secondEntry_one {H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F 1, height H z ≤ 1)
    (hall : ∀ z ∈ Rk F 2, height H z ≤ 2) {m : α} : TopParent F H 1 m ↔ SecondEntry F H 1 m :=
  ⟨topParent_secondEntry, topParent_of_noLate (j := 0) hn hk hall (noLate_one hn hk)⟩

end Mordor.OrbitHeight
