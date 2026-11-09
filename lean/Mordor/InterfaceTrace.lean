import Mordor.IntervalRefinement

/-!
# Interface traces of a confinement region (round 26, §34.3z¹²⁵)

ChatGPT brief "interface preservation and separator ancestry", Programme A.

`G : α × α → α` monotone in the product order, `S` any set of cells (the brief's `S_I = G⁻¹[w, v]`).
* `lowTrace S G p = ⨆_{q ∉ S, q ≤ p} G q`, `highTrace S G p = ⨅_{q ∉ S, p ≤ q} G q`.
* `lowTrace_mono`, `highTrace_mono`; `lowTrace_le_highTrace` (G monotone); `lowTrace_outside`, `highTrace_outside`
  (both recover `G` off `S`); `between_traces`: every monotone `G'` agreeing with `G` off `S` satisfies
  `lowTrace ≤ G' ≤ highTrace` — the external order obligations of a modification supported on `S`.
-/

namespace Mordor.InterfaceTrace

set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] (S : Set (α × α)) (G : α × α → α)

noncomputable def lowTrace (p : α × α) : α := ⨆ q ∈ {q | q ∉ S ∧ q ≤ p}, G q
noncomputable def highTrace (p : α × α) : α := ⨅ q ∈ {q | q ∉ S ∧ p ≤ q}, G q

theorem lowTrace_mono : Monotone (lowTrace S G) := fun _ _ h =>
  iSup₂_le fun q hq => le_iSup₂_of_le q ⟨hq.1, hq.2.trans h⟩ le_rfl

theorem highTrace_mono : Monotone (highTrace S G) := fun _ _ h =>
  le_iInf₂ fun q hq => iInf₂_le q ⟨hq.1, h.trans hq.2⟩

variable {S G}

theorem lowTrace_le_highTrace (hG : Monotone G) (p : α × α) : lowTrace S G p ≤ highTrace S G p :=
  iSup₂_le fun _ hq => le_iInf₂ fun _ hq' => hG (hq.2.trans hq'.2)

theorem lowTrace_outside (hG : Monotone G) {p : α × α} (hp : p ∉ S) : lowTrace S G p = G p :=
  le_antisymm (iSup₂_le fun _ hq => hG hq.2) (le_iSup₂_of_le p ⟨hp, le_rfl⟩ le_rfl)

theorem highTrace_outside (hG : Monotone G) {p : α × α} (hp : p ∉ S) : highTrace S G p = G p :=
  le_antisymm (iInf₂_le p ⟨hp, le_rfl⟩) (le_iInf₂ fun _ hq => hG hq.2)

/-- **External obligations.** -/
theorem between_traces {G' : α × α → α} (hG' : Monotone G') (hagree : ∀ q, q ∉ S → G' q = G q) (p : α × α) :
    lowTrace S G p ≤ G' p ∧ G' p ≤ highTrace S G p :=
  ⟨iSup₂_le fun q hq => (hagree q hq.1) ▸ hG' hq.2, le_iInf₂ fun q hq => (hagree q hq.1) ▸ hG' hq.2⟩

end Mordor.InterfaceTrace
