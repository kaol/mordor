import Mordor.Height4
import Mordor.CutHeight5

/-!
# CL at edge-height ≤ 5

`CutHeight5.lean` (generated) proves the Cut Lemma in every bounded poset with no chain of seven elements: a
drat-trim-verified unsat core (832 ground clauses over 86 F-terms, under `F(⊥,⊤) ∉ D`, removed by
`cut_of_wlog`) of the ground cut theory, found by the tightness-guided term selection of
`experiments/sat/cut_ground.py` (log §34.3h) and replayed by `bv_decide`.
-/

namespace Mordor
open Ground

variable {α : Type*} [CompleteLattice α]

theorem cut_height5' (hn : NoChain α 6) (G : α →o α →o α) : CutCells G :=
  cutCells_of_poset (fun F hF D hD hb ht => cut_height5 hn F hF D hD hb ht) G

/-- **Semi-CL at edge-height ≤ 5.** -/
theorem semi_height5 (hn : NoChain α 6) (G : α →o α →o α)
    (hsemi : ∀ x, b G (a G x) ≤ a G (b G x)) : m G = n G :=
  semi_of_cut (cutMaps_of_cells (cut_height5' hn G)) hsemi

/-- **CL at edge-height ≤ 5.** -/
theorem cl_height5 (hn : NoChain α 6) (G : α →o α →o α)
    (hc : ∀ x, a G (b G x) = b G (a G x)) : m G = n G :=
  semi_height5 hn G fun x => (hc x).ge

end Mordor
