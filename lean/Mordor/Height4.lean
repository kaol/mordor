import Mordor.CutHeight4

/-!
# CL at edge-height ≤ 4 (E_ω included)

`CutHeight4.lean` (generated) proves the Cut Lemma in every bounded poset with no chain of six elements, from a
drat-trim-verified unsat core of the ground cut theory, replayed by `bv_decide`. Here it is specialised to complete
lattices and combined with `semi_of_cut`: semi-commutation, and so commutation, forces `μν = νμ` on every complete
lattice of edge-height ≤ 4 — including the log's last named frontier lattice `E_ω` (columns of 3-chains, §21–§23).
`cutCells_of_poset` is the specialisation for any poset-level certificate (`Height5.lean` reuses it).
-/

namespace Mordor
open Ground

variable {α : Type*} [CompleteLattice α]

/-- The Cut Lemma for all monotone bifunctions on a bounded poset, in the form the generated certificates prove. -/
def PosetCut (α : Type*) [PartialOrder α] [OrderBot α] [OrderTop α] : Prop :=
  ∀ (F : α → α → α), (∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') →
    ∀ (D : Set α), (∀ x y, x ≤ y → y ∈ D → x ∈ D) → ⊥ ∈ D → ⊤ ∉ D →
      ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y)

theorem cutCells_of_poset (h : PosetCut α) (G : α →o α →o α) : CutCells G := by
  intro D hD ⟨d, hd⟩ ⟨u, hu⟩
  have hbot : ⊥ ∈ D := hD bot_le hd
  have htop : ⊤ ∉ D := fun h => hu (hD le_top h)
  obtain ⟨x, hx, y, hy, h⟩ := h (fun x y => G x y)
    (fun x x' y y' hx hy => (G.mono hx y).trans ((G x').mono hy)) D (fun x y h hy => hD h hy) hbot htop
  exact ⟨x, hx, y, hy, h⟩

theorem cut_height4' (hn : NoChain α 5) (G : α →o α →o α) : CutCells G :=
  cutCells_of_poset (fun F hF D hD hb ht => cut_height4 hn F hF D hD hb ht) G

/-- **Semi-CL at edge-height ≤ 4.** -/
theorem semi_height4 (hn : NoChain α 5) (G : α →o α →o α)
    (hsemi : ∀ x, b G (a G x) ≤ a G (b G x)) : m G = n G :=
  semi_of_cut (cutMaps_of_cells (cut_height4' hn G)) hsemi

/-- **CL at edge-height ≤ 4.** -/
theorem cl_height4 (hn : NoChain α 5) (G : α →o α →o α)
    (hc : ∀ x, a G (b G x) = b G (a G x)) : m G = n G :=
  semi_height4 hn G fun x => (hc x).ge

end Mordor
