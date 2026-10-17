import Mordor.CutHeight4

/-!
# CL at edge-height ≤ 4 (E_ω included)

`CutHeight4.lean` (generated) proves the Cut Lemma in every bounded poset with no chain of six elements, from a
drat-trim-verified unsat core of the ground cut theory, replayed by `bv_decide`. Here it is specialised to complete
lattices and combined with `semi_of_cut`: semi-commutation, and so commutation, forces `μν = νμ` on every complete
lattice of edge-height ≤ 4 — including the log's last named frontier lattice `E_ω` (columns of 3-chains, §21–§23).
-/

namespace Mordor
open Ground

variable {α : Type*} [CompleteLattice α]

theorem cut_height4' (hn : NoChain α 5) (G : α →o α →o α) : CutCells G := by
  intro D hD ⟨d, hd⟩ ⟨u, hu⟩
  have hbot : ⊥ ∈ D := hD bot_le hd
  have htop : ⊤ ∉ D := fun h => hu (hD le_top h)
  obtain ⟨x, hx, y, hy, h⟩ := cut_height4 hn (fun x y => G x y)
    (fun x x' y y' hx hy => (G.mono hx y).trans ((G x').mono hy)) D (fun x y h hy => hD h hy) hbot htop
  exact ⟨x, hx, y, hy, h⟩

/-- **Semi-CL at edge-height ≤ 4.** -/
theorem semi_height4 (hn : NoChain α 5) (G : α →o α →o α)
    (hsemi : ∀ x, b G (a G x) ≤ a G (b G x)) : m G = n G :=
  semi_of_cut (cutMaps_of_cells (cut_height4' hn G)) hsemi

/-- **CL at edge-height ≤ 4.** -/
theorem cl_height4 (hn : NoChain α 5) (G : α →o α →o α)
    (hc : ∀ x, a G (b G x) = b G (a G x)) : m G = n G :=
  semi_height4 hn G fun x => (hc x).ge

end Mordor
