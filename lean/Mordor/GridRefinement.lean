import Mordor.FirstEntryBoundary

/-!
# Full-capture refinement of orbit grids: uncaptured columns hang from outside columns (round 26, §34.3z¹¹¹)

Rows `g' : Fin k' → α`, a sub-family `g' ∘ e` (`e` any map, typically an embedding), orbits
`uᵢ(n) = (F g'ᵢ)^[n] s₀` from a column `s₀` contracting for every row, grid columns `W`.

* `W_le_proj`: a column of the larger grid lies below its projection to the sub-grid.
* **`uncaptured_parent_outside`**: if the larger family contains a capturer of every `D`-valued column of the
  sub-grid that the sub-family does not capture ("full-capture refinement"), then every `D`-valued column of the
  larger grid that it leaves uncaptured projects onto an **outside** column of the sub-grid.
* `aggregate_contracts`: every grid column is contracting for the aggregate row `⨅ g`: `F (⨅ g) (W t) ≤ W t`.

Consequence (§34.3z¹¹¹, König): in a counterexample the full-capture refinement process has a persistent outside
column `o` (a column of some finite grid, contracting for that grid's aggregate row) with infinitely many uncaptured
`D`-valued columns below it.
-/

namespace Mordor.GridRefinement
open Finset Mordor.AsyncGrid

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [OrderTop α] {k k' : ℕ}

/-- A column of the larger grid lies below its projection. -/
theorem W_le_proj (u : Fin k' → ℕ → α) (e : Fin k → Fin k') (t : Fin k' → ℕ) :
    W u t ≤ W (fun j => u (e j)) (fun j => t (e j)) :=
  Finset.le_inf fun j _ => W_le u t (e j)

/-- **Uncaptured columns of a full-capture refinement hang from outside columns.** -/
theorem uncaptured_parent_outside {D : Set α} (g' : Fin k' → α)
    (u : Fin k' → ℕ → α) (e : Fin k → Fin k')
    (hfull : ∀ t : Fin k → ℕ, W (fun j => u (e j)) t ∈ D → ∃ i, W (fun j => u (e j)) t ≤ g' i)
    {t : Fin k' → ℕ} (hunc : ∀ i, ¬ W u t ≤ g' i) :
    W (fun j => u (e j)) (fun j => t (e j)) ∉ D ∧ W u t ≤ W (fun j => u (e j)) (fun j => t (e j)) := by
  refine ⟨fun hproj => ?_, W_le_proj u e t⟩
  obtain ⟨i, hi⟩ := hfull _ hproj
  exact hunc i ((W_le_proj u e t).trans hi)

/-- **Grid columns contract for the aggregate row.** -/
theorem aggregate_contracts {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (g : Fin k → α) {s₀ : α} (hgs : ∀ i, F (g i) s₀ ≤ s₀) (t : Fin k → ℕ) :
    F (univ.inf g) (W (fun i m => (F (g i))^[m] s₀) t) ≤ W (fun i m => (F (g i))^[m] s₀) t :=
  (asynchronous_meet_step hF g univ t).trans (Finset.le_inf fun i _ =>
    (Finset.inf_le (f := fun i => (F (g i))^[t i + 1] s₀) (mem_univ i)).trans
      (Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) (hgs i) (Nat.le_succ _)))

end Mordor.GridRefinement
