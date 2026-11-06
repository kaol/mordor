import Mordor.PivotReplacement

/-!
# Dominated rows: geometry without capture (round 26, §34.3z¹¹⁴)

Follow-up to §34.3z¹¹³ ("add only dominated rows `h ≤ m_T`"). Orbits from `⊤`.

* `dominated_row_no_capture`: a row `h ≤ g` captures nothing that `g` does not capture — refinement by dominated rows
  never enlarges the captured region.
* `dominated_column_below_old`: if every row of the enlarged family lies below the row `g (σ j)` it is assigned to,
  every column of the enlarged grid lies below the column of the *original* rows at the raised index
  `t' = s ∘ τ` for a section `τ` of the row assignment `σ`. Proof: orbit comparison (`orbit_le_of_le`).
* `dominated_parent_lt_top`: a column using an orbit point `uᵢ(n)` with `n ≥ 1` lies strictly below `⊤` under no
  witness (`F gᵢ ⊤ = ⊤` would be a witness). So parents of dominated refinements are never the vacuous `⊤`.
* `capture_needs_nondominated`, `alt1_row_dominated`: Alternative-I rows `F(m_T, c) ≤ m_T` are dominated, hence inert;
  any row capturing a new column (e.g. an Alternative-II pivot used as a row) is dominated by no old row.
* `dominated_entry_no_later`, `uncaptured_parent_of_child`, `orbit_stabilizes`: dominated orbits enter `D` no later;
  uncaptured new columns sit below uncaptured old columns; under DCC the old grid has finitely many columns.
Dichotomy (§34.3z¹¹⁴): dominated rows keep the grid tied to a fixed finite parent grid but cannot capture;
non-dominated rows can capture, but their orbits are unconstrained (the fresh first-entry pivots of §34.3z¹¹³).
-/

namespace Mordor.DominatedRows
open Finset Mordor.AsyncGrid

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [OrderTop α]

/-- A dominated row captures nothing new. -/
theorem dominated_row_no_capture {h g c : α} (hhg : h ≤ g) (hc : c ≤ h) : c ≤ g := hc.trans hhg

/-- Orbit comparison (`paired_orbit_order` for a lattice with top). -/
theorem orbit_le_of_le {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {c d : α}
    (hcd : c ≤ d) (s : α) : ∀ n : ℕ, (F c)^[n] s ≤ (F d)^[n] s
  | 0 => le_rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hF _ _ _ _ hcd (orbit_le_of_le hF hcd s n)

/-- **Capturing rows are never dominated.** A row that captures a column escaping every old row is below no old
row. In particular an uncaptured column used as a new row (Alternative II, `h = p_T`) is non-dominated. -/
theorem capture_needs_nondominated {ι : Type*} (g : ι → α) {h c : α} (hc : ∀ i, ¬ c ≤ g i) (hch : c ≤ h) :
    ∀ i, ¬ h ≤ g i :=
  fun i hi => hc i (hch.trans hi)

/-- **Alternative-I rows are dominated.** `F(m_T, c) ≤ m_T ≤ gᵢ` for `i ∈ T`; hence (by `dominated_row_no_capture`)
Alternative-I refinement never captures a new column. -/
theorem alt1_row_dominated {ι : Type*} (g : ι → α) (T : Finset ι) {i : ι} (hi : i ∈ T) {F : α → α → α} {c : α}
    (halt : F (T.inf g) c ≤ T.inf g) : F (T.inf g) c ≤ g i :=
  halt.trans (Finset.inf_le hi)

/-- **Columns of a dominated refinement lie below columns of the original grid.** Rows `r j ≤ g (σ j)`; the column of
the enlarged family at `s` lies below the original column at `fun i => ⨆_{σ j = i} s j` — here stated for one
coordinate per original row: `t' i := s (τ i)` for any choice `τ` with `σ (τ i) = i`. -/
theorem dominated_column_below_old {k l : ℕ} {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (g : Fin k → α) (r : Fin l → α) (σ : Fin l → Fin k)
    (hdom : ∀ j, r j ≤ g (σ j)) (τ : Fin k → Fin l) (hτ : ∀ i, σ (τ i) = i) (s : Fin l → ℕ) :
    W (fun j m => (F (r j))^[m] ⊤) s ≤ W (fun i m => (F (g i))^[m] ⊤) (fun i => s (τ i)) := by
  refine Finset.le_inf fun i _ => (W_le _ s (τ i)).trans ?_
  have h := orbit_le_of_le hF (hdom (τ i)) ⊤ (s (τ i))
  rw [hτ i] at h; exact h

/-- **Parents of dominated refinements are below `⊤`.** -/
theorem dominated_parent_lt_top {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {D : Set α} (htop : ⊤ ∉ D) (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {g : α} (hg : g ∈ D) {n : ℕ}
    (hn : 1 ≤ n) : (F g)^[n] ⊤ < ⊤ := by
  have h1 : F g ⊤ < ⊤ := lt_of_le_of_ne le_top fun he => (nw g hg ⊤ htop).2 he.ge
  have hanti : Antitone fun m => (F g)^[m] ⊤ :=
    Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) le_top
  exact lt_of_le_of_lt (hanti hn) (by simpa using h1)

/-- **Dominated orbits enter no later.** If the dominating orbit is in `D` at time `n`, so is the dominated one. -/
theorem dominated_entry_no_later {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) {h g : α} (hhg : h ≤ g) {n : ℕ}
    (hn : (F g)^[n] ⊤ ∈ D) : (F h)^[n] ⊤ ∈ D :=
  hD _ _ (orbit_le_of_le hF hhg ⊤ n) hn

/-- **Uncaptured children have uncaptured parents.** If a column `c` lies below an old column `P` and `c` escapes
every old row, so does `P`; with `dominated_column_below_old`, the uncaptured columns of any dominated refinement
lie below uncaptured columns of the original grid. -/
theorem uncaptured_parent_of_child {ι : Type*} (g : ι → α) {c P : α} (hcP : c ≤ P) (hc : ∀ i, ¬ c ≤ g i) :
    ∀ i, ¬ P ≤ g i :=
  fun i hP => hc i (hcP.trans hP)

/-- **The parent grid is finite under DCC.** Each orbit from `⊤` stabilizes, so the original grid has finitely many
distinct columns, and every column of every dominated refinement lies below one of them. -/
theorem orbit_stabilizes [WellFoundedLT α] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (g : α) :
    ∃ N, ∀ n ≥ N, (F g)^[n] ⊤ = (F g)^[N] ⊤ :=
  Mordor.PivotReplacement.antitone_stabilizes
    (Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) le_top)

end Mordor.DominatedRows
