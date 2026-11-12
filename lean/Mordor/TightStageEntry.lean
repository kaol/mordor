import Mordor.OrbitHeight

/-!
# Entry routes of the tight-stage top layer (round 26, §34.3z¹⁵²)

ChatGPT brief "Tight-stage predecessor geometry and boundary escape graphs" (HEAD d2d67a0).

At a tight stage (`∀ z ∈ R_k, height z ≤ k`) let `m ∈ R_k` have height `k > 0`. A top element need not be new at
stage `k` (it may already lie in `R_{k−1}`), so the split is taken at its **first-entry stage** `j + 1 ≤ k`:

* `tight_entry_split`: some `j < k` has `m ∉ R_j`, `m ∈ R_{j+1}` and
  - **a-entry**: `m = a x` for some `x ∈ R_j`, with `F x m = m` and `m ≰ x`; or
  - **b-entry**: `b m ∈ R_j`, with `F (b m) m = b m`.
  The generator of `m` in `step R_j` lies in `R_k`, so tightness and `height_strictMono` force it to equal `m`.
* `tightIC_of_aentry_le`: an a-entry with `x ≤ m` is diagonal (`le_diag_of_a`), hence has an interval cell
  (`upc_of_le_diag`). The open a-entry case is `x ∥ m`.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

/-- **The entry split.** -/
theorem tight_entry_split {H : ℕ} (hn : NoChain α (H + 1)) {k : ℕ} (hall : ∀ z ∈ Rk F k, height H z ≤ k)
    {m : α} (hm : m ∈ Rk F k) (hmk : height H m = k) (hm0 : m ≠ ⊥) :
    ∃ j, j < k ∧ m ∉ Rk F j ∧ m ∈ Rk F (j + 1) ∧
      ((∃ x ∈ Rk F j, m = a F x ∧ F x m = m ∧ ¬ m ≤ x) ∨ (b F m ∈ Rk F j ∧ F (b F m) m = b F m)) := by
  classical
  have hex : ∃ i, m ∈ Rk F i := ⟨k, hm⟩
  set i₀ := Nat.find hex with hi₀
  have hi₀k : i₀ ≤ k := Nat.find_min' hex hm
  have hmi₀ : m ∈ Rk F i₀ := Nat.find_spec hex
  have hi₀pos : i₀ ≠ 0 := fun h => hm0 (le_antisymm (by rw [h] at hmi₀; exact hmi₀) bot_le)
  obtain ⟨j, hj⟩ : ∃ j, i₀ = j + 1 := ⟨i₀ - 1, by omega⟩
  have hmj : m ∉ Rk F j := Nat.find_min hex (by omega)
  have hmj1 : m ∈ Rk F (j + 1) := hj ▸ hmi₀
  -- an element of `R_k` above `m` equals `m`
  have heq : ∀ g, m ≤ g → g ∈ Rk F k → g = m := fun g hmg hg => by
    by_contra hne
    have := height_strictMono hn (lt_of_le_of_ne hmg (Ne.symm hne))
    have := hall g hg
    omega
  have hjk : j + 1 ≤ k := hj ▸ hi₀k
  have hsub : Rk F (j + 1) ⊆ Rk F k := Rk_mono hjk
  refine ⟨j, by omega, hmj, hmj1, ?_⟩
  have hstep := hmj1
  rw [Rk_succ] at hstep
  obtain ⟨g, hmg, hg⟩ := hstep
  have hgR : g ∈ Rk F (j + 1) := by rw [Rk_succ]; exact ⟨g, le_rfl, hg⟩
  have hgm : g = m := heq g hmg (hsub hgR)
  subst hgm
  rcases hg with hgj | ⟨x, hx, hgx⟩ | hbg
  · exact absurd hgj hmj
  · left
    refine ⟨x, hx, hgx, hgx ▸ row_a x, fun hgx' => hmj ?_⟩
    have hxk : x ∈ Rk F k := Rk_mono (by omega) hx
    have := heq x hgx' hxk
    exact this ▸ hx
  · exact Or.inr ⟨hbg, col_b g⟩

/-- **An a-entry below its top element has an interval cell.** -/
theorem tightIC_of_aentry_le [WellFoundedLT α] {m x : α} (hmx : m = a F x) (hxm : x ≤ m) (ht : m ≠ ⊤) :
    ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y) :=
  upc_of_le_diag (hmx ▸ le_diag_of_a (hmx ▸ hxm)) ht

end Mordor.OrbitHeight
