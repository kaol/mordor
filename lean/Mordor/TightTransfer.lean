import Mordor.ColumnOrbitCell

/-!
# Cell targets between tight stages and the singleton reduction (round 26, §34.3z¹⁵⁵)

ChatGPT brief "TightIC, column-orbit GFP and lower-cell transfer" (HEAD fe00858).

* `Targets F H k` (the brief's `E_{k+1}`): elements `t` of height `k + 1` in `R_{k+1}` reached by a cell `(m, t)`
  from some `m ∈ R_k` of height `k`, `m < t`.
* `mem_targets_of_cell`: at a tight stage `k + 1` every such cell lands in `Targets`, and if stage `k` also
  satisfies the height bound, the target is new (`t ∉ R_k`).
* `b_le_of_lower`: a lower cell `F m t ≤ m` gives `b t ≤ m`.
* `ic_of_upper_target`: an upper target is diagonal, so it has an interval cell (as in `tightIC_succ_of_upper`).
* **Singleton reduction.** Let stage `k + 1` be tight with a unique top `m` of height `k + 1`, new (`m ∉ R_k`).
  - `single_prev_bound`: stage `k` satisfies the height bound `≤ k`.
  - `single_target_eq`: every cell `(m', y)` from a height-`k` element `m' ∈ R_k` has `y = m`.
  - `single_top_reduction`: given a TightIC witness at stage `k`, either `m` has an interval cell, or some
    `m' ∈ R_k` of height `k` lies below `m` with `F m' m ≤ m'` (the lower case, `b m ≤ m'`).
  So singleton TightIC at `k + 1` follows from TightIC at `k` plus lower transfer for the one-element target
  family `{m}`; the two programmes of the brief coincide there.
* `TightTransfer F H` (the brief's `tightIC_lower_transfer`, existential over the target family; **conjecture**)
  and `tightIC_step_of_transfer`: TightIC at an index-tight stage `k` and transfer give TightIC at the
  index-tight stage `k + 1`. The index bound at stage `k` cannot be weakened to `≤ k + 1`: offset-1 TightIC
  fails on a five-element lattice (log §34.3z¹⁵⁵).
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

/-- The cell-target family `E_{k+1}`. -/
def Targets (F : α →o α →o α) (H k : ℕ) : Set α :=
  {t | t ∈ Rk F (k + 1) ∧ height H t = k + 1 ∧
    ∃ m ∈ Rk F k, height H m = k ∧ m < t ∧ (F m t ≤ m ∨ t ≤ F m t)}

theorem mem_targets_of_cell {H : ℕ} (hn : NoChain α (H + 1)) {k : ℕ}
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m t : α} (hm : m ∈ Rk F k) (hmk : height H m = k)
    (hmt : m < t) (hw : F m t ≤ m ∨ t ≤ F m t) : t ∈ Targets F H k := by
  have ht := mem_succ_of_cell hm le_rfl hw
  have h1 := height_strictMono hn hmt
  have h2 := hall t ht
  exact ⟨ht, by omega, m, hm, hmk, hmt, hw⟩

theorem target_new {H : ℕ} {k : ℕ} (hprev : ∀ z ∈ Rk F k, height H z ≤ k) {t : α}
    (ht : t ∈ Targets F H k) : t ∉ Rk F k := fun h => by
  have := hprev t h
  have := ht.2.1
  omega

theorem b_le_of_lower {m t : α} (h : F m t ≤ m) : b F t ≤ m := b_le h

theorem ic_of_upper_target [WellFoundedLT α] {m t : α} (hmt : m < t) (hup : t ≤ F m t) (htop : t ≠ ⊤) :
    ∃ z, t < z ∧ (F t z ≤ t ∨ z ≤ F t z) :=
  upc_of_le_diag (hup.trans (F.mono hmt.le t)) htop

/-- A singleton new top forces the height bound one stage earlier. -/
theorem single_prev_bound {H : ℕ} {k : ℕ} (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m : α}
    (huniq : ∀ z ∈ Rk F (k + 1), height H z = k + 1 → z = m) (hnew : m ∉ Rk F k) :
    ∀ z ∈ Rk F k, height H z ≤ k := fun z hz => by
  have hz1 : z ∈ Rk F (k + 1) := Rk_mono (Nat.le_succ k) hz
  have := hall z hz1
  by_contra h
  exact hnew (huniq z hz1 (by omega) ▸ hz)

theorem single_target_eq {H : ℕ} (hn : NoChain α (H + 1)) {k : ℕ}
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m : α}
    (huniq : ∀ z ∈ Rk F (k + 1), height H z = k + 1 → z = m) {m' y : α} (hm' : m' ∈ Rk F k)
    (hm'k : height H m' = k) (hlt : m' < y) (hw : F m' y ≤ m' ∨ y ≤ F m' y) : y = m := by
  have ht := mem_targets_of_cell hn hall hm' hm'k hlt hw
  exact huniq y ht.1 ht.2.1

/-- **Singleton reduction.** -/
theorem single_top_reduction [WellFoundedLT α] {H : ℕ} (hn : NoChain α (H + 1)) {k : ℕ}
    (htop : (⊤ : α) ∉ Rk F (k + 2)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m : α}
    (huniq : ∀ z ∈ Rk F (k + 1), height H z = k + 1 → z = m)
    (hprev : ∃ m' ∈ Rk F k, height H m' = k ∧ ∃ y, m' < y ∧ (F m' y ≤ m' ∨ y ≤ F m' y)) :
    (∃ z, m < z ∧ (F m z ≤ m ∨ z ≤ F m z)) ∨
      ∃ m' ∈ Rk F k, height H m' = k ∧ m' < m ∧ F m' m ≤ m' := by
  obtain ⟨m', hm', hm'k, y, hlt, hw⟩ := hprev
  have hy := single_target_eq hn hall huniq hm' hm'k hlt hw
  subst hy
  rcases hw with hlo | hup
  · exact Or.inr ⟨m', hm', hm'k, hlt, hlo⟩
  · have hmR : y ∈ Rk F (k + 1) := mem_succ_of_cell hm' le_rfl (Or.inr hup)
    have hyt : y ≠ ⊤ := fun h => htop (h ▸ Rk_mono (Nat.le_succ _) hmR)
    exact Or.inl (ic_of_upper_target hlt hup hyt)

/-- **Lower-cell transfer** (conjecture, existential over the target family). -/
def TightTransfer (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k, (⊤ : α) ∉ Rk F (k + 2) → (∀ z ∈ Rk F k, height H z ≤ k) → (∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) →
    (Targets F H k).Nonempty → ∃ t ∈ Targets F H k, ∃ z, t < z ∧ (F t z ≤ t ∨ z ≤ F t z)

/-- **One step of the stage induction.** -/
theorem tightIC_step_of_transfer {H : ℕ} (hn : NoChain α (H + 1)) (htr : TightTransfer F H) {k : ℕ}
    (htop : (⊤ : α) ∉ Rk F (k + 2)) (hprev : ∀ z ∈ Rk F k, height H z ≤ k)
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    (hic : ∃ m ∈ Rk F k, height H m = k ∧ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) :
    ∃ t ∈ Rk F (k + 1), height H t = k + 1 ∧ ∃ z, t < z ∧ (F t z ≤ t ∨ z ≤ F t z) := by
  obtain ⟨m, hm, hmk, y, hlt, hw⟩ := hic
  obtain ⟨t, ht, hz⟩ := htr k htop hprev hall ⟨y, mem_targets_of_cell hn hall hm hmk hlt hw⟩
  exact ⟨t, ht.1, ht.2.1, hz⟩

end Mordor.OrbitHeight
