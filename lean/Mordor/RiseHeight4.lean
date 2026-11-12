import Mordor.HeightInduction

/-!
# Boundary orbits, the mixed grid, and the final-stage TightIC bridge (round 26, §34.3z¹⁵⁹)

ChatGPT brief "Rise at height four via two-sided boundary orbits" (HEAD 601eb5c).

* Boundary orbits `uSeq F n = (x ↦ F x ⊤)^[n] ⊥` and `dSeq F n = (y ↦ F ⊥ y)^[n] ⊤`, with `u₁ = d₁ = F ⊥ ⊤`.
  - `uSeq_le_succ`, `dSeq_succ_le`: `u` ascends, `d` descends.
  - `uSeq_lt_succ` (`b ⊤ = ⊤`): `u n ≠ ⊤ → u n < u (n+1)`; `dSeq_succ_lt` (`a ⊥ = ⊥`): `d n ≠ ⊥ → d (n+1) < d n`.
  - Endpoints at edge-height `≤ H`: `uSeq_eq_top` (`u H = ⊤`), `dSeq_eq_bot` (`d H = ⊥`).
  - `exists_last_u`: some `u n < ⊤` has `F (u n) ⊤ = ⊤`, hence `u n < a (u n) = ⊤`.
* Mixed grid `z_ij = F (u i) (d j)`: `grid_bounds`: `d (j+1) ≤ z_ij ≤ u (i+1)`.
* **Final-stage TightIC bridge.** `top_mem_of_lastIC`: a TightIC witness at stage `H − 1` (a height-`(H−1)` element
  of `R_{H−1}` with a cell) gives `⊤ ∈ R_H` (its column is forced to be `⊤`); `rise_of_lastIC` (`b ⊤ = ⊤`): the
  cell is then upper and the witness is a good `m < a m = ⊤` — Rise. `top_mem_of_tightIC_last`: `TightIC F H`
  at the last stage alone gives `⊤ ∈ R_H`.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

/-- The ascending boundary orbit `⊥, F(⊥, ⊤), F(F(⊥, ⊤), ⊤), …` (column `⊤`). -/
def uSeq (F : α →o α →o α) (n : ℕ) : α := (fun x => F x ⊤)^[n] ⊥
/-- The descending boundary orbit `⊤, F(⊥, ⊤), F(⊥, F(⊥, ⊤)), …` (row `⊥`). -/
def dSeq (F : α →o α →o α) (n : ℕ) : α := (fun y => F ⊥ y)^[n] ⊤

theorem uSeq_succ (n : ℕ) : uSeq F (n + 1) = F (uSeq F n) ⊤ := Function.iterate_succ_apply' _ _ _
theorem dSeq_succ (n : ℕ) : dSeq F (n + 1) = F ⊥ (dSeq F n) := Function.iterate_succ_apply' _ _ _
theorem uSeq_one_eq_dSeq_one : uSeq F 1 = dSeq F 1 := by rw [uSeq_succ, dSeq_succ]; rfl

theorem uSeq_le_succ : ∀ n, uSeq F n ≤ uSeq F (n + 1)
  | 0 => bot_le
  | n + 1 => calc
      uSeq F (n + 1) = F (uSeq F n) ⊤ := uSeq_succ n
      _ ≤ F (uSeq F (n + 1)) ⊤ := F.mono (uSeq_le_succ n) ⊤
      _ = uSeq F (n + 2) := (uSeq_succ (n + 1)).symm

theorem dSeq_succ_le : ∀ n, dSeq F (n + 1) ≤ dSeq F n
  | 0 => le_top
  | n + 1 => calc
      dSeq F (n + 2) = F ⊥ (dSeq F (n + 1)) := dSeq_succ (n + 1)
      _ ≤ F ⊥ (dSeq F n) := (F ⊥).mono (dSeq_succ_le n)
      _ = dSeq F (n + 1) := (dSeq_succ n).symm

theorem uSeq_lt_succ (hbt : b F ⊤ = ⊤) {n : ℕ} (h : uSeq F n ≠ ⊤) : uSeq F n < uSeq F (n + 1) :=
  lt_of_le_of_ne (uSeq_le_succ n) fun e => h (top_le_iff.1 (hbt ▸ b_le (by rw [← uSeq_succ, ← e])))

theorem dSeq_succ_lt (ha : a F ⊥ = ⊥) {n : ℕ} (h : dSeq F n ≠ ⊥) : dSeq F (n + 1) < dSeq F n :=
  lt_of_le_of_ne (dSeq_succ_le n) fun e => h (le_bot_iff.1 (ha ▸ le_a (by rw [← dSeq_succ, e])))

theorem chainTo_uSeq (hbt : b F ⊤ = ⊤) : ∀ n, uSeq F n ≠ ⊤ → chainTo (uSeq F n) n
  | 0, _ => trivial
  | n + 1, h => by
    have hn : uSeq F n ≠ ⊤ := fun e => h (top_le_iff.1 (e ▸ uSeq_le_succ n))
    exact ⟨uSeq F n, uSeq_lt_succ hbt hn, chainTo_uSeq hbt n hn⟩

theorem chainTo_dSeq (ha : a F ⊥ = ⊥) : ∀ n, dSeq F n ≠ ⊥ → ∀ k, chainTo (dSeq F n) k → chainTo (⊤ : α) (n + k)
  | 0, _, k, hk => by simpa [dSeq] using hk
  | n + 1, h, k, hk => by
    have hn : dSeq F n ≠ ⊥ := fun e => h (le_bot_iff.1 (e ▸ dSeq_succ_le n))
    have := chainTo_dSeq ha n hn (k + 1) ⟨_, dSeq_succ_lt ha hn, hk⟩
    rwa [show n + 1 + k = n + (k + 1) by omega]

theorem uSeq_eq_top {H : ℕ} (hn : NoChain α (H + 1)) (hbt : b F ⊤ = ⊤) : uSeq F H = ⊤ := by
  by_contra h
  exact hn ⊤ ⟨uSeq F H, lt_top_iff_ne_top.2 h, chainTo_uSeq hbt H h⟩

theorem dSeq_eq_bot {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥) : dSeq F H = ⊥ := by
  by_contra h
  exact hn ⊤ (chainTo_dSeq ha H h 1 ⟨⊥, bot_lt_iff_ne_bot.2 h, trivial⟩)

/-- **The last step of the ascending boundary orbit rises to the top.** -/
theorem exists_last_u {H : ℕ} (hn : NoChain α (H + 1)) (hbt : b F ⊤ = ⊤) (h0 : (⊥ : α) ≠ ⊤) :
    ∃ n, uSeq F n < ⊤ ∧ F (uSeq F n) ⊤ = ⊤ ∧ uSeq F n < a F (uSeq F n) := by
  classical
  have hex : ∃ n, uSeq F n = ⊤ := ⟨H, uSeq_eq_top hn hbt⟩
  obtain ⟨n, hn1⟩ : ∃ n, Nat.find hex = n + 1 := ⟨Nat.find hex - 1, by
    have : Nat.find hex ≠ 0 := fun e => h0 (by have := Nat.find_spec hex; rw [e] at this; exact this)
    omega⟩
  have hlt : uSeq F n ≠ ⊤ := Nat.find_min hex (by omega)
  have htop : F (uSeq F n) ⊤ = ⊤ := by rw [← uSeq_succ, ← hn1]; exact Nat.find_spec hex
  exact ⟨n, lt_top_iff_ne_top.2 hlt, htop, lt_of_lt_of_le (lt_top_iff_ne_top.2 hlt) (le_a htop.ge)⟩

/-- **The mixed grid.** `d (j+1) ≤ F (u i) (d j) ≤ u (i+1)`. -/
theorem grid_bounds (i j : ℕ) :
    dSeq F (j + 1) ≤ F (uSeq F i) (dSeq F j) ∧ F (uSeq F i) (dSeq F j) ≤ uSeq F (i + 1) := by
  rw [dSeq_succ, uSeq_succ]
  exact ⟨F.mono bot_le _, (F _).mono le_top⟩

/-- **Final-stage TightIC gives the top.** -/
theorem top_mem_of_lastIC {H : ℕ} (hn : NoChain α (H + 1)) {k : ℕ} (hk : k + 1 = H)
    (hic : ∃ m ∈ Rk F k, height H m = k ∧ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) : (⊤ : α) ∈ Rk F H := by
  obtain ⟨m, hm, hmk, y, hlt, hw⟩ := hic
  have hy := mem_succ_of_cell hm le_rfl hw
  have := height_strictMono hn hlt
  have hyt : y = ⊤ := eq_top_of_le_height hn (by omega)
  exact hk ▸ hyt ▸ hy

/-- **Final-stage TightIC gives Rise** (`b ⊤ = ⊤`: the cell is upper, `m < a m = ⊤`). -/
theorem rise_of_lastIC {H : ℕ} (hn : NoChain α (H + 1)) (hbt : b F ⊤ = ⊤) {k : ℕ} (hk : k + 1 = H)
    (hic : ∃ m ∈ Rk F k, height H m = k ∧ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) : Rise F H := by
  obtain ⟨m, hm, hmk, y, hlt, hw⟩ := hic
  have := height_strictMono hn hlt
  have hyt : y = ⊤ := eq_top_of_le_height hn (by omega)
  subst hyt
  rcases hw with hlo | hup
  · exact absurd (top_le_iff.1 (hbt ▸ b_le hlo)) (ne_top_of_lt hlt)
  · exact Or.inr (Or.inr (Or.inr ⟨m, k, hm, hmk.ge, lt_of_lt_of_le hlt (le_a hup)⟩))

/-- **`TightIC` at the last stage alone gives the top.** -/
theorem top_mem_of_tightIC_last {H : ℕ} (hn : NoChain α (H + 1)) (hic : TightIC F H) {k : ℕ} (hk : k + 1 = H) :
    (⊤ : α) ∈ Rk F H := by
  by_contra hnot
  have hbound : ∀ z ∈ Rk F k, height H z ≤ k := fun z hz => by
    by_contra hz'
    have hzt : z = ⊤ := eq_top_of_le_height hn (by omega)
    exact hnot (hk ▸ Rk_mono (Nat.le_succ k) (hzt ▸ hz))
  exact hnot (top_mem_of_lastIC hn hk (hic k (hk ▸ hnot) hbound))

end Mordor.OrbitHeight
