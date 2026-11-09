import Mordor.Stable
import Mordor.GapPotential

/-!
# The orbit-height invariant (round 26, §34.3z¹⁴⁰)

Down-set orbit `R₀ = ↓⊥`, `R_{k+1} = ↓(R_k ∪ a(R_k) ∪ b⁻¹(R_k))` (`Orbit.Rk`). Exact SAT on finite lattices
(`experiments/amalgamation/`) supports the uniform conjecture

  **(OH)** `⊤ ∉ R_k → ∃ z ∈ R_k, k ≤ height z`,

hence **(ORB)** `R_H = L` at edge-height `H`, for every monotone `F` — a width-independent orbit length. This file:

* `escape`: for `m ∈ R_k`, `m ≠ ⊤`, some `y ∈ R_{k+1}` has `y ≰ m` (the principal-cut lemma read along the orbit).
* `orbitHeight_one`: (OH) at `k = 1`, unconditionally (DCC).
* `eq_top_of_le_height`: at edge-height `≤ H`, an element of height `≥ H` is `⊤`.
* `top_mem_of_orbitHeight`, `cutMaps_of_orbitHeight`: (OH) at `k = H` gives `⊤ ∈ R_H`, and then the Cut Lemma for `F`
  (`cutMaps_of_top_mem`: any stage containing `⊤` does).
* `TightStep`, `RisingEscape` (the unresolved local step, exact SAT-supported), `orbitHeight_of_tightStep`,
  `tightStep_of_risingEscape`, `cutMaps_of_risingEscape`: rising escape at edge-height `H` ⇒ (OH) ⇒ Cut;
  `risingEscape_zero`: its `k = 0` case is a theorem.
* `TightUPC` (tight-stage upper principal cut), `mem_succ_of_cell`, `risingEscape_of_tightUPC`,
  `cutMaps_of_tightUPC`: the sharpest local form of the unresolved step, and its implication to Cut.
* `join_mem_of_top_mem` (**amalgamation**): once `⊤ ∈ R_K`, any `x, y` have `x ⊔ y ∈ R_K`; so (ORB) is the
  width-independent amalgamation bound `k(H, m, n) = H` of Programme C.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

theorem bot_mem_Rk (k : ℕ) : ⊥ ∈ Rk F k := Rk_mono (Nat.zero_le k) (show (⊥ : α) ∈ Set.Iic ⊥ from le_rfl)

/-- **Escape along the orbit.** -/
theorem escape [WellFoundedLT α] {k : ℕ} {m : α} (hm : m ∈ Rk F k) (ht : m ≠ ⊤) :
    ∃ y ∈ Rk F (k + 1), ¬ y ≤ m := by
  obtain ⟨x, hxm, y, hym, hw⟩ := cut_principal_down F m ht
  have hx : x ∈ Rk F k := Rk_down k hxm hm
  refine ⟨y, ?_, hym⟩
  rw [Rk_succ]
  rcases hw with h | h
  · exact ⟨y, le_rfl, Or.inr (Or.inr (Rk_down k (b_le h) hx))⟩
  · exact ⟨a F x, le_a h, Or.inr (Or.inl ⟨x, hx, rfl⟩)⟩

/-- **(OH) at `k = 1`.** Unless `⊤ ∈ R₁`, the first stage contains an element other than `⊥`. -/
theorem orbitHeight_one [WellFoundedLT α] (h : (⊤ : α) ∉ Rk F 1) : ∃ z ∈ Rk F 1, z ≠ ⊥ := by
  by_cases hb : (⊥ : α) = ⊤
  · exact absurd (hb ▸ bot_mem_Rk 1) h
  obtain ⟨y, hy, hyb⟩ := escape (F := F) (k := 0) (show (⊥ : α) ∈ Rk F 0 from le_rfl) hb
  exact ⟨y, hy, fun e => hyb (e ▸ le_rfl)⟩

/-- At edge-height `≤ H`, an element of height `≥ H` is the top. -/
theorem eq_top_of_le_height {H : ℕ} (hn : NoChain α (H + 1)) {z : α} (hz : H ≤ height H z) : z = ⊤ := by
  by_contra hne
  have hlt : z < ⊤ := lt_top_iff_ne_top.2 hne
  have hc : chainTo (⊤ : α) (H + 1) := ⟨z, hlt, chainTo_mono' (height H z) H z (chainTo_height z) hz⟩
  exact hn ⊤ hc

/-- The orbit-height invariant (a conjecture; see the module docstring). -/
def OrbitHeightInv (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k, (⊤ : α) ∉ Rk F k → ∃ z ∈ Rk F k, k ≤ height H z

theorem top_mem_of_orbitHeight {H : ℕ} (hn : NoChain α (H + 1)) (h : OrbitHeightInv F H) : (⊤ : α) ∈ Rk F H := by
  by_contra hnot
  obtain ⟨z, hz, hle⟩ := h H hnot
  exact hnot (eq_top_of_le_height hn hle ▸ hz)

/-- Any orbit stage containing `⊤` gives the Cut Lemma for `F`. -/
theorem cutMaps_of_top_mem {K : ℕ} (h : (⊤ : α) ∈ Rk F K) : CutMaps F :=
  cutMaps_iff_R.2 (Set.eq_univ_of_forall fun _ => R_closed.1 le_top (Rk_subset_R K h))

/-- **(OH) at edge-height `H` ⇒ the Cut Lemma for `F`.** -/
theorem cutMaps_of_orbitHeight {H : ℕ} (hn : NoChain α (H + 1)) (h : OrbitHeightInv F H) : CutMaps F :=
  cutMaps_of_top_mem (top_mem_of_orbitHeight hn h)

/-- The height step at tight stages: if every element of `R_k` has height `≤ k` and `⊤ ∉ R_{k+1}`, then `R_{k+1}`
reaches height `k + 1`. -/
def TightStep (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k, (⊤ : α) ∉ Rk F (k + 1) → (∀ z ∈ Rk F k, height H z ≤ k) → ∃ y ∈ Rk F (k + 1), k + 1 ≤ height H y

/-- **Rising escape** (the unresolved local step): at a tight stage some element of `R_k` of height `k` is strictly
exceeded by an element of `R_{k+1}`. -/
def RisingEscape (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k, (⊤ : α) ∉ Rk F (k + 1) → (∀ z ∈ Rk F k, height H z ≤ k) →
    ∃ m ∈ Rk F k, height H m = k ∧ ∃ y ∈ Rk F (k + 1), m < y

theorem orbitHeight_of_tightStep {H : ℕ} (h : TightStep F H) : OrbitHeightInv F H := by
  intro k ht
  cases k with
  | zero => exact ⟨⊥, show (⊥ : α) ∈ Set.Iic ⊥ from le_rfl, Nat.zero_le _⟩
  | succ k =>
    by_cases hall : ∀ w ∈ Rk F k, height H w ≤ k
    · exact h k ht hall
    · push_neg at hall
      obtain ⟨w, hw, hlt⟩ := hall
      exact ⟨w, Rk_mono (Nat.le_succ k) hw, hlt⟩

theorem tightStep_of_risingEscape {H : ℕ} (hn : NoChain α (H + 1)) (h : RisingEscape F H) : TightStep F H := by
  intro k ht hall
  obtain ⟨m, -, hmk, y, hy, hmy⟩ := h k ht hall
  exact ⟨y, hy, hmk ▸ Nat.succ_le_of_lt (height_strictMono hn hmy)⟩

/-- **Rising escape ⇒ the Cut Lemma for `F`**, at edge-height `≤ H`. -/
theorem cutMaps_of_risingEscape {H : ℕ} (hn : NoChain α (H + 1)) (h : RisingEscape F H) : CutMaps F :=
  cutMaps_of_orbitHeight hn (orbitHeight_of_tightStep (tightStep_of_risingEscape hn h))

/-- **Tight-stage upper principal cut** (the sharpest form of the unresolved step): at a tight stage some element
`m ∈ R_k` of height `k` carries a witness cell `(x, y)` with `x ≤ m < y`. For an arbitrary `m` this is false
(§34.3z¹⁴⁰, a 4-element instance); at tight stages it holds on every finite lattice checked. -/
def TightUPC (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k, (⊤ : α) ∉ Rk F (k + 1) → (∀ z ∈ Rk F k, height H z ≤ k) →
    ∃ m ∈ Rk F k, height H m = k ∧ ∃ x, x ≤ m ∧ ∃ y, m < y ∧ (F x y ≤ x ∨ y ≤ F x y)

/-- A witness cell `(x, y)` with `x ≤ m ∈ R_k` puts `y` into `R_{k+1}`. -/
theorem mem_succ_of_cell {k : ℕ} {m x y : α} (hm : m ∈ Rk F k) (hxm : x ≤ m) (hw : F x y ≤ x ∨ y ≤ F x y) :
    y ∈ Rk F (k + 1) := by
  have hx : x ∈ Rk F k := Rk_down k hxm hm
  rw [Rk_succ]
  rcases hw with h | h
  · exact ⟨y, le_rfl, Or.inr (Or.inr (Rk_down k (b_le h) hx))⟩
  · exact ⟨a F x, le_a h, Or.inr (Or.inl ⟨x, hx, rfl⟩)⟩

theorem risingEscape_of_tightUPC {H : ℕ} (h : TightUPC F H) : RisingEscape F H := by
  intro k ht hall
  obtain ⟨m, hm, hmk, x, hxm, y, hmy, hw⟩ := h k ht hall
  exact ⟨m, hm, hmk, y, mem_succ_of_cell hm hxm hw, hmy⟩

/-- **Tight-stage upper principal cut ⇒ the Cut Lemma for `F`**, at edge-height `≤ H`. -/
theorem cutMaps_of_tightUPC {H : ℕ} (hn : NoChain α (H + 1)) (h : TightUPC F H) : CutMaps F :=
  cutMaps_of_risingEscape hn (risingEscape_of_tightUPC h)

/-- Rising escape at `k = 0` holds unconditionally (DCC): it is `orbitHeight_one`. -/
theorem risingEscape_zero [WellFoundedLT α] {H : ℕ} (ht : (⊤ : α) ∉ Rk F 1) :
    ∃ m ∈ Rk F 0, height H m = 0 ∧ ∃ y ∈ Rk F 1, m < y := by
  obtain ⟨y, hy, hyb⟩ := orbitHeight_one ht
  refine ⟨⊥, show (⊥ : α) ∈ Set.Iic ⊥ from le_rfl, ?_, y, hy, bot_lt_iff_ne_bot.2 hyb⟩
  by_contra hne
  obtain ⟨z, hz, -⟩ : chainTo (⊥ : α) 1 := by
    have h1 : 1 ≤ height H (⊥ : α) := Nat.one_le_iff_ne_zero.2 hne
    exact chainTo_mono' _ 1 ⊥ (chainTo_height ⊥) h1
  exact not_lt_bot hz

/-- **Amalgamation from the orbit length.** -/
theorem join_mem_of_top_mem {K : ℕ} (h : (⊤ : α) ∈ Rk F K) (x y : α) : x ⊔ y ∈ Rk F K :=
  Rk_down K le_top h

end Mordor.OrbitHeight
