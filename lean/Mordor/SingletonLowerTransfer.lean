import Mordor.TightTransfer

/-!
# Singleton lower transfer: the exact statement and its reductions (round 26, §34.3z¹⁵⁶)

ChatGPT brief "Prove singleton lower transfer" (HEAD a50f91e).

* `SingletonLower F H` — **conjecture** (the brief's Programme A, as a Prop): stages `k`, `k + 1` index-tight,
  `⊤ ∉ R_{k+2}`, `m` the unique element of height `k + 1` in `R_{k+1}`, `m ∉ R_k`, and a lower feeder
  `m' ∈ R_k` of height `k` with `m' < m`, `F m' m ≤ m'`; then `m` has an interval cell.
* `singleton_tightIC_of_lower`: with `single_top_reduction`, `SingletonLower` and a TightIC witness at stage `k`
  give the interval cell at the singleton new top of stage `k + 1`.
* `bentry_iff` (Programme B): at an index-tight stage `k + 1` with `m` of height `k + 1`,
  `BEntry_k(m) := ∃ y, m ≤ y ∧ b y ∈ R_k` is equivalent to `b m ∈ R_k`: a column `y ≥ m` with `b y ∈ R_k`
  lies in `R_{k+1}`, so the height bound forces `y = m`. (The brief's warning against this strengthening is not
  needed.)
* `floor_le_row`: `b m ≤ m` gives `b m ≤ F m y` for every `y ≥ m` (`F (b m) m = b m`). In particular the
  incomparable output `w = F(m, y*)` of `colOrb_dichotomy` lies above `b m`; with `b m = m'` (exact evidence,
  §34.3z¹⁵⁶) and `m' ⋖ m` this pins `w ⊓ m = m'`.
* **Feeder identity** (conjectured in general, exact evidence §34.3z¹⁵⁶: a lower cell `(m', t)` into a new target
  has `b t = m'`). `feeder_identity_of_below`: it holds whenever everything strictly below `m'` already lies in the
  previous stage; `feeder_identity_one`: hence at `k = 1` (feeder an atom).
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

/-- **Singleton lower transfer** (conjecture). -/
def SingletonLower (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k, (⊤ : α) ∉ Rk F (k + 2) → (∀ z ∈ Rk F k, height H z ≤ k) → (∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) →
    ∀ m, (∀ z ∈ Rk F (k + 1), height H z = k + 1 → z = m) → m ∈ Rk F (k + 1) → height H m = k + 1 →
      m ∉ Rk F k → ∀ m' ∈ Rk F k, height H m' = k → m' < m → F m' m ≤ m' →
        ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)

/-- **Singleton TightIC from singleton lower transfer.** -/
theorem singleton_tightIC_of_lower [WellFoundedLT α] {H : ℕ} (hn : NoChain α (H + 1))
    (hsl : SingletonLower F H) {k : ℕ} (htop : (⊤ : α) ∉ Rk F (k + 2))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m : α}
    (huniq : ∀ z ∈ Rk F (k + 1), height H z = k + 1 → z = m) (hm : m ∈ Rk F (k + 1))
    (hmk : height H m = k + 1) (hnew : m ∉ Rk F k)
    (hprev : ∃ m' ∈ Rk F k, height H m' = k ∧ ∃ y, m' < y ∧ (F m' y ≤ m' ∨ y ≤ F m' y)) :
    ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y) := by
  rcases single_top_reduction hn htop hall huniq hprev with h | ⟨m', hm', hm'k, hlt, hlo⟩
  · exact h
  · exact hsl k htop (single_prev_bound hall huniq hnew) hall m huniq hm hmk hnew m' hm' hm'k hlt hlo

/-- `b y ∈ R_k` puts `y` into `R_{k+1}`. -/
theorem mem_succ_of_b {k : ℕ} {y : α} (h : b F y ∈ Rk F k) : y ∈ Rk F (k + 1) :=
  mem_succ_of_cell h le_rfl (Or.inl (col_b y).le)

/-- **BEntry is b-membership of the top itself.** -/
theorem bentry_iff {H : ℕ} (hn : NoChain α (H + 1)) {k : ℕ} (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m : α} (hmk : height H m = k + 1) : (∃ y, m ≤ y ∧ b F y ∈ Rk F k) ↔ b F m ∈ Rk F k := by
  refine ⟨fun ⟨y, hmy, hy⟩ => ?_, fun h => ⟨m, le_rfl, h⟩⟩
  rcases eq_or_lt_of_le hmy with e | hlt
  · exact e ▸ hy
  · have := height_strictMono hn hlt
    have := hall y (mem_succ_of_b hy)
    omega

/-- **The floor of the row.** -/
theorem floor_le_row {m y : α} (hbm : b F m ≤ m) (hmy : m ≤ y) : b F m ≤ F m y :=
  calc b F m = F (b F m) m := (col_b m).symm
    _ ≤ F m y := (F.mono hbm m).trans ((F m).mono hmy)

/-- **Feeder identity, the easy case.** -/
theorem feeder_identity_of_below {j : ℕ} {m' t : α} (hbelow : ∀ z, z < m' → z ∈ Rk F j)
    (ht : t ∉ Rk F (j + 1)) (hlo : F m' t ≤ m') : b F t = m' := by
  rcases eq_or_lt_of_le (b_le hlo) with e | hlt
  · exact e
  · exact absurd (mem_succ_of_b (hbelow _ hlt)) ht

/-- **Feeder identity at `k = 1`.** -/
theorem feeder_identity_one {H : ℕ} (hH : 1 ≤ H) (hn : NoChain α (H + 1)) {m' t : α}
    (hm'1 : height H m' = 1) (ht : t ∉ Rk F 1) (hlo : F m' t ≤ m') : b F t = m' := by
  refine feeder_identity_of_below (j := 0) (fun z hz => ?_) ht hlo
  have hz0 : z = ⊥ := by
    by_contra hw
    have := le_height hH ⟨⊥, bot_lt_iff_ne_bot.2 hw, trivial⟩
    have := height_strictMono hn hz
    omega
  exact hz0 ▸ (show (⊥ : α) ∈ Rk F 0 from le_rfl)

end Mordor.OrbitHeight
