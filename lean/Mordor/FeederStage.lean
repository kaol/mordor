import Mordor.HeightInduction

/-!
# Stage-local feeder identity and the meet identity of singleton lower transfer (round 26, §34.3z¹⁶²)

ChatGPT brief "Structural proof strategies without escalating DRAT" (HEAD fa913e6), Priority A.

* `diagGood_of_ohBelow`: a diagonal pre-fixed point `c` of height `< k` lies in `R_{h(c)}`, given `OHAt` only at
  heights `< k` (the interval `[⊥, c]` has edge-height `≤ h(c)`); no condition on the global edge-height bound `H`.
* `feeder_identity_stage`: **feeder identity at stage `k`** (`h(m') ≤ k`, `m' ≤ t`, `t ∉ R_k`, `F m' t ≤ m'`
  ⇒ `b t = m'`), given `OHAt` below `k`. `feeder_identity_le_four`: hence **unconditionally for `k ≤ 4`**, at every
  edge-height (ordinary proofs only: `OHAt ≤ 3` from `HeightInduction`). This settles the `k = 2` case asked about.
* `meet_dichotomy`: in the singleton lower configuration (`m' ⋖ m` by heights, `F m' m ≤ m'`, `m ∉ R_k`), given
  `OHAt` below `k`: for every `y ≥ m`, either `m ≤ F m y` or `F m y ⊓ m = m'`.
  - `single_lower_meet` (`single_lower_meet_le_four`: unconditional for `k ≤ 4`): in particular the incomparable output `w = F(m, y*)` of `colOrb_dichotomy` has
    `w ⊓ m = m'`; and `diag_meet`: `F m m ⊓ m = m'` unless `m` is diagonal.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} [CompleteLattice α] {F : α →o α →o α}

/-- **Diagonal goodness from `OHAt` below the element's own height.** -/
theorem diagGood_of_ohBelow {k H : ℕ} (IH : ∀ H' < k, OHAt.{u} H') (hn : NoChain α (H + 1)) {c : α}
    (hc : F c c ≤ c) (hck : height H c < k) : c ∈ Rk F (height H c) := by
  haveI : Fact ((⊥ : α) ≤ c) := ⟨bot_le⟩
  exact diag_pre_mem hc (IH _ hck _ _ (noChain_Icc_bot hn c))

/-- **Feeder identity at stage `k`**, from `OHAt` below `k`. -/
theorem feeder_identity_stage {k H : ℕ} (IH : ∀ H' < k, OHAt.{u} H') (hn : NoChain α (H + 1)) {m' t : α}
    (hm'k : height H m' ≤ k) (hmt : m' ≤ t) (ht : t ∉ Rk F k) (hlo : F m' t ≤ m') : b F t = m' := by
  rcases eq_or_lt_of_le (b_le hlo) with e | hlt
  · exact e
  exfalso
  have hct : b F t ≤ t := hlt.le.trans hmt
  have hdiag : F (b F t) (b F t) ≤ b F t := ((F (b F t)).mono hct).trans (col_b t).le
  have h1 := height_strictMono hn hlt
  have hmem := diagGood_of_ohBelow IH hn hdiag (by omega)
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact ht (mem_succ_of_b (Rk_mono (by omega) hmem))

/-- `OHAt` below 4, by ordinary proofs. -/
theorem ohAt_lt_four : ∀ H' < 4, OHAt.{u} H' := fun _ _ => ohAt_of_riseAt fun _ h => riseAt_le_three (by omega)

/-- **Feeder identity at stages `k ≤ 4`, unconditionally** (any edge-height). -/
theorem feeder_identity_le_four {k H : ℕ} (hk : k ≤ 4) (hn : NoChain α (H + 1)) {m' t : α}
    (hm'k : height H m' ≤ k) (hmt : m' ≤ t) (ht : t ∉ Rk F k) (hlo : F m' t ≤ m') : b F t = m' :=
  feeder_identity_stage (fun H' h => ohAt_lt_four H' (by omega)) hn hm'k hmt ht hlo

/-- A height gap of one is a cover. -/
theorem eq_of_height_between {H : ℕ} (hn : NoChain α (H + 1)) {k : ℕ} {m' m z : α}
    (hm'k : height H m' = k) (hmk : height H m = k + 1) (h1 : m' ≤ z) (h2 : z ≤ m) : z = m' ∨ z = m := by
  rcases eq_or_lt_of_le h1 with e | l1
  · exact Or.inl e.symm
  rcases eq_or_lt_of_le h2 with e | l2
  · exact Or.inr e
  have := height_strictMono hn l1; have := height_strictMono hn l2; omega

/-- **The meet dichotomy of a singleton lower feeder.** -/
theorem meet_dichotomy {k H : ℕ} (IH : ∀ H' < k, OHAt.{u} H') (hn : NoChain α (H + 1)) {m' m : α}
    (hm'k : height H m' = k) (hmk : height H m = k + 1) (hlt : m' < m) (hnew : m ∉ Rk F k)
    (hlo : F m' m ≤ m') {y : α} (hmy : m ≤ y) : m ≤ F m y ∨ F m y ⊓ m = m' := by
  have hb : b F m = m' := feeder_identity_stage IH hn hm'k.le hlt.le hnew hlo
  have hfloor : m' ≤ F m y := hb ▸ floor_le_row (hb ▸ hlt.le) hmy
  rcases eq_of_height_between hn hm'k hmk (le_inf hfloor hlt.le) inf_le_right with e | e
  · exact Or.inr e
  · exact Or.inl (e.symm.le.trans inf_le_left)

/-- **The incomparable column output meets `m` in the feeder** (`w ⊓ m = m'`). -/
theorem single_lower_meet {k H : ℕ} (IH : ∀ H' < k, OHAt.{u} H') (hn : NoChain α (H + 1)) {m' m : α}
    (hm'k : height H m' = k) (hmk : height H m = k + 1) (hlt : m' < m) (hnew : m ∉ Rk F k)
    (hlo : F m' m ≤ m') {y : α} (hmy : m ≤ y) (hnot : ¬ m ≤ F m y) : F m y ⊓ m = m' :=
  (meet_dichotomy IH hn hm'k hmk hlt hnew hlo hmy).resolve_left hnot

/-- **The diagonal meets `m` in the feeder unless `m` is diagonal.** -/
theorem diag_meet {k H : ℕ} (IH : ∀ H' < k, OHAt.{u} H') (hn : NoChain α (H + 1)) {m' m : α}
    (hm'k : height H m' = k) (hmk : height H m = k + 1) (hlt : m' < m) (hnew : m ∉ Rk F k)
    (hlo : F m' m ≤ m') : m ≤ F m m ∨ F m m ⊓ m = m' :=
  meet_dichotomy IH hn hm'k hmk hlt hnew hlo le_rfl

/-- **The meet identity at stages `k ≤ 4`, unconditionally.** -/
theorem single_lower_meet_le_four {k H : ℕ} (hk : k ≤ 4) (hn : NoChain α (H + 1)) {m' m : α}
    (hm'k : height H m' = k) (hmk : height H m = k + 1) (hlt : m' < m) (hnew : m ∉ Rk F k)
    (hlo : F m' m ≤ m') {y : α} (hmy : m ≤ y) (hnot : ¬ m ≤ F m y) : F m y ⊓ m = m' :=
  single_lower_meet (fun H' h => ohAt_lt_four H' (by omega)) hn hm'k hmk hlt hnew hlo hmy hnot

end Mordor.OrbitHeight
