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

/-- **No strictly higher column has its b-value below `m`** (§34.3z¹⁶³). In the singleton lower configuration with
no interval cell at `m`: for `y > m`, `b y ∈ [m', m]` would be `m'` (then `y ∈ R_{k+1}` above the height bound)
or `m` (then `F m y = m`, a lower cell). Only `m' ≤ b m` is needed (feeder identity gives equality). -/
theorem strict_upper_b_not_le {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m' m : α} (hm' : m' ∈ Rk F k) (hm'k : height H m' = k) (hmk : height H m = k + 1) (hb : m' ≤ b F m)
    (hnocell : ¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) : ∀ y, m < y → ¬ b F y ≤ m := by
  intro y hy hle
  have h1 : m' ≤ b F y := hb.trans ((b F).mono hy.le)
  rcases eq_of_height_between hn hm'k hmk h1 hle with e | e
  · have := hall y (mem_succ_of_b (e ▸ hm'))
    have := height_strictMono hn hy
    omega
  · exact hnocell ⟨y, hy, Or.inl (by rw [← e]; exact (col_b y).le)⟩

/-! ### Crossing facts and the side interval (§34.3z¹⁶³) -/

/-- **The b-value dichotomy.** For `y ≥ m` with `m' ≤ b m` and `m' ⋖ m` (heights): `m ≤ b y` or `b y ⊓ m = m'`. -/
theorem b_dichotomy {k H : ℕ} (hn : NoChain α (H + 1)) {m' m : α} (hm'k : height H m' = k)
    (hmk : height H m = k + 1) (hm'm : m' ≤ m) (hb : m' ≤ b F m) {y : α} (hmy : m ≤ y) :
    m ≤ b F y ∨ b F y ⊓ m = m' := by
  rcases eq_of_height_between hn hm'k hmk (le_inf (hb.trans ((b F).mono hmy)) hm'm) inf_le_right with e | e
  · exact Or.inr e
  · exact Or.inl (e.symm.le.trans inf_le_left)

/-- First crossing case: a column whose b-value lies above `m` bounds the next column-orbit value. -/
theorem col_step_le_b {m c : α} (h : m ≤ b F c) : m ⊔ F m c ≤ b F c :=
  sup_le h ((F.mono h c).trans (col_b c).le)

/-- Second crossing case: a b-value below its own column is diagonal pre-fixed. -/
theorem b_diag_pre {c : α} (h : b F c ≤ c) : F (b F c) (b F c) ≤ b F c :=
  ((F (b F c)).mono h).trans (col_b c).le

/-- **Uniqueness above the feeder.** At a tight stage `k + 1` with the unique top `m`, every element of `R_{k+1}`
strictly above a height-`k` element `m'` is `m`. -/
theorem above_feeder_eq {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m' m : α} (huniq : ∀ z ∈ Rk F (k + 1), height H z = k + 1 → z = m) (hm'k : height H m' = k)
    {z : α} (hz : z ∈ Rk F (k + 1)) (hlt : m' < z) : z = m := by
  have := height_strictMono hn hlt; have := hall z hz
  exact huniq z hz (by omega)

/-- **The feeder has no cell sideways.** Every `z > m'` other than `m` is not a cell column of the row `m'`. -/
theorem feeder_row_escape {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m' m : α} (huniq : ∀ z ∈ Rk F (k + 1), height H z = k + 1 → z = m) (hm' : m' ∈ Rk F k)
    (hm'k : height H m' = k) {z : α} (hlt : m' < z) (hzm : z ≠ m) : ¬ F m' z ≤ m' ∧ ¬ z ≤ F m' z :=
  ⟨fun h => hzm (above_feeder_eq hn hall huniq hm'k (mem_succ_of_cell hm' le_rfl (Or.inl h)) hlt),
   fun h => hzm (above_feeder_eq hn hall huniq hm'k (mem_succ_of_cell hm' le_rfl (Or.inr h)) hlt)⟩

/-- **The side interval is invariant under the feeder's column map.** If `m' ≤ w`, `m ≰ w` and `F m' w ≤ w`, then
`z ↦ m' ⊔ F m' z` maps `(m', w]` into itself, and (by `feeder_row_escape`) `m'` has no cell into `(m', w]`: the
incomparable configuration at `m` reproduces at the feeder, one height lower. -/
theorem side_interval_maps {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m' m : α} (huniq : ∀ z ∈ Rk F (k + 1), height H z = k + 1 → z = m) (hm' : m' ∈ Rk F k)
    (hm'k : height H m' = k) {w : α} (hm'w : m' ≤ w) (hmw : ¬ m ≤ w) (hFw : F m' w ≤ w)
    {z : α} (hlt : m' < z) (hzw : z ≤ w) : m' < m' ⊔ F m' z ∧ m' ⊔ F m' z ≤ w := by
  have hzm : z ≠ m := fun e => hmw (e ▸ hzw)
  refine ⟨lt_of_le_of_ne le_sup_left fun e => ?_, sup_le hm'w (((F m').mono hzw).trans hFw)⟩
  exact (feeder_row_escape hn hall huniq hm' hm'k hlt hzm).1 (le_sup_right.trans e.symm.le)

/-- The side-interval hypothesis `F m' w ≤ w` is automatic for the column-orbit output `w = F m y` of a fixed point
`y = m ⊔ F m y` (monotonicity in both arguments). -/
theorem feeder_le_side {m' m y : α} (hm'm : m' ≤ m) (hy : m ⊔ F m y = y) : F m' (F m y) ≤ F m y :=
  ((F.mono hm'm) (F m y)).trans ((F m).mono (le_sup_right.trans hy.le))

end Mordor.OrbitHeight
