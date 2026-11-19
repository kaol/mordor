import Mordor.ParentAncestry

/-!
# Late parents: up-closure of A-parents, the A-normal form, isolation (round 26, §34.3z¹⁶⁷)

ChatGPT brief "Eliminate late-parent ancestry" (HEAD 19c5e82).

* `a_parent_up`: for a height-`(k+1)` column `z` of a tight `R_{k+1}`, the A-parents of `z` in `R_k` form an
  **up-set of `R_k`** (`z ≤ F x z`, `x ≤ y ∈ R_k` ⟹ `F y z = z`). The B-parents do not (finite counterexample,
  `late_probe.py`).
* `topParent_of_a_parent_le_top` (a special case of the brief's `LateBJumpCompensation`): a second top with an
  A-parent (late or not) below an element of `T_k` has an on-time A-parent; TopParent holds.
* `not_topParent_a_isolated`: if TopParent fails, every A-parent of every second top is **isolated from `T_k`**
  (nothing of height `k` in `R_k` lies above it).
* `a_normal`: every `q ∈ R_s` lies below `a^[i] q'` with `q' ∈ R_t`, `t + i ≤ s`, and `q'` *terminal*: `t = 0`, or
  `q'` is new at stage `t`, B-entered and not A-entered.
* `exists_max_height`, **`max_a_parent_normal`** (the brief's Deliverable A1): an A-parent of maximum height among the
  A-parents of `z` *equals* its normal form `a^[i] q'` with terminal `q'`, and keeps `F x z = z`.
* `late_not_pre`: with `OHAt` below `k + 1`, a late element (`x ∉ R_k`, `h(x) ≤ k`) is not diagonal pre-fixed
  (`diagGood_of_ohBelow`).
* B-side (§34.3z¹⁶⁸): `b_parent_le_ontime` (a B-parent below its top is on time), `late_b_parent_not_le` (late
  B-parents are incomparable with their top), `topParent_of_b_le`, `topParent_of_a_top`, `not_topParent_a_low`
  (a TopParent failure forces `a y = m` or `h(a y) ≤ k` for every `y ∈ T_k`), `feeder_a_ne` (`a m' ≠ m`),
  `CanonicalTopParent` (conjectured: no counterexample) and `topParent_of_canonical`.
* §34.3z¹⁶⁹: `rowCollapse_iff_canonical` (the brief's `rowCollapse_to_BTop` is CanonicalTopParent), `row_cell_of_above`,
  `canonical_of_row_descent`, **`canonical_of_feeder_descent`** (CanonicalTopParent when the feeder row stays above
  `m'` on its pre-fixed columns in `(m', w]`), `DescentWitness` (conjectured: no counterexample),
  `canonical_of_descentWitness`, `topParent_of_descentWitness`.
* §34.3z¹⁷⁰ (drop geometry): `drop_lt`, `drop_row_pre`, `drop_meet`, `canonical_of_drop_le`,
  `drop_incomparable_or_canonical` (a drop is mechanism B unless its output is incomparable with the feeder).
* §34.3z¹⁷¹ (raw feeder orbit): `feeder_a_le_y`, `feeder_a_le_w` (`a m' ≤ w`), `a_le_iter`, `exists_iter_fix`,
  `rawOrbit_terminal` (the raw feeder orbit from `w` or `r` ends at `a m'`), `a_le_drop` (`a m' ≤ r`),
  `canonical_of_feeder_lt_a`, **`feeder_descent_leaves`**.
* §34.3z¹⁷²: `UpCell` (a top row with a cell above itself away from `m`), `upCell_of_descentWitness`,
  `canonical_of_upCell`, `secondEntry_of_canonical`, **`singletonLower_of_upCell`** (UpCell in every no-cell
  configuration ⟹ `SingletonLower`).
* §34.3z¹⁷³: `noUpCell_forces_incomparable_drop`, `topRow_normalForm`, `topRow_terminal_B`, `feeder_b_lt`.
* §34.3z¹⁷⁴: `covBy_of_height`, `height_bot_eq_zero`, `strictBTop_has_cover_source(_one)`, **`cross_shadow`**,
  `source_meet`, `source_meet_lt`, `feeder_new`, `feeder_cover_source`.
* §34.3z¹⁷⁵: `shadow_trichotomy`, **`sibling_of_shadow`** (same-source siblings), `source_new`, `upper_branch_eq_a`,
  **`sibling_join`** (`F p (x ⊔ c) = c`), `sibling_join_lower`.
* §34.3z¹⁷⁶: `source_row_const` (`F p ≡ c` on `(c, u]`), **`siblingShadow_upCell`** (SiblingShadowCell unless the
  row `c` is incomparable with every column of `(c, u]`).
* §34.3z¹⁷⁹: `DropNode`, `ChainExit`, `dropNode_step`, **`dropChain_exit`** (the shadow chain down the B-sources ends in
  an exit; no orbit hypotheses), `iter_source_new`, `lowerExit_mem`.
* §34.3z¹⁸⁰: `dropNode_source_lt`, `chainExit_not_D` (the D-exit is impossible), `CellState`, **`cellState_cell`**
  (two-dimensional descent yields a genuine cell), **`dropNode_cell`**, `feeder_cell_dichotomy`,
  `depthOne_lowerCell_sibling`.
* §34.3z¹⁸¹: **`depthOne_shadow_upCell`** (the depth-one lift, comparable case).
* §34.3z¹⁸²: `row_cell_of_above_shadow` (descent with shadow tracking), **`climb_step`**, **`climb_next_config`** (a
  sibling-shadow configuration whose cell is a new lower-cell shadow gives a sibling-shadow configuration one
  stage higher).
* §34.3z¹⁸³: `TopFibre`, **`upCell_of_topFibre`**, **`singletonLower_of_topFibre`**.
* §34.3z¹⁸⁴: `shadowFibre`, `FibreTopAt`, **`fibreTopAt_iff_join`** (a stable fibre join reduces FibreTop to the single
  interval `(c, ⋁S]`), `topFibre_iff`.
* §34.3z¹⁸⁵: `SibConfig`, `SeedEdge`, `SeedReach` (the descent-seeded configuration graph), `seedReach_stage`,
  **`seedEdge_of_climb`**, `seedEdge_anchor`, `aRoot_eq_a`, `upCell_of_sibConfig_top`.
* §34.3z¹⁸⁶: `AEdge`, `aEdge_eq_a`, `aEdge_of_upper`, `MixedReach`, `mixedReach_stage`, `upCell_of_mixedTop`,
  `upCell_of_sibConfig_src`, `upCell_of_aEdge`, `TopEdge`, `TopReach`, `topReach_of_mixedReach`, `upCell_of_topEdge`,
  `SeededStepB`, `TopGoal`, `topReach_stage`, `topReach_top`, `upCell_of_topGoal`.
* §34.3z¹⁸⁷: `UpAt`, `Good`, `topReach_cons`, `topGoal_of_good`, `good_of_topReach`, `good_iff_topGoal`, `good_le`,
  `NonemptyForkGoodChild`, `topGoal_of_fork`, `good_term_of_topEdge`, `good_child_of_good`,
  `nonemptyForkGoodChild_iff`, `ForkGoodChildAll`, `nonemptyForkGoodChild_of_all`.
* §34.3z¹⁸⁸: `le_a_of_upper`, `aEdge_le_a`, `upAt_of_a`, `good_aChild_term`, `AGoodFrom`, `BOnlyGoodChild`,
  `nonemptyForkGoodChild_of_split`, `topGoal_of_split`, `topEdge_lt`, `topReach_ge`, `ConeForkGood`,
  `nonemptyForkGoodChild_of_cone`, `not_tight_of_early`.
* §34.3z¹⁸⁹: `shadowFibre_downClosed`, `fibreTopAt_iff_mem`, `shadowFibre_eq_Ioc`, `StableFibreTop`, `JumpFibreTop`.
* §34.3z¹⁹⁰: `htf_concl_iff`, `fibre_bad_of_not_upCell`, `badFibre_row`, `no_cell_above`, `rowShadow_source`, `MinUpCell`,
  `singletonLower_of_minUpCell`, **`upCell_zero`** (MinUpCell at `k = 0`).
* §34.3z¹⁹¹: `MinDescentWitness`, `minUpCell_of_minDescentWitness`, `diag_post_of_aEntry`, `above_of_diag_post`.
* §34.3z¹⁹²: **`saturated_shadow`**, `SatSourceBelow` (refuted), `initialPair_of_le`.
* §34.3z¹⁹³: **`joinProbe`**, `joinProbe_split`, `sat_iter_ge`, `joinProbe_A1_ge`, `eq_meet_of_row_below`.
* §34.3z¹⁹⁴: **`noUpCell_aResponse`**, `stationary_b_le`, `entry_of_new`, **`upCell_of_diagPost_pair`**, **`noUpCell_rowTypes`**.
* §34.3z¹⁹⁵: `pureA_le_succ`, `pureA_mono`, `noUpCell_ascending_old`, **`noUpCell_pureA_jump`**, `old_diagPost_eq_top`,
  **`pureA_height_le`**, **`noUpCell_not_below_pureA`**, **`noUpCell_nonAscending_terminal`**.
* §34.3z¹⁹⁶: `terminalSource_new`, **`terminalBAncestry`**, **`ascending_height_le`**, `row_below_ascending_eq`, `a_ascending`,
  **`nonAscending_chain`**, `noUpCell_nonAscending_terminal'`.
* §34.3z¹⁹⁷: `i0_dichotomy`, `bSource_of_new_nonAscending`, **`noUpCell_i0_cover`**, `i0_A1_cover`, `noUpCell_firstA_parent`,
  `noUpCell_firstA_parent_height`.
* §34.3z¹⁹⁸: `source_row_or`, `exceptional_column`, **`upCell_of_rowConst`**, **`a1_upCell_or_exceptional`**.
* §34.3z¹⁹⁹: `exceptional_same_source`, **`exception_join_dichotomy`**, `A1CleanFibre`, **`upCell_of_a1CleanFibre`**, `A1Cert`,
  `a1Cert_of_cleanFibre`, **`upCell_of_a1Cert`**, `A1RowTypeCert`, **`noUpCell_a1_fibre_empty`**.
* §34.3z²⁰⁰: `A1BadForbidden`, **`a1RowTypeCert_iff`**, `a1_rowValue_ge`, `nonAscending_gfp_incomparable`.
* §34.3z²⁰¹: `A1SelfUpCell`, **`noUpCell_a1_fibre_empty'`**.
* §34.3z²⁰²: `DominantA1` (refuted).
* §34.3z²⁰³: `secondEntry_of_upCell`, `upCell_of_otherAscending`, **`secondEntry_of_A1BadForbidden`**, `SecondEntryOfGenuineA1`,
  `secondEntryOfGenuineA1_of_badForbidden`, `MinSecondEntry`, `minSecondEntry_of_minUpCell`,
  **`singletonLower_of_minSecondEntry`**, `secondEntryOfGenuineA1_of_min`, `minSecondEntry_zero`.
* §34.3z²⁰⁴ (uniqueness consequences, k = 1 anatomy): **`tight_of_not_secondEntry`**, `cell_eq_of_not_secondEntry`,
  `noIC_of_not_secondEntry`, `bot_row_le_side`, `a_bot_of_not_secondEntry_one`, **`exists_cellFree_off_one`**.
* §34.3z²⁰⁵ (k = 1 bottom-row descent): **`row_cell_of_bot_le_one`**, `mem_one_of_bot_value`, `upCell_of_bot_side_one`,
  **`upCell_of_bot_side_le_one`**, `bot_side_residue_one`, `LTPair`, **`secondEntry_of_LTPair`**, `MinLT`, **`secondEntry_one_of_minLT`**.
* §34.3z²⁰⁶ (the row of the bottom-row descent): `bot_iter_le`, **`exists_bot_descent_atom`**, `RowLT2`,
  **`secondEntry_one_of_rowLT2`**.
* §34.3z²⁰⁷ (bare two-stage form): `TightRowCell2`, **`secondEntry_one_of_tightRowCell2`**.
* §34.3z²⁰⁸ (split): `IC3`, `DeepFree`, **`secondEntry_one_of_IC3_deepFree`**.
* §34.3z²⁰⁹ (IC-lemma structure): `inf_eq_bot_of_height_one`, `eq_of_le_height_one`, `icLemma_meets`,
  **`no_preColumn_of_cellFree`**, **`ic_of_preColumn`**, `ic_of_preColumn_le`.
* §34.3z²¹⁰ (the KL2 reduction): **`no_kl2Column`**, `KL2E`, **`ic_of_KL2E`**.
* §34.3z²¹¹ (the gap configuration): `exists_iter_fix_mono`, **`exists_gap`**.
* §34.3z²¹² (localization at g): `no_kl3Column`.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} [CompleteLattice α] {F : α →o α →o α}

/-- **A-parents form an up-set of `R_k`.** -/
theorem a_parent_up {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {x y z : α} (hy : y ∈ Rk F k) (hxy : x ≤ y) (hz : height H z = k + 1) (hA : z ≤ F x z) : F y z = z := by
  have hle : z ≤ a F y := le_a (hA.trans ((F.mono hxy) z))
  have e : z = a F y := by
    by_contra hne
    have := height_strictMono hn (lt_of_le_of_ne hle hne)
    have := hall _ (mem_succ_of_a hy le_rfl); omega
  rw [e]; exact row_a y

/-- **Compensation for a dominated A-parent.** -/
theorem topParent_of_a_parent_le_top {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m x y z : α} (hzm : z ≠ m) (hz : height H z = k + 1)
    (hzR : z ∈ Rk F (k + 1)) (hy : y ∈ Rk F k) (hyk : height H y = k) (hxy : x ≤ y) (hA : z ≤ F x z) :
    TopParent F H k m :=
  ⟨z, y, hzm, hz, hzR, hy, hyk, Or.inr (a_parent_up hn hall hy hxy hz hA)⟩

/-- **Isolation.** If TopParent fails, no element of height `k` of `R_k` lies above an A-parent of a second top. -/
theorem not_topParent_a_isolated {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m x y z : α} (hnot : ¬ TopParent F H k m) (hzm : z ≠ m)
    (hz : height H z = k + 1) (hzR : z ∈ Rk F (k + 1)) (hy : y ∈ Rk F k) (hxy : x ≤ y) (hA : z ≤ F x z) :
    height H y ≠ k := fun hyk =>
  hnot (topParent_of_a_parent_le_top hn hall hzm hz hzR hy hyk hxy hA)

/-- Terminal sources of the A-normal form: stage `0`, or new at stage `t' + 1`, B-entered, not A-entered. -/
def ATerminal (F : α →o α →o α) (t : ℕ) (q : α) : Prop :=
  t = 0 ∨ ∃ t', t = t' + 1 ∧ q ∉ Rk F t' ∧ b F q ∈ Rk F t' ∧ ¬ ∃ r ∈ Rk F t', q ≤ a F r

/-- **A-normal form.** -/
theorem a_normal : ∀ (s : ℕ) (q : α), q ∈ Rk F s →
    ∃ i t q', t + i ≤ s ∧ q' ∈ Rk F t ∧ q ≤ (a F)^[i] q' ∧ ATerminal F t q'
  | 0, q, hq => ⟨0, 0, q, le_refl _, hq, le_rfl, Or.inl rfl⟩
  | s + 1, q, hq => by
      classical
      by_cases hA : ∃ r ∈ Rk F s, q ≤ a F r
      · obtain ⟨r, hr, hqr⟩ := hA
        obtain ⟨i, t, q', hti, hq', hrq, ht⟩ := a_normal s r hr
        refine ⟨i + 1, t, q', by omega, hq', ?_, ht⟩
        rw [Function.iterate_succ_apply']; exact hqr.trans ((a F).mono hrq)
      · by_cases hold : q ∈ Rk F s
        · obtain ⟨i, t, q', hti, hq', hle, ht⟩ := a_normal s q hold
          exact ⟨i, t, q', by omega, hq', hle, ht⟩
        · rcases mem_succ_iff.1 hq with h | h | h
          · exact absurd h hold
          · exact absurd h hA
          · exact ⟨0, s + 1, q, le_refl _, hq, le_rfl, Or.inr ⟨s, rfl, hold, h, hA⟩⟩

/-- An element of maximum height in a nonempty set (heights are bounded by `H`; no finiteness of the set). -/
theorem exists_max_height {H : ℕ} {S : Set α} (hS : S.Nonempty) :
    ∃ x ∈ S, ∀ y ∈ S, height H y ≤ height H x := by
  classical
  obtain ⟨y0, hy0⟩ := hS
  let P : ℕ → Prop := fun n => ∃ y ∈ S, height H y = n
  have hP : P (Nat.findGreatest P H) :=
    Nat.findGreatest_spec (P := P) (height_le (H := H) y0) ⟨y0, hy0, rfl⟩
  obtain ⟨x, hx, hxe⟩ := hP
  exact ⟨x, hx, fun y hy => hxe ▸ Nat.le_findGreatest (height_le (H := H) y) ⟨y, hy, rfl⟩⟩

/-- **Maximum-height A-parent normalization** (Deliverable A1): an A-parent of maximum height among the A-parents
of `z` in `R_k` is its own normal form `a^[i] q'` with a terminal source `q'`. -/
theorem max_a_parent_normal {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {x z : α} (hx : x ∈ Rk F k) (hz : height H z = k + 1) (hA : z ≤ F x z)
    (hmax : ∀ y ∈ Rk F k, z ≤ F y z → height H y ≤ height H x) :
    ∃ i t q', t + i ≤ k ∧ q' ∈ Rk F t ∧ x = (a F)^[i] q' ∧ ATerminal F t q' ∧ F x z = z := by
  obtain ⟨i, t, q', hti, hq', hle, ht⟩ := a_normal k x hx
  have hy : (a F)^[i] q' ∈ Rk F k := Rk_mono hti (aIter_mem hq' i)
  have hyz : F ((a F)^[i] q') z = z := a_parent_up hn hall hy hle hz hA
  have hxy : x = (a F)^[i] q' := by
    by_contra hne
    have := height_strictMono hn (lt_of_le_of_ne hle hne)
    have := hmax _ hy hyz.ge; omega
  exact ⟨i, t, q', hti, hq', hxy, ht, hxy ▸ hyz⟩

/-- **Late elements are not diagonal pre-fixed** (given `OHAt` below `k + 1`). -/
theorem late_not_pre {k H : ℕ} (IH : ∀ H' < k + 1, OHAt.{u} H') (hn : NoChain α (H + 1)) {x : α}
    (hxk : height H x ≤ k) (hx : x ∉ Rk F k) : ¬ F x x ≤ x := fun hpre =>
  hx (Rk_mono hxk (diagGood_of_ohBelow IH hn hpre (by omega)))

/-! ### The B-side (§34.3z¹⁶⁸) -/

/-- **A B-parent below its top is on time.** With `OHAt` below `k + 1`, `R_{k+1}` tight and `h(z) = k + 2`: a
B-parent `x ∈ R_{k+1}` of `z` (`F x z = x`) with `x ≤ z` has height `k + 1`. (`F x x ≤ F x z = x`, so a late `x`
would be diagonal pre-fixed, contradicting `late_not_pre`.) -/
theorem b_parent_le_ontime {k H : ℕ} (IH : ∀ H' < k + 1, OHAt.{u} H') (hn : NoChain α (H + 1))
    (hk1 : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {x z : α} (hx : x ∈ Rk F (k + 1))
    (hz : height H z = k + 2) (hB : F x z = x) (hxz : x ≤ z) : height H x = k + 1 := by
  have hnew : x ∉ Rk F k := top_parent_new hk1 hz (Or.inl hB.le)
  have hpre : F x x ≤ x := ((F x).mono hxz).trans hB.le
  have := hk1 x hx
  by_contra hne
  exact late_not_pre IH hn (by omega) hnew hpre

/-- **Late B-parents are incomparable with their top.** -/
theorem late_b_parent_not_le {k H : ℕ} (IH : ∀ H' < k + 1, OHAt.{u} H') (hn : NoChain α (H + 1))
    (hk1 : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {x z : α} (hx : x ∈ Rk F (k + 1))
    (hz : height H z = k + 2) (hB : F x z = x) (hlate : height H x ≤ k) : ¬ x ≤ z := fun hxz => by
  have := b_parent_le_ontime IH hn hk1 hx hz hB hxz; omega

/-- **A comparable B-source gives TopParent.** A second top `z` whose least B-source `b z ∈ R_{k+1}` lies below
it has the on-time B-parent `b z`. -/
theorem topParent_of_b_le {k H : ℕ} (IH : ∀ H' < k + 1, OHAt.{u} H') (hn : NoChain α (H + 1))
    (hk1 : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m z : α} (hzm : z ≠ m) (hz : height H z = k + 2)
    (hzR : z ∈ Rk F (k + 2)) (hb : b F z ∈ Rk F (k + 1)) (hbz : b F z ≤ z) : TopParent F H (k + 1) m :=
  ⟨z, b F z, hzm, hz, hzR, hb, b_parent_le_ontime IH hn hk1 hb hz (col_b z) hbz, Or.inl (col_b z)⟩

/-- **A row gfp at the top layer gives TopParent.** If `y ∈ T_{k}` has `a y ≠ m` of height `k + 1`, the row `y`
is an on-time A-parent of the second top `a y`. -/
theorem topParent_of_a_top {k H : ℕ} {m y : α} (hy : y ∈ Rk F k) (hyk : height H y = k)
    (hay : height H (a F y) = k + 1) (hm : a F y ≠ m) : TopParent F H k m :=
  ⟨a F y, y, hm, hay, mem_succ_of_a hy le_rfl, hy, hyk, Or.inr (row_a y)⟩

/-- **Global constraints of a TopParent failure.** If TopParent fails: every `y ∈ T_k` has `a y = m` or
`h(a y) ≤ k` (with tight `R_{k+1}`); and every second top `z` has `b z ≰ z` whenever `b z ∈ R_k` (at stage `k + 1`
indexing, with `OHAt` below `k + 1`). For the feeder, `a m' ≠ m` when `F m' m ≤ m' < m`. -/
theorem not_topParent_a_low {k H : ℕ} (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m y : α}
    (hnot : ¬ TopParent F H k m) (hy : y ∈ Rk F k) (hyk : height H y = k) :
    a F y = m ∨ height H (a F y) ≤ k := by
  by_cases hm : a F y = m
  · exact Or.inl hm
  · have := hall _ (mem_succ_of_a hy le_rfl)
    by_contra h; push_neg at h
    exact hnot (topParent_of_a_top hy hyk (by omega) hm)

theorem feeder_a_ne {m' m : α} (hlo : F m' m ≤ m') (hlt : m' < m) : a F m' ≠ m := fun e =>
  absurd ((e ▸ row_a m').symm.le.trans hlo) (not_le_of_gt hlt)

/-- **CanonicalTopParent** (conjectured, §34.3z¹⁶⁸): one of the two canonical mechanisms — a top `y` of `R_k` whose
row gfp `a y ≠ m` is a top of `R_{k+1}`, or a second top `z` whose least B-source `b z ∈ R_k` lies below it. -/
def CanonicalTopParent (F : α →o α →o α) (H k : ℕ) (m : α) : Prop :=
  (∃ y ∈ Rk F k, height H y = k ∧ a F y ≠ m ∧ height H (a F y) = k + 1) ∨
    ∃ z, z ≠ m ∧ height H z = k + 1 ∧ b F z ∈ Rk F k ∧ b F z ≤ z

/-- CanonicalTopParent implies TopParent (stage `k + 1` indexing; `OHAt` below `k + 1` for the B-mechanism). -/
theorem topParent_of_canonical {k H : ℕ} (IH : ∀ H' < k + 1, OHAt.{u} H') (hn : NoChain α (H + 1))
    (hk1 : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m : α} (h : CanonicalTopParent F H (k + 1) m) :
    TopParent F H (k + 1) m := by
  rcases h with ⟨y, hy, hyk, hm, hay⟩ | ⟨z, hzm, hz, hb, hbz⟩
  · exact topParent_of_a_top hy hyk hay hm
  · exact topParent_of_b_le IH hn hk1 hzm hz (mem_succ_of_b hb) hb hbz

/-! ### Feeder-row descent into the canonical disjunction (§34.3z¹⁶⁹) -/

/-- `rowCollapse_to_BTop` (the brief's Priority A) is CanonicalTopParent itself: `¬A → B` is `A ∨ B`. -/
theorem rowCollapse_iff_canonical {H k : ℕ} {m : α} :
    ((¬ ∃ y ∈ Rk F k, height H y = k ∧ a F y ≠ m ∧ height H (a F y) = k + 1) →
      ∃ z, z ≠ m ∧ height H z = k + 1 ∧ b F z ∈ Rk F k ∧ b F z ≤ z) ↔ CanonicalTopParent F H k m := by
  unfold CanonicalTopParent; exact (or_iff_not_imp_left).symm

/-- **Row descent above the row.** If the row `x` stays above `x` on its pre-fixed columns in `(x, v]`, it has a cell
in `(x, v]` (generalizes `row_cell_of_diag_post`, whose hypothesis `x ≤ F x x` implies this one). -/
theorem row_cell_of_above {H : ℕ} (hn : NoChain α (H + 1)) {x v : α}
    (habove : ∀ u, x < u → u ≤ v → F x u ≤ u → x ≤ F x u) :
    ∀ (n : ℕ) {u : α}, height H u ≤ n → x < u → u ≤ v → F x u ≤ u →
      ∃ z, x < z ∧ z ≤ u ∧ (F x z ≤ x ∨ z ≤ F x z)
  | 0, u, hu, hxu, _, _ => by have := height_strictMono hn hxu; omega
  | n + 1, u, hu, hxu, huv, hFu => by
      by_cases h1 : F x u ≤ x
      · exact ⟨u, hxu, le_rfl, Or.inl h1⟩
      by_cases h2 : u ≤ F x u
      · exact ⟨u, hxu, le_rfl, Or.inr h2⟩
      have hxg : x < F x u := lt_of_le_not_ge (habove u hxu huv hFu) h1
      have hgu : F x u < u := lt_of_le_not_ge hFu h2
      have := height_strictMono hn hgu
      obtain ⟨z, hz1, hz2, hz3⟩ :=
        row_cell_of_above hn habove n (by omega) hxg (hgu.le.trans huv) ((F x).mono hFu)
      exact ⟨z, hz1, hz2.trans hgu.le, hz3⟩

/-- **Canonical mechanism from a row descent.** Let `x ∈ R_k` with `h(x) = k`, `x < v`, `F x v ≤ v`, and suppose the
row `x` stays above `x` on its pre-fixed columns in `(x, v]`. If `m ≰ v`, CanonicalTopParent holds: the first cell
`z ∈ (x, v]` is a top `≠ m`; an upper cell makes `z = a x` (mechanism A), a lower cell gives `b z ≤ x < z`
(mechanism B). -/
theorem canonical_of_row_descent {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m x v : α} (hx : x ∈ Rk F k) (hxk : height H x = k)
    (hxv : x < v) (hFv : F x v ≤ v) (hmv : ¬ m ≤ v)
    (habove : ∀ u, x < u → u ≤ v → F x u ≤ u → x ≤ F x u) : CanonicalTopParent F H k m := by
  obtain ⟨z, hz1, hz2, hz3⟩ := row_cell_of_above hn habove H (height_le _) hxv le_rfl hFv
  have hzR := mem_succ_of_cell hx le_rfl hz3
  have := height_strictMono hn hz1; have := hall z hzR
  have hz : height H z = k + 1 := by omega
  have hzm : z ≠ m := fun e => hmv (e ▸ hz2)
  rcases hz3 with h | h
  · have hb : b F z ≤ x := b_le h
    exact Or.inr ⟨z, hzm, hz, Rk_down k hb hx, hb.trans hz1.le⟩
  · have hle : z ≤ a F x := le_a h
    have e : z = a F x := by
      by_contra hne
      have := height_strictMono hn (lt_of_le_of_ne hle hne)
      have := hall _ (mem_succ_of_a hx le_rfl); omega
    exact Or.inl ⟨x, hx, hxk, e ▸ hzm, e ▸ hz⟩

/-- **The feeder-row descent from the column output.** In the no-cell configuration (`y = m ⊔ F m y`,
`w = F m y ∥ m`), with the feeder `m' ∈ R_k`, `h(m') = k`, `m' ≤ m`, `m' ≤ F m' m`: if the row `m'` stays above `m'`
on its pre-fixed columns in `(m', w]`, CanonicalTopParent holds. -/
theorem canonical_of_feeder_descent {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m' m y : α} (hm' : m' ∈ Rk F k) (hm'k : height H m' = k)
    (hm'm : m' ≤ m) (hfeed : m' ≤ F m' m) (hy : m ⊔ F m y = y) (hmw : ¬ m ≤ F m y) (hwm : ¬ F m y ≤ m)
    (habove : ∀ u, m' < u → u ≤ F m y → F m' u ≤ u → m' ≤ F m' u) : CanonicalTopParent F H k m := by
  have hmy : m ≤ y := le_sup_left.trans hy.le
  have hm'w : m' ≤ F m y := hfeed.trans (((F m').mono hmy).trans ((F.mono hm'm) y))
  have hlt : m' < F m y := lt_of_le_of_ne hm'w fun e => hwm (e ▸ hm'm)
  exact canonical_of_row_descent hn hall hm' hm'k hlt (feeder_le_side hm'm hy) hmw habove

/-- **DescentWitness** (conjectured, §34.3z¹⁶⁹): a top row `x ∈ T_k` and a row-pre-fixed column `v ≱ m` above `x`
on whose interval `(x, v]` the row stays above `x` at its pre-fixed columns. Generalizes a diagonal post-fixed top
(`x ≤ F x x` gives the condition for every `v ≥ x`). -/
def DescentWitness (F : α →o α →o α) (H k : ℕ) (m : α) : Prop :=
  ∃ x ∈ Rk F k, height H x = k ∧ ∃ v, x < v ∧ F x v ≤ v ∧ ¬ m ≤ v ∧
    ∀ u, x < u → u ≤ v → F x u ≤ u → x ≤ F x u

theorem canonical_of_descentWitness {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m : α} (h : DescentWitness F H k m) :
    CanonicalTopParent F H k m := by
  obtain ⟨x, hx, hxk, v, hxv, hFv, hmv, habove⟩ := h
  exact canonical_of_row_descent hn hall hx hxk hxv hFv hmv habove

/-- **TopParent from a descent witness** (stage `k + 1` indexing). -/
theorem topParent_of_descentWitness {k H : ℕ} (IH : ∀ H' < k + 1, OHAt.{u} H') (hn : NoChain α (H + 1))
    (hk1 : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) (hall : ∀ z ∈ Rk F (k + 2), height H z ≤ k + 2) {m : α}
    (h : DescentWitness F H (k + 1) m) : TopParent F H (k + 1) m :=
  topParent_of_canonical IH hn hk1 (canonical_of_descentWitness hn hall h)

/-! ### Drop geometry of the feeder row (§34.3z¹⁷⁰)

A *drop* of the row `m'` on `(m', w]` is a column `q` with `m' < q ≤ w`, `F m' q ≤ q`, `m' ≰ F m' q`; write
`r = F m' q`. -/

/-- The drop output is strictly below the drop column. -/
theorem drop_lt {m' q : α} (hm'q : m' < q) (hFq : F m' q ≤ q) (hdrop : ¬ m' ≤ F m' q) : F m' q < q :=
  lt_of_le_of_ne hFq fun e => hdrop (by rw [e]; exact hm'q.le)

/-- The drop output is again row-pre-fixed for the feeder. -/
theorem drop_row_pre {m' q : α} (hFq : F m' q ≤ q) : F m' (F m' q) ≤ F m' q := (F m').mono hFq

/-- The drop output meets `m` below the feeder (`w ⊓ m = m'` from `single_lower_meet`). -/
theorem drop_meet {m' m w q : α} (hqw : q ≤ w) (hmeet : w ⊓ m = m') (hFq : F m' q ≤ q) : F m' q ⊓ m ≤ m' :=
  (inf_le_inf_right m (hFq.trans hqw)).trans hmeet.le

/-- **A drop with output below the feeder is mechanism B**: `q` is a second top with `b q ≤ m' < q`. -/
theorem canonical_of_drop_le {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m' m q : α} (hm' : m' ∈ Rk F k) (hm'k : height H m' = k) (hm'q : m' < q) (hmq : ¬ m ≤ q)
    (hle : F m' q ≤ m') : CanonicalTopParent F H k m := by
  have hqR := mem_succ_of_cell hm' le_rfl (Or.inl hle)
  have := height_strictMono hn hm'q; have := hall q hqR
  have hb : b F q ≤ m' := b_le hle
  exact Or.inr ⟨q, fun e => hmq (e ▸ le_rfl), by omega, Rk_down k hb hm', hb.trans hm'q.le⟩

/-- **Drop dichotomy.** For a drop `q` with `m ≰ q`: CanonicalTopParent holds, or the drop output is incomparable
with the feeder. -/
theorem drop_incomparable_or_canonical {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m' m q : α} (hm' : m' ∈ Rk F k) (hm'k : height H m' = k)
    (hm'q : m' < q) (hmq : ¬ m ≤ q) (hdrop : ¬ m' ≤ F m' q) :
    CanonicalTopParent F H k m ∨ (¬ F m' q ≤ m' ∧ ¬ m' ≤ F m' q) := by
  by_cases hle : F m' q ≤ m'
  · exact Or.inl (canonical_of_drop_le hn hall hm' hm'k hm'q hmq hle)
  · exact Or.inr ⟨hle, hdrop⟩

/-! ### The raw feeder orbit ends at `a m'` (§34.3z¹⁷¹) -/

/-- `a m'` is below the column gfp `y` (`y` dominates every post-fixed point of `z ↦ m ⊔ F m z`, as
`colOrb_dichotomy` provides). -/
theorem feeder_a_le_y {m' m y : α} (hm'm : m' ≤ m) (hmax : ∀ z, z ≤ m ⊔ F m z → z ≤ y) : a F m' ≤ y :=
  hmax _ ((row_a m').symm.le.trans (((F.mono hm'm) (a F m')).trans le_sup_right))

/-- **`a m' ≤ w`.** -/
theorem feeder_a_le_w {m' m y : α} (hm'm : m' ≤ m) (hmax : ∀ z, z ≤ m ⊔ F m z → z ≤ y) : a F m' ≤ F m y :=
  (row_a m').symm.le.trans (((F m').mono (feeder_a_le_y hm'm hmax)).trans ((F.mono hm'm) y))

/-- The feeder-row iterates of anything above `a m'` stay above `a m'`. -/
theorem a_le_iter {x v : α} (hv : a F x ≤ v) : ∀ n, a F x ≤ (F x)^[n] v
  | 0 => hv
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      exact (row_a x).symm.le.trans ((F x).mono (a_le_iter hv n))

/-- **The raw row orbit of a row-pre-fixed column stabilizes** (finite edge-height). -/
theorem exists_iter_fix {H : ℕ} (hn : NoChain α (H + 1)) {x : α} :
    ∀ (k : ℕ) {v : α}, height H v ≤ k → F x v ≤ v → ∃ n, F x ((F x)^[n] v) = (F x)^[n] v
  | 0, v, hv, hFv => by
      refine ⟨0, le_antisymm hFv ?_⟩
      by_contra hne
      have := height_strictMono hn (lt_of_le_not_ge hFv hne); omega
  | k + 1, v, hv, hFv => by
      by_cases he : F x v = v
      · exact ⟨0, he⟩
      have hlt : F x v < v := lt_of_le_of_ne hFv he
      have := height_strictMono hn hlt
      obtain ⟨n, hn'⟩ := exists_iter_fix hn k (by omega) ((F x).mono hFv)
      exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn'⟩

/-- **`rawDropOrbit_terminal`**: a fixed point of the row `x` reached by iterating from a column above `a x` is
`a x` itself. Applied to the feeder from `w` (or from the drop output `r`, which is `≥ a m'`): the raw feeder orbit
ends exactly at `a m'`. -/
theorem rawOrbit_terminal {x v : α} (hv : a F x ≤ v) {n : ℕ} (hfix : F x ((F x)^[n] v) = (F x)^[n] v) :
    (F x)^[n] v = a F x :=
  le_antisymm (le_a hfix.ge) (a_le_iter hv n)

/-- The drop output dominates `a m'`: `a m' ≤ F m' q` for every column `q ≥ a m'`. -/
theorem a_le_drop {m' q : α} (hq : a F m' ≤ q) : a F m' ≤ F m' q :=
  (row_a m').symm.le.trans ((F m').mono hq)

/-- **A feeder below its row gfp gives mechanism A.** In the no-cell configuration (`hmax`, `m ≰ w`), if
`m' < a m'` then `a m'` is a second top with the on-time A-parent `m'`. -/
theorem canonical_of_feeder_lt_a {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m' m y : α} (hm' : m' ∈ Rk F k) (hm'k : height H m' = k)
    (hm'm : m' ≤ m) (hmax : ∀ z, z ≤ m ⊔ F m z → z ≤ y) (hmw : ¬ m ≤ F m y) (hlt : m' < a F m') :
    CanonicalTopParent F H k m := by
  have hR := mem_succ_of_a hm' (le_refl (a F m'))
  have := height_strictMono hn hlt; have := hall _ hR
  exact Or.inl ⟨m', hm', hm'k, fun e => hmw (e.symm.le.trans (feeder_a_le_w hm'm hmax)), by omega⟩

/-- **The feeder descent must leave `↑m'`.** In the no-cell configuration, unless CanonicalTopParent holds or the
feeder is diagonal post-fixed (`m' ≤ F m' m'`, settled by `secondEntry_of_post_layer`), the raw feeder orbit from
`w` reaches a column not above `m'` — namely its terminal value `a m'`, with `m' ≰ a m'`. -/
theorem feeder_descent_leaves {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m' m y : α} (hm' : m' ∈ Rk F k) (hm'k : height H m' = k)
    (hm'm : m' ≤ m) (hy : m ⊔ F m y = y) (hmax : ∀ z, z ≤ m ⊔ F m z → z ≤ y) (hmw : ¬ m ≤ F m y) :
    CanonicalTopParent F H k m ∨ m' ≤ F m' m' ∨
      ∃ n, (F m')^[n] (F m y) = a F m' ∧ F m' ((F m')^[n] (F m y)) = (F m')^[n] (F m y) ∧ ¬ m' ≤ a F m' := by
  by_cases hle : m' ≤ a F m'
  · rcases eq_or_lt_of_le hle with e | hlt
    · exact Or.inr (Or.inl (e.trans ((row_a m').symm.trans (by rw [← e]))).le)
    · exact Or.inl (canonical_of_feeder_lt_a hn hall hm' hm'k hm'm hmax hmw hlt)
  · obtain ⟨n, hfix⟩ := exists_iter_fix (x := m') hn H (height_le _) (feeder_le_side hm'm hy)
    exact Or.inr (Or.inr ⟨n, rawOrbit_terminal (feeder_a_le_w hm'm hmax) hfix, hfix, hle⟩)

/-! ### UpCell: the weakest row-cell target, and the packaged reduction of `SingletonLower` (§34.3z¹⁷²) -/

/-- **UpCell**: some top row `x ∈ T_k` has a cell at a column strictly above `x` and not above `m`. -/
def UpCell (F : α →o α →o α) (H k : ℕ) (m : α) : Prop :=
  ∃ x ∈ Rk F k, height H x = k ∧ ∃ z, x < z ∧ ¬ m ≤ z ∧ (F x z ≤ x ∨ z ≤ F x z)

/-- DescentWitness gives UpCell (`row_cell_of_above`). -/
theorem upCell_of_descentWitness {k H : ℕ} (hn : NoChain α (H + 1)) {m : α} (h : DescentWitness F H k m) :
    UpCell F H k m := by
  obtain ⟨x, hx, hxk, v, hxv, hFv, hmv, habove⟩ := h
  obtain ⟨z, hz1, hz2, hz3⟩ := row_cell_of_above hn habove H (height_le _) hxv le_rfl hFv
  exact ⟨x, hx, hxk, z, hz1, fun h => hmv (h.trans hz2), hz3⟩

/-- UpCell gives CanonicalTopParent (the two cell types are the two mechanisms). -/
theorem canonical_of_upCell {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m : α} (h : UpCell F H k m) : CanonicalTopParent F H k m := by
  obtain ⟨x, hx, hxk, z, hz1, hmz, hz3⟩ := h
  have hzR := mem_succ_of_cell hx le_rfl hz3
  have := height_strictMono hn hz1; have := hall z hzR
  have hz : height H z = k + 1 := by omega
  have hzm : z ≠ m := fun e => hmz (e ▸ le_rfl)
  rcases hz3 with h | h
  · have hb : b F z ≤ x := b_le h
    exact Or.inr ⟨z, hzm, hz, Rk_down k hb hx, hb.trans hz1.le⟩
  · have hle : z ≤ a F x := le_a h
    have e : z = a F x := by
      by_contra hne
      have := height_strictMono hn (lt_of_le_of_ne hle hne)
      have := hall _ (mem_succ_of_a hx le_rfl); omega
    exact Or.inl ⟨x, hx, hxk, e ▸ hzm, e ▸ hz⟩

/-- CanonicalTopParent gives SecondEntry directly (no `OHAt`). -/
theorem secondEntry_of_canonical {k H : ℕ} {m : α} (h : CanonicalTopParent F H k m) : SecondEntry F H k m := by
  rcases h with ⟨y, hy, -, hm, hay⟩ | ⟨z, hzm, hz, hb, -⟩
  · exact ⟨a F y, hm, hay, mem_succ_of_a hy le_rfl⟩
  · exact ⟨z, hzm, hz, mem_succ_of_b hb⟩

/-- **The packaged reduction of `SingletonLower`.** If, in every uniqueness-free singleton configuration whose top
`m` has no interval cell, some top row of `R_k` has a cell above itself away from `m` (UpCell), then
`SingletonLower F H` holds. (By `upCell_of_descentWitness`, DescentWitness suffices.) -/
theorem singletonLower_of_upCell {H : ℕ} (hn : NoChain α (H + 1))
    (hup : ∀ k, (⊤ : α) ∉ Rk F (k + 2) → (∀ z ∈ Rk F k, height H z ≤ k) →
      (∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) → ∀ m, m ∈ Rk F (k + 1) → height H m = k + 1 → m ∉ Rk F k →
      ∀ m' ∈ Rk F k, height H m' = k → m' < m → F m' m ≤ m' →
      (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) → UpCell F H k m) :
    SingletonLower F H := by
  intro k htop hk hall m huniq hm hmk hnew m' hm' hm'k hlt hlo
  by_contra hno
  obtain ⟨z, hzm, hz, hzR⟩ :=
    secondEntry_of_canonical (canonical_of_upCell hn hall (hup k htop hk hall m hm hmk hnew m' hm' hm'k hlt hlo hno))
  exact hzm (huniq z hzR hz)

/-! ### Consequences of ¬UpCell, top-row normal form, feeder source (§34.3z¹⁷³) -/

/-- **No UpCell forces an incomparable drop on every upward pre-fixed interval of every top row.** -/
theorem noUpCell_forces_incomparable_drop {k H : ℕ} (hn : NoChain α (H + 1)) {m x v : α}
    (hnot : ¬ UpCell F H k m) (hx : x ∈ Rk F k) (hxk : height H x = k) (hxv : x < v) (hFv : F x v ≤ v)
    (hmv : ¬ m ≤ v) : ∃ u, x < u ∧ u ≤ v ∧ F x u ≤ u ∧ ¬ x ≤ F x u ∧ ¬ F x u ≤ x := by
  by_contra hno
  push_neg at hno
  apply hnot
  refine upCell_of_descentWitness hn ⟨x, hx, hxk, v, hxv, hFv, hmv, fun u hxu huv hFu => ?_⟩
  by_contra hge
  have hle := hno u hxu huv hFu hge
  exact hnot ⟨x, hx, hxk, u, hxu, fun h => hmv (h.trans huv), Or.inl hle⟩

/-- **Top-row normal form.** A top `x ∈ R_k` (`h(x) = k`, `R_k` tight) *equals* `a^[i] q'` for a terminal source
`q' ∈ R_t`, `t + i ≤ k`. -/
theorem topRow_normalForm {k H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F k, height H z ≤ k) {x : α}
    (hx : x ∈ Rk F k) (hxk : height H x = k) :
    ∃ i t q', t + i ≤ k ∧ q' ∈ Rk F t ∧ x = (a F)^[i] q' ∧ ATerminal F t q' := by
  obtain ⟨i, t, q', hti, hq', hle, ht⟩ := a_normal k x hx
  refine ⟨i, t, q', hti, hq', ?_, ht⟩
  by_contra hne
  have := height_strictMono hn (lt_of_le_of_ne hle hne)
  have := hk _ (Rk_mono hti (aIter_mem hq' i)); omega

/-- For rigid maps (`a ⊥ = ⊥`) the terminal source of a nonzero top row is B-entered, never at stage `0`. -/
theorem topRow_terminal_B {k H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F k, height H z ≤ k)
    (hr : a F ⊥ = ⊥) {x : α} (hx : x ∈ Rk F k) (hxk : height H x = k) (hk0 : 0 < k) :
    ∃ i t' q', t' + 1 + i ≤ k ∧ q' ∈ Rk F (t' + 1) ∧ x = (a F)^[i] q' ∧ q' ∉ Rk F t' ∧ b F q' ∈ Rk F t' ∧
      ¬ ∃ r ∈ Rk F t', q' ≤ a F r := by
  obtain ⟨i, t, q', hti, hq', hxe, ht⟩ := topRow_normalForm hn hk hx hxk
  rcases ht with h0 | ⟨t', rfl, h1, h2, h3⟩
  · subst h0
    have hq : q' = ⊥ := le_bot_iff.1 hq'
    have hxb : x = ⊥ := by rw [hxe, hq, pureA_rigid hr]
    have hc := chainTo_height (H := H) x
    rw [hxk] at hc
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [hj] at hc
    obtain ⟨y, hy, -⟩ := hc
    exact absurd (hxb ▸ hy) (not_lt_bot)
  · exact ⟨i, t', q', hti, hq', hxe, h1, h2, h3⟩

/-- **The feeder's own B-source is strictly below it** when the feeder is not diagonal post-fixed. -/
theorem feeder_b_lt {m' m : α} (hm'm : m' ≤ m) (hlo : F m' m ≤ m') (hnp : ¬ m' ≤ F m' m') : b F m' < m' := by
  have hpre : F m' m' ≤ m' := ((F m').mono hm'm).trans hlo
  refine lt_of_le_of_ne (b_le hpre) fun e => hnp ?_
  have := col_b (F := F) m'; rw [e] at this; exact this.ge

/-! ### Cover sources and cross-evaluation shadows (§34.3z¹⁷⁴) -/

/-- Height difference one makes a strict relation a cover. -/
theorem covBy_of_height {H : ℕ} (hn : NoChain α (H + 1)) {p x : α} (hpx : p < x)
    (hh : height H x = height H p + 1) : p ⋖ x :=
  ⟨hpx, fun y h1 h2 => by
    have := height_strictMono hn h1; have := height_strictMono hn h2; omega⟩

theorem height_bot_eq_zero {H : ℕ} : height H (⊥ : α) = 0 := by
  rcases hh : height H (⊥ : α) with _ | j
  · rfl
  · have hc := chainTo_height (H := H) (⊥ : α)
    rw [hh] at hc
    obtain ⟨y, hy, -⟩ := hc
    exact absurd hy not_lt_bot

/-- **Cover source of a strict B-top** (A1). With `OHAt` below `j + 1`: a top `x` of height `j + 2` that is *new* at
stage `j + 2` (`x ∉ R_{j+1}`) and whose B-source `p = b x` lies below it has `h(p) = j + 1`, so `p ⋖ x`. Neither
tightness of `R_{j+1}` nor `p ∈ R_{j+1}` is needed; newness of `x` is (an early top need not cover its source). -/
theorem strictBTop_has_cover_source {j H : ℕ} (IH : ∀ H' < j + 1, OHAt.{u} H') (hn : NoChain α (H + 1))
    {x : α} (hxk : height H x = j + 2) (hnew : x ∉ Rk F (j + 1)) (hlt : b F x < x) :
    height H (b F x) = j + 1 ∧ b F x ⋖ x := by
  have hlow := height_strictMono hn hlt
  have hp : height H (b F x) = j + 1 := by
    by_contra hne
    have hpj : height H (b F x) ≤ j := by omega
    have hpnew : b F x ∉ Rk F j := fun h => hnew (mem_succ_of_b h)
    exact late_not_pre IH hn hpj hpnew (((F (b F x)).mono hlt.le).trans (col_b x).le)
  exact ⟨hp, covBy_of_height hn hlt (by omega)⟩

/-- The base case: a height-`1` top with B-source in `R_0` is covered by its source `⊥`. -/
theorem strictBTop_has_cover_source_one {H : ℕ} (hn : NoChain α (H + 1)) {x : α} (hxk : height H x = 1)
    (hb : b F x ∈ Rk F 0) : b F x = ⊥ ∧ (⊥ : α) ⋖ x := by
  have hb0 : b F x = ⊥ := le_bot_iff.1 hb
  refine ⟨hb0, covBy_of_height hn (bot_lt_iff_ne_bot.2 fun e => by
    rw [e, height_bot_eq_zero] at hxk; omega) (by rw [height_bot_eq_zero, hxk])⟩

/-- **Cross-evaluation shadow** (A2). Let `p ⋖ x` with `F p x = p`, `p ∈ R_j`, `h(x) = j + 1`, `R_{j+1}` tight, and
let `u` be a drop column of the row `x`: `x < u`, `F x u ≤ u`, `x ≰ r = F x u`. Then the shadow `c = F p u`
satisfies `p < c ≤ r ≤ u` and `c ∥ x` (`r ≰ x` is not needed). -/
theorem cross_shadow {j H : ℕ} (hn : NoChain α (H + 1)) (hk1 : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    {p x u : α} (hp : p ∈ Rk F j) (hxk : height H x = j + 1) (hcov : p ⋖ x) (hpx : F p x = p) (hxu : x < u)
    (hFu : F x u ≤ u) (hr1 : ¬ x ≤ F x u) :
    p < F p u ∧ F p u ≤ F x u ∧ F x u ≤ u ∧ ¬ F p u ≤ x ∧ ¬ x ≤ F p u := by
  have hlo : p ≤ F p u := hpx.symm.le.trans ((F p).mono hxu.le)
  have hhi : F p u ≤ F x u := (F.mono hcov.le) u
  have hne : F p u ≠ p := fun e => by
    have huR := mem_succ_of_cell hp le_rfl (Or.inl e.le)
    have := height_strictMono hn hxu; have := hk1 u huR; omega
  refine ⟨lt_of_le_of_ne hlo (Ne.symm hne), hhi, hFu, fun hcx => ?_, fun hxc => hr1 (hxc.trans hhi)⟩
  rcases hcov.eq_or_eq hlo hcx with e | e
  · exact hne e
  · exact hr1 (e ▸ hhi)

/-- **Source meet** (Programme B). For two rows `x, y` of `R_k` with B-sources in `R_j`: the meet column `d = x ⊓ y`
lies in `R_k`, its B-source `s = b d ≤ b x ⊓ b y` lies in `R_j`, and `F s d = s`; if the sources are incomparable,
`s` is strictly below both. -/
theorem source_meet {j k : ℕ} {x y : α} (hx : x ∈ Rk F k) (hbx : b F x ∈ Rk F j) :
    x ⊓ y ∈ Rk F k ∧ b F (x ⊓ y) ≤ b F x ⊓ b F y ∧ b F (x ⊓ y) ∈ Rk F j ∧ F (b F (x ⊓ y)) (x ⊓ y) = b F (x ⊓ y) :=
  ⟨Rk_down k inf_le_left hx, le_inf ((b F).mono inf_le_left) ((b F).mono inf_le_right),
    Rk_down j ((b F).mono inf_le_left) hbx, col_b _⟩

theorem source_meet_lt {x y : α} (hpq : ¬ b F x ≤ b F y) (hqp : ¬ b F y ≤ b F x) :
    b F (x ⊓ y) < b F x ∧ b F (x ⊓ y) < b F y := by
  have h1 : b F (x ⊓ y) ≤ b F x := (b F).mono inf_le_left
  have h2 : b F (x ⊓ y) ≤ b F y := (b F).mono inf_le_right
  exact ⟨lt_of_le_of_ne h1 fun e => hpq (e ▸ h2), lt_of_le_of_ne h2 fun e => hqp (e ▸ h1)⟩

/-- **The feeder is new at its stage**: `m' ∈ R_j` with `F m' m ≤ m'` would put `m` into `R_{j+1}`. -/
theorem feeder_new {j : ℕ} {m' m : α} (hlo : F m' m ≤ m') (hm : m ∉ Rk F (j + 1)) : m' ∉ Rk F j := fun h =>
  hm (mem_succ_of_cell h le_rfl (Or.inl hlo))

/-- **The feeder covers its own B-source** (OHAt below `j + 1`, feeder not diagonal post-fixed). -/
theorem feeder_cover_source {j H : ℕ} (IH : ∀ H' < j + 1, OHAt.{u} H') (hn : NoChain α (H + 1)) {m' m : α}
    (hm'k : height H m' = j + 2) (hm'm : m' ≤ m) (hlo : F m' m ≤ m') (hnp : ¬ m' ≤ F m' m')
    (hm : m ∉ Rk F (j + 2)) : height H (b F m') = j + 1 ∧ b F m' ⋖ m' :=
  strictBTop_has_cover_source IH hn hm'k (feeder_new hlo hm) (feeder_b_lt hm'm hlo hnp)

/-! ### The top-shadow trichotomy and same-source siblings (§34.3z¹⁷⁵) -/

/-- **Top-shadow trichotomy.** If `p ⋖ c` and `F p c ≤ c`, then `F p c ≤ p`, or `F p c = c`, or `F p c ∥ p`. -/
theorem shadow_trichotomy {p c : α} (hcov : p ⋖ c) (hle : F p c ≤ c) :
    F p c ≤ p ∨ F p c = c ∨ (¬ F p c ≤ p ∧ ¬ p ≤ F p c) := by
  by_cases h1 : F p c ≤ p
  · exact Or.inl h1
  by_cases h2 : p ≤ F p c
  · rcases hcov.eq_or_eq h2 hle with e | e
    · exact absurd e.le h1
    · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- **Same-source sibling.** With `OHAt` below `j + 1`: if the shadow `c` is a top of height `j + 2` new at stage
`j + 2` and `F p c ≤ p` for the height-`(j + 1)` source `p < c`, then `b c = p` and `F p c = p`. -/
theorem sibling_of_shadow {j H : ℕ} (IH : ∀ H' < j + 1, OHAt.{u} H') (hn : NoChain α (H + 1)) {p c : α}
    (hck : height H c = j + 2) (hcnew : c ∉ Rk F (j + 1)) (hph : height H p = j + 1) (hpc : p < c)
    (hle : F p c ≤ p) : b F c = p ∧ F p c = p := by
  have hb : b F c ≤ p := b_le hle
  have hbc := (strictBTop_has_cover_source IH hn hck hcnew (lt_of_le_of_lt hb hpc)).1
  have e : b F c = p := by
    by_contra hne
    have := height_strictMono hn (lt_of_le_of_ne hb hne); omega
  exact ⟨e, by have := col_b (F := F) c; rwa [e] at this⟩

/-- **The source of a new top is new one stage lower.** -/
theorem source_new {j : ℕ} {x : α} (hxnew : x ∉ Rk F (j + 1)) : b F x ∉ Rk F j := fun h =>
  hxnew (mem_succ_of_b h)

/-- **The upper branch is the row gfp of the source**: `F p c = c` with `p ∈ R_j` and `c` of height `j + 1` in a
tight `R_{j+1}` forces `c = a p`. -/
theorem upper_branch_eq_a {j H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    {p c : α} (hp : p ∈ Rk F j) (hck : height H c = j + 1) (heq : F p c = c) : c = a F p := by
  have hle : c ≤ a F p := le_a heq.ge
  by_contra hne
  have := height_strictMono hn (lt_of_le_of_ne hle hne)
  have := hk _ (mem_succ_of_a hp le_rfl); omega

/-- **Sibling join.** Let `p ⋖ c`, `F p x = p` with `p ∈ R_j`, `h(x) = j + 1`, `R_{j+1}` tight, `c ≰ x`, and let `u`
be a column with `x ⊔ c ≤ u` and `F p u = c` (the drop column whose shadow is `c`). Then `F p (x ⊔ c) = c`;
consequently every row `y ≥ p` has `c ≤ F y (x ⊔ c)`. -/
theorem sibling_join {j H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    {p x c u : α} (hp : p ∈ Rk F j) (hxk : height H x = j + 1) (hcov : p ⋖ c) (hpx : F p x = p)
    (hcx : ¬ c ≤ x) (hju : x ⊔ c ≤ u) (hpu : F p u = c) : F p (x ⊔ c) = c := by
  have hlo : p ≤ F p (x ⊔ c) := hpx.symm.le.trans ((F p).mono le_sup_left)
  have hhi : F p (x ⊔ c) ≤ c := ((F p).mono hju).trans hpu.le
  rcases hcov.eq_or_eq hlo hhi with e | e
  · exfalso
    have hR := mem_succ_of_cell hp le_rfl (Or.inl e.le)
    have hlt : x < x ⊔ c := lt_of_le_of_ne le_sup_left fun h => hcx (h ▸ le_sup_right)
    have := height_strictMono hn hlt; have := hk _ hR; omega
  · exact e

theorem sibling_join_lower {p x c y : α} (hpy : p ≤ y) (hj : F p (x ⊔ c) = c) : c ≤ F y (x ⊔ c) :=
  hj.symm.le.trans ((F.mono hpy) (x ⊔ c))

/-! ### SiblingShadowCell, comparable case (§34.3z¹⁷⁶) -/

/-- **The source row is constant on the shadow interval.** Let `p ⋖ c` with `F p c = p`, `p ∈ R_j`, `h(c) = j + 1`,
`R_{j+1}` tight, and `F p u = c`. Then `F p z = c` for every `z ∈ (c, u]`. (The value lies in `[p, c]`; `p` would be
a lower cell putting `z`, of height `> j + 1`, into `R_{j+1}`.) -/
theorem source_row_const {j H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    {p c u z : α} (hp : p ∈ Rk F j) (hck : height H c = j + 1) (hcov : p ⋖ c) (hpc : F p c = p)
    (hpu : F p u = c) (hcz : c < z) (hzu : z ≤ u) : F p z = c := by
  have hlo : p ≤ F p z := hpc.symm.le.trans ((F p).mono hcz.le)
  have hhi : F p z ≤ c := ((F p).mono hzu).trans hpu.le
  rcases hcov.eq_or_eq hlo hhi with e | e
  · exfalso
    have hR := mem_succ_of_cell hp le_rfl (Or.inl e.le)
    have := height_strictMono hn hcz; have := hk z hR; omega
  · exact e

/-- **SiblingShadowCell, comparable case.** In the same setting, with `c ∈ R_{j+1}` a top (`h(c) = j + 1`) and
`m ≰ u`: if some column `z ∈ (c, u]` is comparable with its row-`c` value (`F c z ≤ z` or `z ≤ F c z`), then UpCell
holds, witnessed by the row `c`. On `(c, u]` the row `c` stays above `c` (`F c z ≥ F p z = c`), so a pre-fixed `z`
is a descent witness and a post-fixed `z` is an upper cell. The remaining case is that the row `c` is
*incomparable on the whole interval*: `F c z ∥ z` for every `z ∈ (c, u]`. -/
theorem siblingShadow_upCell {j H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    {m p c u : α} (hp : p ∈ Rk F j) (hc : c ∈ Rk F (j + 1)) (hck : height H c = j + 1) (hcov : p ⋖ c)
    (hpc : F p c = p) (hpu : F p u = c) (hmu : ¬ m ≤ u)
    (hcase : ∃ z, c < z ∧ z ≤ u ∧ (F c z ≤ z ∨ z ≤ F c z)) : UpCell F H (j + 1) m := by
  obtain ⟨z, hcz, hzu, h | h⟩ := hcase
  · refine upCell_of_descentWitness hn ⟨c, hc, hck, z, hcz, h, fun hm => hmu (hm.trans hzu), fun y hcy hyz _ => ?_⟩
    exact (source_row_const hn hk hp hck hcov hpc hpu hcy (hyz.trans hzu)).symm.le.trans ((F.mono hcov.le) y)
  · exact ⟨c, hc, hck, z, hcz, fun hm => hmu (hm.trans hzu), Or.inr h⟩

/-! ### The shadow chain down the B-sources (§34.3z¹⁷⁹) -/

/-- **A drop node**: a diagonal pre-fixed row `p` with a pre-fixed column `c > p` at which it drops. -/
def DropNode (F : α →o α →o α) (p c : α) : Prop := F p p ≤ p ∧ p < c ∧ F p c ≤ c ∧ ¬ p ≤ F p c

/-- **An exit**: a row `r` with a pre-fixed column `e > r` at which it has a lower cell, or stays above itself, or
drops while being its own B-source (`b r = r`, a diagonal fixed point). -/
def ChainExit (F : α →o α →o α) (r e : α) : Prop :=
  r < e ∧ F r e ≤ e ∧ (F r e ≤ r ∨ r ≤ F r e ∨ (b F r = r ∧ ¬ r ≤ F r e))

/-- **One transition.** For a drop node `(p, c)` with `q = b p`: the shadow `e = F q c` satisfies `q ≤ e ≤ c`,
`F q e ≤ e`, and `q` is again diagonal pre-fixed. -/
theorem dropNode_step {p c : α} (h : DropNode F p c) :
    b F p ≤ p ∧ F (b F p) (b F p) ≤ b F p ∧ b F p ≤ F (b F p) c ∧ F (b F p) c ≤ c ∧
      F (b F p) (F (b F p) c) ≤ F (b F p) c := by
  obtain ⟨hpre, hpc, hFc, -⟩ := h
  have hq : b F p ≤ p := b_le hpre
  have hqp : F (b F p) p = b F p := col_b p
  have hec : F (b F p) c ≤ c := ((F.mono hq) c).trans hFc
  exact ⟨hq, ((F (b F p)).mono hq).trans hqp.le, hqp.symm.le.trans ((F (b F p)).mono hpc.le), hec,
    (F (b F p)).mono hec⟩

/-- **The shadow chain terminates in an exit** (no orbit hypotheses). From a drop node `(p, c)`, follow
`p ↦ b p`, `c ↦ F (b p) c` while the new row drops. Heights strictly decrease, so some iterate `r = b^[i] p` has a
column `e ≤ c` forming an exit. -/
theorem dropChain_exit {H : ℕ} (hn : NoChain α (H + 1)) :
    ∀ (n : ℕ) {p c : α}, height H p ≤ n → DropNode F p c →
      ∃ i, ∃ e, e ≤ c ∧ ChainExit F ((b F)^[i] p) e := by
  intro n
  induction n with
  | zero =>
    intro p c hp h
    obtain ⟨hpre, hpc, hFc, hdrop⟩ := h
    refine ⟨0, c, le_rfl, hpc, hFc, Or.inr (Or.inr ⟨?_, hdrop⟩)⟩
    by_contra hne
    have := height_strictMono hn (lt_of_le_of_ne (b_le hpre) hne); omega
  | succ n ih =>
    intro p c hp h
    obtain ⟨hq, hqpre, hqe, hec, hFe⟩ := dropNode_step h
    obtain ⟨hpre, hpc, hFc, hdrop⟩ := h
    by_cases hbp : b F p = p
    · exact ⟨0, c, le_rfl, hpc, hFc, Or.inr (Or.inr ⟨hbp, hdrop⟩)⟩
    have hqlt : b F p < p := lt_of_le_of_ne hq hbp
    by_cases h0 : F (b F p) c ≤ b F p
    · exact ⟨1, c, le_rfl, hqlt.trans hpc, hec, Or.inl h0⟩
    have hqe' : b F p < F (b F p) c := lt_of_le_of_ne hqe fun e => h0 (e ▸ le_rfl)
    by_cases h1 : F (b F p) (F (b F p) c) ≤ b F p
    · exact ⟨1, F (b F p) c, hec, hqe', hFe, Or.inl h1⟩
    by_cases h2 : b F p ≤ F (b F p) (F (b F p) c)
    · exact ⟨1, F (b F p) c, hec, hqe', hFe, Or.inr (Or.inl h2)⟩
    have := height_strictMono hn hqlt
    obtain ⟨i, e, hee, hex⟩ := ih (by omega) ⟨hqpre, hqe', hFe, h2⟩
    exact ⟨i + 1, e, hee.trans hec, by rw [Function.iterate_succ_apply]; exact hex⟩

/-- **The chain rows stay new**: if `p ∉ R_{j+i}` then `b^[i] p ∉ R_j` (iterating `source_new`). -/
theorem iter_source_new {j : ℕ} : ∀ (i : ℕ) {p : α}, p ∉ Rk F (j + i) → (b F)^[i] p ∉ Rk F j
  | 0, p, h => h
  | i + 1, p, h => by
      rw [Function.iterate_succ_apply]
      exact iter_source_new i (source_new (show p ∉ Rk F (j + i + 1) by simpa [Nat.add_assoc] using h))

/-- **A lower exit puts its column one stage up**: `r ∈ R_s`, `F r e ≤ r` give `e ∈ R_{s+1}`. -/
theorem lowerExit_mem {s : ℕ} {r e : α} (hr : r ∈ Rk F s) (hL : F r e ≤ r) : e ∈ Rk F (s + 1) :=
  mem_succ_of_cell hr le_rfl (Or.inl hL)

/-! ### Two-dimensional descent: genuine cell extraction (§34.3z¹⁸⁰) -/

/-- **A drop row has a strict B-source.** `b p = p` would give `F p p = p ≤ F p c`. -/
theorem dropNode_source_lt {p c : α} (h : DropNode F p c) : b F p < p := by
  obtain ⟨hpre, hpc, -, hdrop⟩ := h
  refine lt_of_le_of_ne (b_le hpre) fun e => hdrop ?_
  have := col_b (F := F) p; rw [e] at this
  exact this.symm.le.trans ((F p).mono hpc.le)

/-- **The D-exit is impossible**: a row that is its own B-source stays above itself on every column above it. -/
theorem chainExit_not_D {r e : α} (hre : r < e) (hb : b F r = r) : r ≤ F r e := by
  have := col_b (F := F) r; rw [hb] at this
  exact this.symm.le.trans ((F r).mono hre.le)

/-- The state of the two-dimensional descent: a diagonal pre-fixed row `r` with a pre-fixed column `e > r`. -/
def CellState (F : α →o α →o α) (r e : α) : Prop := F r r ≤ r ∧ r < e ∧ F r e ≤ e

/-- **Two-dimensional descent.** From `CellState r e`, some B-iterate `b^[i] r` has a *cell* at a column
`z ≤ e` above it. Measure `h(r) + h(e)`: an intermediate output `r < F r e < e` keeps the row and lowers the column;
an incomparable output is a drop node, and passing to `b r < r` (`dropNode_source_lt`) with column `F (b r) e ≤ e`
lowers the row. -/
theorem cellState_cell {H : ℕ} (hn : NoChain α (H + 1)) :
    ∀ (n : ℕ) {r e : α}, height H r + height H e ≤ n → CellState F r e →
      ∃ i z, z ≤ e ∧ (b F)^[i] r < z ∧ (F ((b F)^[i] r) z ≤ (b F)^[i] r ∨ z ≤ F ((b F)^[i] r) z) := by
  have hmono := (height_strictMono (H := H) hn).monotone
  intro n
  induction n with
  | zero =>
    intro r e hh h
    have := height_strictMono hn h.2.1; omega
  | succ n ih =>
    intro r e hh h
    obtain ⟨hpre, hre, hFe⟩ := h
    by_cases h1 : F r e ≤ r
    · exact ⟨0, e, le_rfl, hre, Or.inl h1⟩
    by_cases h2 : e ≤ F r e
    · exact ⟨0, e, le_rfl, hre, Or.inr h2⟩
    by_cases h3 : r ≤ F r e
    · have hrt : r < F r e := lt_of_le_of_ne h3 fun e' => h1 (e' ▸ le_rfl)
      have hte : F r e < e := lt_of_le_not_ge hFe h2
      have := height_strictMono hn hte
      obtain ⟨i, z, hz, hlt, hc⟩ := ih (by omega) ⟨hpre, hrt, (F r).mono hFe⟩
      exact ⟨i, z, hz.trans hte.le, hlt, hc⟩
    · have hd : DropNode F r e := ⟨hpre, hre, hFe, h3⟩
      have hqlt := dropNode_source_lt hd
      obtain ⟨-, hqpre, hqe, hec, hFe'⟩ := dropNode_step hd
      by_cases h4 : F (b F r) e ≤ b F r
      · exact ⟨1, e, le_rfl, hqlt.trans hre, Or.inl h4⟩
      have hqe' : b F r < F (b F r) e := lt_of_le_of_ne hqe fun e' => h4 (e' ▸ le_rfl)
      have := height_strictMono hn hqlt; have := hmono hec
      obtain ⟨i, z, hz, hlt, hc⟩ := ih (by omega) ⟨hqpre, hqe', hFe'⟩
      refine ⟨i + 1, z, hz.trans hec, ?_, ?_⟩ <;> rw [Function.iterate_succ_apply] <;> assumption

/-- **`dropNode_cell`** (the brief's strengthening of `dropChain_exit`): a drop node yields a genuine cell on some
B-iterate of its row, at a column `≤ c`. -/
theorem dropNode_cell {H : ℕ} (hn : NoChain α (H + 1)) {p c : α} (h : DropNode F p c) :
    ∃ i z, z ≤ c ∧ (b F)^[i] p < z ∧ (F ((b F)^[i] p) z ≤ (b F)^[i] p ∨ z ≤ F ((b F)^[i] p) z) :=
  cellState_cell hn _ le_rfl ⟨h.1, h.2.1, h.2.2.1⟩

/-- **The feeder's two-dimensional descent from `w`**: in the no-cell configuration (with `m' ≤ F m' m`, as in
`canonical_of_feeder_descent`), either UpCell holds (a cell of the feeder row itself at a column `≤ w`), or some
proper B-iterate `b^[i+1] m'` of the feeder has a cell at a column `z ≤ w` above it. -/
theorem feeder_cell_dichotomy {k H : ℕ} (hn : NoChain α (H + 1)) {m' m y : α} (hm' : m' ∈ Rk F k)
    (hm'k : height H m' = k) (hm'm : m' ≤ m) (hfeed : m' ≤ F m' m) (hlo : F m' m ≤ m') (hy : m ⊔ F m y = y)
    (hmw : ¬ m ≤ F m y) (hwm : ¬ F m y ≤ m) :
    UpCell F H k m ∨ ∃ i z, z ≤ F m y ∧ (b F)^[i + 1] m' < z ∧
      (F ((b F)^[i + 1] m') z ≤ (b F)^[i + 1] m' ∨ z ≤ F ((b F)^[i + 1] m') z) := by
  have hmy : m ≤ y := le_sup_left.trans hy.le
  have hpre : F m' m' ≤ m' := ((F m').mono hm'm).trans hlo
  have hm'w : m' ≤ F m y := hfeed.trans (((F m').mono hmy).trans ((F.mono hm'm) y))
  have hlt : m' < F m y := lt_of_le_of_ne hm'w fun e => hwm (e ▸ hm'm)
  obtain ⟨i, z, hz, hrz, hc⟩ := cellState_cell hn _ le_rfl ⟨hpre, hlt, feeder_le_side hm'm hy⟩
  rcases i with _ | i
  · exact Or.inl ⟨m', hm', hm'k, z, hrz, fun h => hmw (h.trans hz), hc⟩
  · exact Or.inr ⟨i, z, hz, hrz, hc⟩

/-- **A depth-one lower cell with a new column is a feeder sibling.** With `OHAt` below `j + 1`, `R_{j+2}` tight,
the feeder's source `r = b m' ∈ R_{j+1}` of height `j + 1`, and a lower cell `F r z ≤ r` at a column `z > r` that
is new at stage `j + 2`: then `z ∈ R_{j+2}`, `h(z) = j + 2`, `b z = r = b m'` and `F r z = r`. -/
theorem depthOne_lowerCell_sibling {j H : ℕ} (IH : ∀ H' < j + 1, OHAt.{u} H') (hn : NoChain α (H + 1))
    (hk : ∀ z ∈ Rk F (j + 2), height H z ≤ j + 2) {r z : α} (hr : r ∈ Rk F (j + 1)) (hrh : height H r = j + 1)
    (hrz : r < z) (hL : F r z ≤ r) (hznew : z ∉ Rk F (j + 1)) :
    z ∈ Rk F (j + 2) ∧ height H z = j + 2 ∧ b F z = r ∧ F r z = r := by
  have hzR := lowerExit_mem hr hL
  have := height_strictMono hn hrz; have := hk z hzR
  have hzh : height H z = j + 2 := by omega
  obtain ⟨h1, h2⟩ := sibling_of_shadow IH hn hzh hznew hrh hrz hL
  exact ⟨hzR, hzh, h1, h2⟩

/-- **Depth-one lift, comparable case.** With `OHAt` below `j + 1` and `R_{j+2}` tight: let `q ∈ R_{j+1}` have height
`j + 1` (the feeder's source at stage `k = j + 2`), and let `z = F q u` be a shadow of a column `u` with `m ≰ u`, new at
stage `j + 2`, carrying a lower cell `F q z ≤ q` with `q < z`. If some column of `(z, u]` is comparable with its
row-`z` value, then UpCell holds at stage `j + 2`, witnessed by `z` (a same-source sibling of the feeder). -/
theorem depthOne_shadow_upCell {j H : ℕ} (IH : ∀ H' < j + 1, OHAt.{u} H') (hn : NoChain α (H + 1))
    (hk : ∀ z ∈ Rk F (j + 2), height H z ≤ j + 2) {m q z u : α} (hq : q ∈ Rk F (j + 1))
    (hqh : height H q = j + 1) (hqz : q < z) (hL : F q z ≤ q) (hznew : z ∉ Rk F (j + 1)) (hqu : F q u = z)
    (hmu : ¬ m ≤ u) (hcase : ∃ y, z < y ∧ y ≤ u ∧ (F z y ≤ y ∨ y ≤ F z y)) : UpCell F H (j + 2) m := by
  obtain ⟨hzR, hzh, -, hqzq⟩ := depthOne_lowerCell_sibling IH hn hk hq hqh hqz hL hznew
  have hcov : q ⋖ z := covBy_of_height hn hqz (by omega)
  exact siblingShadow_upCell hn hk hq hzR hzh hcov hqzq hqu hmu hcase

/-! ### Climbing through sibling shadows (§34.3z¹⁸²) -/

/-- **Row descent with shadow tracking.** As `row_cell_of_above`, and moreover the cell column `z` is the starting
column `u` itself or a row value `z = F x u'` of a row-pre-fixed column `u' ∈ (x, u]`. -/
theorem row_cell_of_above_shadow {H : ℕ} (hn : NoChain α (H + 1)) {x v : α}
    (habove : ∀ u, x < u → u ≤ v → F x u ≤ u → x ≤ F x u) :
    ∀ (n : ℕ) {u : α}, height H u ≤ n → x < u → u ≤ v → F x u ≤ u →
      ∃ z, x < z ∧ z ≤ u ∧ (F x z ≤ x ∨ z ≤ F x z) ∧
        (z = u ∨ ∃ u', z = F x u' ∧ x < u' ∧ u' ≤ u ∧ F x u' ≤ u')
  | 0, u, hu, hxu, _, _ => by have := height_strictMono hn hxu; omega
  | n + 1, u, hu, hxu, huv, hFu => by
      by_cases h1 : F x u ≤ x
      · exact ⟨u, hxu, le_rfl, Or.inl h1, Or.inl rfl⟩
      by_cases h2 : u ≤ F x u
      · exact ⟨u, hxu, le_rfl, Or.inr h2, Or.inl rfl⟩
      have hxg : x < F x u := lt_of_le_not_ge (habove u hxu huv hFu) h1
      have hgu : F x u < u := lt_of_le_not_ge hFu h2
      have := height_strictMono hn hgu
      obtain ⟨z, hz1, hz2, hz3, hz4⟩ :=
        row_cell_of_above_shadow hn habove n (by omega) hxg (hgu.le.trans huv) ((F x).mono hFu)
      refine ⟨z, hz1, hz2.trans hgu.le, hz3, Or.inr ?_⟩
      rcases hz4 with e | ⟨u', e, h1', h2', h3'⟩
      · exact ⟨u, e, hxu, le_rfl, hFu⟩
      · exact ⟨u', e, h1', h2'.trans hgu.le, h3'⟩

/-- **The climb step.** A sibling-shadow configuration at stage `j + 1` (`p ∈ R_j` of height `j`, a top `c ∈ R_{j+1}`
of height `j + 1`, `p ⋖ c`, `F p c = p`, `F p u = c`) with a row-`c` pre-fixed column `v ∈ (c, u]` yields a cell of
the row `c` at some `y ∈ (c, v]`, where `y = v` or `y = F c u'` for a row-`c` pre-fixed column `u' ∈ (c, v]`. -/
theorem climb_step {j H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    {p c u v : α} (hp : p ∈ Rk F j) (hck : height H c = j + 1) (hcov : p ⋖ c) (hpc : F p c = p)
    (hpu : F p u = c) (hcv : c < v) (hvu : v ≤ u) (hFv : F c v ≤ v) :
    ∃ y, c < y ∧ y ≤ v ∧ (F c y ≤ c ∨ y ≤ F c y) ∧ (y = v ∨ ∃ u', y = F c u' ∧ c < u' ∧ u' ≤ v ∧ F c u' ≤ u') :=
  row_cell_of_above_shadow hn (fun z hcz hzv _ =>
      (source_row_const hn hk hp hck hcov hpc hpu hcz (hzv.trans hvu)).symm.le.trans ((F.mono hcov.le) z))
    H (height_le _) hcv le_rfl hFv

/-- **The next configuration.** If the climb step yields a *lower* cell at a shadow `y = F c u'` that is new at
stage `j + 2` (with `OHAt` below `j + 1` and `R_{j+2}` tight), then `(c, y, u')` is a sibling-shadow configuration
one stage higher: `y ∈ R_{j+2}`, `h(y) = j + 2`, `c ⋖ y`, `F c y = c`, `F c u' = y`. -/
theorem climb_next_config {j H : ℕ} (IH : ∀ H' < j + 1, OHAt.{u} H') (hn : NoChain α (H + 1))
    (hk2 : ∀ z ∈ Rk F (j + 2), height H z ≤ j + 2) {c y u' : α} (hc : c ∈ Rk F (j + 1))
    (hck : height H c = j + 1) (hcy : c < y) (hL : F c y ≤ c) (hynew : y ∉ Rk F (j + 1)) (hy : y = F c u') :
    y ∈ Rk F (j + 2) ∧ height H y = j + 2 ∧ c ⋖ y ∧ F c y = c ∧ F c u' = y := by
  obtain ⟨hyR, hyh, -, hcyc⟩ := depthOne_lowerCell_sibling IH hn hk2 hc hck hcy hL hynew
  exact ⟨hyR, hyh, covBy_of_height hn hcy (by omega), hcyc, hy.symm⟩

/-! ### TopFibre: a stage-`k` sibling-shadow configuration with a comparable fibre column (§34.3z¹⁸³) -/

/-- **TopFibre** at stage `j + 1`: a height-`j` row `p ∈ R_j` below a height-`(j+1)` top `c ∈ R_{j+1}` with
`F p c = p`, a column `v` of the off-target shadow fibre (`F p v = c`, `m ≰ v`), and a column `y ∈ (c, v]` comparable
with its row-`c` value. -/
def TopFibre (F : α →o α →o α) (H j : ℕ) (m : α) : Prop :=
  ∃ p c v y, p ∈ Rk F j ∧ height H p = j ∧ c ∈ Rk F (j + 1) ∧ height H c = j + 1 ∧ p < c ∧ F p c = p ∧
    F p v = c ∧ ¬ m ≤ v ∧ c < y ∧ y ≤ v ∧ (F c y ≤ y ∨ y ≤ F c y)

/-- **TopFibre gives UpCell** (`siblingShadow_upCell`; the cover `p ⋖ c` comes from the heights). -/
theorem upCell_of_topFibre {j H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    {m : α} (h : TopFibre F H j m) : UpCell F H (j + 1) m := by
  obtain ⟨p, c, v, y, hp, hph, hc, hch, hpc, hpcp, hpv, hmv, hcy, hyv, hcell⟩ := h
  exact siblingShadow_upCell hn hk hp hc hch (covBy_of_height hn hpc (by omega)) hpcp hpv hmv ⟨y, hcy, hyv, hcell⟩

/-- **SingletonLower from TopFibre.** If in every uniqueness-free no-cell singleton configuration at stage `k`
either UpCell holds or (`k = j + 1` and) TopFibre holds at `j`, then `SingletonLower F H`. -/
theorem singletonLower_of_topFibre {H : ℕ} (hn : NoChain α (H + 1))
    (htf : ∀ k, (⊤ : α) ∉ Rk F (k + 2) → (∀ z ∈ Rk F k, height H z ≤ k) →
      (∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) → ∀ m, m ∈ Rk F (k + 1) → height H m = k + 1 → m ∉ Rk F k →
      ∀ m' ∈ Rk F k, height H m' = k → m' < m → F m' m ≤ m' →
      (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) → UpCell F H k m ∨ ∃ j, k = j + 1 ∧ TopFibre F H j m) :
    SingletonLower F H := by
  refine singletonLower_of_upCell hn fun k htop hk hall m hm hmk hnew m' hm' hm'k hlt hlo hno => ?_
  rcases htf k htop hk hall m hm hmk hnew m' hm' hm'k hlt hlo hno with h | ⟨j, rfl, h⟩
  · exact h
  · exact upCell_of_topFibre hn hk h

/-! ### The fibre join (§34.3z¹⁸⁴) -/

/-- The off-target shadow fibre of the configuration `(p, c)`. -/
def shadowFibre (F : α →o α →o α) (m p c : α) : Set α := {v | c < v ∧ ¬ m ≤ v ∧ F p v = c}

/-- FibreTop at a fixed configuration `(p, c)`: some fibre interval `(c, v]` has a column comparable with its
row-`c` value. -/
def FibreTopAt (F : α →o α →o α) (m p c : α) : Prop :=
  ∃ v ∈ shadowFibre F m p c, ∃ y, c < y ∧ y ≤ v ∧ (F c y ≤ y ∨ y ≤ F c y)

/-- **A stable fibre join reduces FibreTop to one interval.** If `U = ⋁ S(p, c; m)` is itself in the fibre
(`F p U = c`, `m ≰ U`), then FibreTop at `(p, c)` holds iff `(c, U]` contains a comparable column. -/
theorem fibreTopAt_iff_join {m p c : α} (hU : F p (sSup (shadowFibre F m p c)) = c)
    (hmU : ¬ m ≤ sSup (shadowFibre F m p c)) :
    FibreTopAt F m p c ↔
      ∃ y, c < y ∧ y ≤ sSup (shadowFibre F m p c) ∧ (F c y ≤ y ∨ y ≤ F c y) := by
  constructor
  · rintro ⟨v, hv, y, hcy, hyv, hc⟩
    exact ⟨y, hcy, hyv.trans (le_sSup hv), hc⟩
  · rintro ⟨y, hcy, hyU, hc⟩
    exact ⟨_, ⟨lt_of_lt_of_le hcy hyU, hmU, hU⟩, y, hcy, hyU, hc⟩

/-- `TopFibre` is FibreTop at some stage configuration. -/
theorem topFibre_iff {j H : ℕ} {m : α} :
    TopFibre F H j m ↔ ∃ p c, p ∈ Rk F j ∧ height H p = j ∧ c ∈ Rk F (j + 1) ∧ height H c = j + 1 ∧ p < c ∧
      F p c = p ∧ FibreTopAt F m p c := by
  constructor
  · rintro ⟨p, c, v, y, hp, hph, hc, hch, hpc, hpcp, hpv, hmv, hcy, hyv, hcell⟩
    exact ⟨p, c, hp, hph, hc, hch, hpc, hpcp, v, ⟨lt_of_lt_of_le hcy hyv, hmv, hpv⟩, y, hcy, hyv, hcell⟩
  · rintro ⟨p, c, hp, hph, hc, hch, hpc, hpcp, v, ⟨-, hmv, hpv⟩, y, hcy, hyv, hcell⟩
    exact ⟨p, c, v, y, hp, hph, hc, hch, hpc, hpcp, hpv, hmv, hcy, hyv, hcell⟩

/-! ### The descent-seeded configuration graph (§34.3z¹⁸⁵) -/

/-- A sibling-shadow **configuration** `(p, c)` at stage `j + 1`. -/
def SibConfig (F : α →o α →o α) (H j : ℕ) (m p c : α) : Prop :=
  p ∈ Rk F j ∧ height H p = j ∧ c ∈ Rk F (j + 1) ∧ c ∉ Rk F j ∧ height H c = j + 1 ∧ p < c ∧ F p c = p ∧
    (shadowFibre F m p c).Nonempty

/-- A **tagged edge** `(p, c) → (c, y)`: a fibre column `v`, a row-`c` pre-fixed column `v' ∈ (c, v]`, and the cell
`y ≤ v'` that the shadow-tracking descent extracts: `y = v'` (endpoint) or `y = F c u'` (row-value shadow), a lower
cell of the row `c`, with `(c, y)` again a configuration. -/
def SeedEdge (F : α →o α →o α) (H j : ℕ) (m p c y : α) : Prop :=
  SibConfig F H j m p c ∧ SibConfig F H (j + 1) m c y ∧
    ∃ v ∈ shadowFibre F m p c, ∃ v', c < v' ∧ v' ≤ v ∧ F c v' ≤ v' ∧ y ≤ v' ∧ F c y ≤ c ∧
      (y = v' ∨ ∃ u', y = F c u' ∧ c < u' ∧ u' ≤ v' ∧ F c u' ≤ u')

/-- **Root-relative reachability** along tagged edges (each edge raises the stage by one). -/
inductive SeedReach (F : α →o α →o α) (H : ℕ) (m : α) (j₀ : ℕ) (p₀ c₀ : α) : ℕ → α → α → Prop
  | root : SeedReach F H m j₀ p₀ c₀ j₀ p₀ c₀
  | step {j p c y} : SeedReach F H m j₀ p₀ c₀ j p c → SeedEdge F H j m p c y →
      SeedReach F H m j₀ p₀ c₀ (j + 1) c y

theorem seedReach_stage {j₀ : ℕ} {p₀ c₀ : α} {H : ℕ} {m : α} {j : ℕ} {p c : α}
    (h : SeedReach F H m j₀ p₀ c₀ j p c) : j₀ ≤ j := by
  induction h with
  | root => exact le_rfl
  | step _ _ ih => omega

/-- **Edges exist where the climb extracts a new lower cell with a nonempty fibre.** With `OHAt` below `j + 1`
and `R_{j+1}`, `R_{j+2}` tight: given a configuration `(p, c)` at stage `j + 1`, a fibre column `v`, a row-`c`
pre-fixed `v' ∈ (c, v]` and the `climb_step` output `y` — a lower cell, new at stage `j + 2`, with a nonempty fibre
`S(c, y; m)` — the edge `(p, c) → (c, y)` holds. -/
theorem seedEdge_of_climb {j H : ℕ} (IH : ∀ H' < j + 1, OHAt.{u} H') (hn : NoChain α (H + 1))
    (hk2 : ∀ z ∈ Rk F (j + 2), height H z ≤ j + 2) {m p c v v' y : α} (hC : SibConfig F H j m p c)
    (hv : v ∈ shadowFibre F m p c) (hcv' : c < v') (hv'v : v' ≤ v) (hFv' : F c v' ≤ v') (hcy : c < y)
    (hyv' : y ≤ v') (hL : F c y ≤ c) (horig : y = v' ∨ ∃ u', y = F c u' ∧ c < u' ∧ u' ≤ v' ∧ F c u' ≤ u')
    (hynew : y ∉ Rk F (j + 1)) (hfib : (shadowFibre F m c y).Nonempty) : SeedEdge F H j m p c y := by
  obtain ⟨hp, hph, hc, hcnew, hch, hpc, hpcp, hS⟩ := hC
  obtain ⟨hyR, hyh, -, hcyc⟩ := depthOne_lowerCell_sibling IH hn hk2 hc hch hcy hL hynew
  exact ⟨⟨hp, hph, hc, hcnew, hch, hpc, hpcp, hS⟩, ⟨hc, hch, hyR, hynew, hyh, hcy, hcyc, hfib⟩,
    v, hv, v', hcv', hv'v, hFv', hyv', hL, horig⟩

/-- **Shadow edges preserve anchoring.** If the edge's fibre column `v` lies below `w` and the cell is a row-value
shadow `y = F c u'` of a row-`c` pre-fixed `u' ∈ (c, v]`, then `u'` is a fibre column of the child `(c, y)` below
`w`. -/
theorem seedEdge_anchor {m c y v w u' : α} (hy : y = F c u') (hFu' : F c u' ≤ u') (hu'v : u' ≤ v)
    (hvw : v ≤ w) (hmv : ¬ m ≤ v) (hL : F c y ≤ c) (hcy : c < y) :
    u' ∈ shadowFibre F m c y ∧ u' ≤ w := by
  have hyu : y ≤ u' := hy ▸ hFu'
  have hne : y ≠ u' := fun e => by
    have h1 : F c y = y := by
      calc F c y = F c u' := by rw [e]
        _ = y := hy.symm
    exact absurd (h1.symm.le.trans hL) (not_le_of_gt hcy)
  exact ⟨⟨lt_of_le_of_ne hyu hne, fun h => hmv (h.trans hu'v), hy.symm⟩, hu'v.trans hvw⟩

/-- **The A-roots.** A depth-`≥ 1` *upper* final cell `z ≤ F r z` of a row `r ∈ R_j`, with `z` of height `j + 1` in a
tight `R_{j+1}`, is the row gfp: `z = a r` (`upper_branch_eq_a` after `F r z = z`). -/
theorem aRoot_eq_a {j H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    {r z : α} (hr : r ∈ Rk F j) (hzh : height H z = j + 1) (hU : z ≤ F r z) : z = a F r := by
  have hle : z ≤ a F r := le_a hU
  by_contra hne
  have := height_strictMono hn (lt_of_le_of_ne hle hne)
  have := hk _ (mem_succ_of_a hr le_rfl); omega

/-- **A stage-`k` configuration with FibreTop gives UpCell.** -/
theorem upCell_of_sibConfig_top {j H : ℕ} (hn : NoChain α (H + 1))
    (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1) {m p c : α} (hC : SibConfig F H j m p c)
    (hT : FibreTopAt F m p c) : UpCell F H (j + 1) m := by
  obtain ⟨hp, hph, hc, -, hch, hpc, hpcp, -⟩ := hC
  exact upCell_of_topFibre hn hk (topFibre_iff.2 ⟨p, c, hp, hph, hc, hch, hpc, hpcp, hT⟩)

/-! ### Mixed A/B transitions (§34.3z¹⁸⁶) -/

/-- **An A-edge** from a top `c` (stage `j + 1`): an *upper* cell `y ≤ F c y` at a column `y > c`, `m ≰ y`, which is
a new top of stage `j + 2`. -/
def AEdge (F : α →o α →o α) (H j : ℕ) (m c y : α) : Prop :=
  c ∈ Rk F (j + 1) ∧ height H c = j + 1 ∧ c < y ∧ y ≤ F c y ∧ ¬ m ≤ y ∧ y ∈ Rk F (j + 2) ∧ y ∉ Rk F (j + 1) ∧
    height H y = j + 2

/-- **The A-edge is the row gfp**: with `R_{j+2}` tight, an A-edge `c → y` has `y = a c` and `F c y = y`. -/
theorem aEdge_eq_a {j H : ℕ} (hn : NoChain α (H + 1)) (hk2 : ∀ z ∈ Rk F (j + 2), height H z ≤ j + 2)
    {m c y : α} (h : AEdge F H j m c y) : y = a F c ∧ F c y = y := by
  obtain ⟨hc, -, -, hU, -, -, -, hyh⟩ := h
  have e := aRoot_eq_a hn hk2 hc hyh hU
  exact ⟨e, by rw [e]; exact row_a c⟩

/-- **Upper cells of tops give A-edges.** If the top `c ∈ R_{j+1}` (height `j + 1`) has an upper cell `y ≤ F c y` at a
column `y > c` with `m ≰ y`, new at stage `j + 2`, in a tight `R_{j+2}`, then `c → y` is an A-edge. -/
theorem aEdge_of_upper {j H : ℕ} (hn : NoChain α (H + 1)) (hk2 : ∀ z ∈ Rk F (j + 2), height H z ≤ j + 2)
    {m c y : α} (hc : c ∈ Rk F (j + 1)) (hch : height H c = j + 1) (hcy : c < y) (hU : y ≤ F c y)
    (hmy : ¬ m ≤ y) (hynew : y ∉ Rk F (j + 1)) : AEdge F H j m c y := by
  have hyR : y ∈ Rk F (j + 2) := mem_succ_of_cell hc le_rfl (Or.inr hU)
  have := height_strictMono hn hcy; have := hk2 y hyR
  exact ⟨hc, hch, hcy, hU, hmy, hyR, hynew, by omega⟩

/-- **Mixed reachability** from a top `c₀` at stage `j₀ + 1`: along B-edges (`SeedEdge`, forgetting the source) and
A-edges. -/
inductive MixedReach (F : α →o α →o α) (H : ℕ) (m : α) (j₀ : ℕ) (c₀ : α) : ℕ → α → Prop
  | root : MixedReach F H m j₀ c₀ j₀ c₀
  | bstep {j p c y} : MixedReach F H m j₀ c₀ j c → SeedEdge F H j m p c y → MixedReach F H m j₀ c₀ (j + 1) y
  | astep {j c y} : MixedReach F H m j₀ c₀ j c → AEdge F H j m c y → MixedReach F H m j₀ c₀ (j + 1) y

theorem mixedReach_stage {H j₀ j : ℕ} {m c₀ c : α} (h : MixedReach F H m j₀ c₀ j c) : j₀ ≤ j := by
  induction h with
  | root => exact le_rfl
  | bstep _ _ ih => omega
  | astep _ _ ih => omega

/-- **A reachable top at stage `k` with an off-target upward cell is UpCell** (immediate from the definition; recorded
to fix the terminal condition of the mixed graph). -/
theorem upCell_of_mixedTop {j H : ℕ} {m c : α} (hc : c ∈ Rk F (j + 1)) (hch : height H c = j + 1)
    (hcell : ∃ z, c < z ∧ ¬ m ≤ z ∧ (F c z ≤ c ∨ z ≤ F c z)) : UpCell F H (j + 1) m := by
  obtain ⟨z, hcz, hmz, hz⟩ := hcell
  exact ⟨c, hc, hch, z, hcz, hmz, hz⟩

/-- **The source of a sibling configuration is an UpCell witness at its own stage**: `F p c = p` is a lower cell at the
column `c > p`, and `m ≰ c` because the fibre is nonempty (`c < v`, `m ≰ v`). -/
theorem upCell_of_sibConfig_src {j H : ℕ} {m p c : α} (hC : SibConfig F H j m p c) : UpCell F H j m := by
  obtain ⟨hp, hph, -, -, -, hpc, hpcp, v, hcv, hmv, -⟩ := hC
  exact ⟨p, hp, hph, c, hpc, fun hmc => hmv (hmc.trans hcv.le), Or.inl hpcp.le⟩

/-- The source of an A-edge is an UpCell witness at its stage. -/
theorem upCell_of_aEdge {j H : ℕ} {m c y : α} (h : AEdge F H j m c y) : UpCell F H (j + 1) m := by
  obtain ⟨hc, hch, hcy, hU, hmy, -⟩ := h
  exact ⟨c, hc, hch, y, hcy, hmy, Or.inr hU⟩

/-- **Top edges**: `c → y` when `(c, y)` is itself a sibling configuration (a B-cell out of `c`, with nonempty child
fibre), or an A-edge. No incoming source is required. -/
def TopEdge (F : α →o α →o α) (H j : ℕ) (m c y : α) : Prop := SibConfig F H (j + 1) m c y ∨ AEdge F H j m c y

inductive TopReach (F : α →o α →o α) (H : ℕ) (m : α) (j₀ : ℕ) (c₀ : α) : ℕ → α → Prop
  | root : TopReach F H m j₀ c₀ j₀ c₀
  | step {j c y} : TopReach F H m j₀ c₀ j c → TopEdge F H j m c y → TopReach F H m j₀ c₀ (j + 1) y

/-- The mixed graph embeds in the top graph (`SeedEdge p c y` contains `SibConfig c y`). -/
theorem topReach_of_mixedReach {H j₀ j : ℕ} {m c₀ c : α} (h : MixedReach F H m j₀ c₀ j c) :
    TopReach F H m j₀ c₀ j c := by
  induction h with
  | root => exact .root
  | bstep _ he ih => exact .step ih (Or.inl he.2.1)
  | astep _ he ih => exact .step ih (Or.inr he)

/-- **Any top with an outgoing top edge is an UpCell witness at its stage.** Hence the terminal condition of the top
graph at stage `k` is just "some reached stage-`k` top has an out-edge (or any upward cell away from `m`)". -/
theorem upCell_of_topEdge {j H : ℕ} {m c y : α} (h : TopEdge F H j m c y) : UpCell F H (j + 1) m :=
  h.elim upCell_of_sibConfig_src upCell_of_aEdge

/-- **Seeded step, B-edges only** (the statement refuted in §34.3z¹⁸⁶ by `seeded_deadend_min29.json`): every reachable
configuration strictly below stage `k` has a B-successor. -/
def SeededStepB (F : α →o α →o α) (H k : ℕ) (m : α) (j₀ : ℕ) (p₀ c₀ : α) : Prop :=
  ∀ j p c, SeedReach F H m j₀ p₀ c₀ j p c → j + 1 < k → ∃ y, SeedEdge F H j m p c y

/-- **Top-graph goal** (conjectural; 68/68 seeded roots below `k` in the sweep): the top graph from the seeded root
reaches a stage-`k` top that is an UpCell witness. -/
def TopGoal (F : α →o α →o α) (H k : ℕ) (m : α) (j₀ : ℕ) (c₀ : α) : Prop :=
  ∃ c, TopReach F H m j₀ c₀ (k - 1) c ∧ ∃ z, c < z ∧ ¬ m ≤ z ∧ (F c z ≤ c ∨ z ≤ F c z)

theorem topReach_stage {H j₀ j : ℕ} {m c₀ c : α} (h : TopReach F H m j₀ c₀ j c) : j₀ ≤ j := by
  induction h with
  | root => exact le_rfl
  | step _ _ ih => omega

/-- Reached tops are new tops at stage `j + 1` of height `j + 1` (for `j > j₀`, from the edge; the root by assumption). -/
theorem topReach_top {H j₀ j : ℕ} {m c₀ c : α} (h0 : c₀ ∈ Rk F (j₀ + 1) ∧ height H c₀ = j₀ + 1)
    (h : TopReach F H m j₀ c₀ j c) : c ∈ Rk F (j + 1) ∧ height H c = j + 1 := by
  cases h with
  | root => exact h0
  | step _ he =>
    rcases he with ⟨-, -, hy, -, hyh, -⟩ | ⟨-, -, -, -, -, hy, -, hyh⟩
    · exact ⟨hy, hyh⟩
    · exact ⟨hy, hyh⟩

/-- **TopGoal gives UpCell at stage `k`** (`k ≥ 1`). -/
theorem upCell_of_topGoal {H k j₀ : ℕ} {m c₀ : α} (hk : 1 ≤ k) (h0 : c₀ ∈ Rk F (j₀ + 1) ∧ height H c₀ = j₀ + 1)
    (h : TopGoal F H k m j₀ c₀) : UpCell F H k m := by
  obtain ⟨c, hr, z, hcz, hmz, hz⟩ := h
  obtain ⟨hc, hch⟩ := topReach_top h0 hr
  have e : k - 1 + 1 = k := by omega
  rw [e] at hc hch
  exact ⟨c, hc, hch, z, hcz, hmz, hz⟩

/-! ### Good tops and fork selection (§34.3z¹⁸⁷) -/

/-- The terminal condition: an upward cell away from `m`. -/
def UpAt (F : α →o α →o α) (m c : α) : Prop := ∃ z, c < z ∧ ¬ m ≤ z ∧ (F c z ≤ c ∨ z ≤ F c z)

/-- **Good tops** (index `j` = the top lies at stage `j + 1`): at index `k − 1` a top with an upward cell away from `m`;
below, a top with a top edge to a good top. -/
inductive Good (F : α →o α →o α) (H k : ℕ) (m : α) : ℕ → α → Prop
  | term {c} : UpAt F m c → Good F H k m (k - 1) c
  | step {j c y} : TopEdge F H j m c y → Good F H k m (j + 1) y → Good F H k m j c

/-- Prepending an edge to a top-graph path. -/
theorem topReach_cons {H j j' : ℕ} {m c y c' : α} (he : TopEdge F H j m c y)
    (h : TopReach F H m (j + 1) y j' c') : TopReach F H m j c j' c' := by
  induction h with
  | root => exact .step .root he
  | step _ he' ih => exact .step ih he'

/-- Good tops are exactly the roots of TopGoal (forward direction). -/
theorem topGoal_of_good {H k j : ℕ} {m c : α} (h : Good F H k m j c) : TopGoal F H k m j c := by
  induction h with
  | term hu => exact ⟨_, .root, hu⟩
  | step he _ ih =>
    obtain ⟨c', hr, hu⟩ := ih
    exact ⟨c', topReach_cons he hr, hu⟩

/-- Goodness propagates backwards along top-graph paths. -/
theorem good_of_topReach {H k j₀ j : ℕ} {m c₀ c : α} (hr : TopReach F H m j₀ c₀ j c) (hg : Good F H k m j c) :
    Good F H k m j₀ c₀ := by
  induction hr with
  | root => exact hg
  | step _ he ih => exact ih (.step he hg)

/-- **`Good ↔ TopGoal`.** -/
theorem good_iff_topGoal {H k j : ℕ} {m c : α} : Good F H k m j c ↔ TopGoal F H k m j c :=
  ⟨topGoal_of_good, fun ⟨_, hr, hu⟩ => good_of_topReach hr (.term hu)⟩

/-- A good top sits at index `≤ k − 1`. -/
theorem good_le {H k j : ℕ} {m c : α} (h : Good F H k m j c) : j ≤ k - 1 := by
  induction h with
  | term => exact le_rfl
  | step _ _ ih => omega

/-- **Nonempty-fork good child** (conjectural, §34.3z¹⁸⁷), relative to a root: every top reachable from `c₀` strictly
below index `k − 1` that has some top edge has a good child. -/
def NonemptyForkGoodChild (F : α →o α →o α) (H k : ℕ) (m : α) (j₀ : ℕ) (c₀ : α) : Prop :=
  ∀ j c, TopReach F H m j₀ c₀ j c → j < k - 1 → (∃ y, TopEdge F H j m c y) →
    ∃ y, TopEdge F H j m c y ∧ Good F H k m (j + 1) y

/-- **Fork selection gives TopGoal**: if the root (strictly below index `k − 1`) has a top edge and the fork principle
holds, the root is good. (Only the root instance of the principle is used.) -/
theorem topGoal_of_fork {H k j₀ : ℕ} {m c₀ : α} (hj : j₀ < k - 1) (hroot : ∃ y, TopEdge F H j₀ m c₀ y)
    (hfork : NonemptyForkGoodChild F H k m j₀ c₀) : TopGoal F H k m j₀ c₀ := by
  obtain ⟨y, he, hg⟩ := hfork j₀ c₀ .root hj hroot
  exact good_iff_topGoal.1 (.step he hg)

/-- **Inversion below the terminal index**: a good top strictly below `k − 1` has a good child. -/
theorem good_child_of_good {H k j : ℕ} {m c : α} (h : Good F H k m j c) (hj : j < k - 1) :
    ∃ y, TopEdge F H j m c y ∧ Good F H k m (j + 1) y := by
  cases h with
  | term => omega
  | step he hg => exact ⟨_, he, hg⟩

/-- **The fork principle, restated**: it says exactly that every reachable top strictly below `k − 1` with a top edge
is good. -/
theorem nonemptyForkGoodChild_iff {H k j₀ : ℕ} {m c₀ : α} :
    NonemptyForkGoodChild F H k m j₀ c₀ ↔
      ∀ j c, TopReach F H m j₀ c₀ j c → j < k - 1 → (∃ y, TopEdge F H j m c y) → Good F H k m j c := by
  constructor
  · intro hf j c hr hj he
    obtain ⟨y, hy, hg⟩ := hf j c hr hj he
    exact .step hy hg
  · intro hf j c hr hj he
    exact good_child_of_good (hf j c hr hj he) hj

/-- **The unrooted fork principle** (refuted in §34.3z¹⁸⁷ by `fork_allbad_new_min17.json`): every top strictly below
`k − 1` (in `R_{j+1}`, of height `j + 1`) with a top edge has a good child. -/
def ForkGoodChildAll (F : α →o α →o α) (H k : ℕ) (m : α) : Prop :=
  ∀ j c, c ∈ Rk F (j + 1) → height H c = j + 1 → j < k - 1 → (∃ y, TopEdge F H j m c y) →
    ∃ y, TopEdge F H j m c y ∧ Good F H k m (j + 1) y

/-- The unrooted principle implies every rooted one. Its refutation means a proof of the rooted principle must use
reachability from the root. -/
theorem nonemptyForkGoodChild_of_all {H k j₀ : ℕ} {m c₀ : α} (h0 : c₀ ∈ Rk F (j₀ + 1) ∧ height H c₀ = j₀ + 1)
    (h : ForkGoodChildAll F H k m) : NonemptyForkGoodChild F H k m j₀ c₀ := by
  intro j c hr hj he
  obtain ⟨hc, hch⟩ := topReach_top h0 hr
  exact h j c hc hch hj he

/-! ### Decomposition of the rooted fork principle (§34.3z¹⁸⁸) -/

/-- **An upper cell makes its column row-post-fixed**: `c ≤ y ≤ F c y` gives `y ≤ F y y`, so `y ≤ a y`. -/
theorem le_a_of_upper {c y : α} (hcy : c ≤ y) (hU : y ≤ F c y) : y ≤ a F y :=
  le_a (hU.trans ((F.mono hcy) y))

theorem aEdge_le_a {j H : ℕ} {m c y : α} (h : AEdge F H j m c y) : y ≤ a F y :=
  le_a_of_upper h.2.2.1.le h.2.2.2.1

/-- **A-orbit terminal step**: a strict A-iterate off `m` is an upward cell, `a y ≤ F y (a y)` (`row_a`). -/
theorem upAt_of_a {m y : α} (hy : y < a F y) (hm : ¬ m ≤ a F y) : UpAt F m y :=
  ⟨a F y, hy, hm, Or.inr (row_a y).ge⟩

/-- **A-orbit terminal lemma**: an A-child at the terminal index whose own A-iterate moves strictly and stays off `m`
is good. The two obstructions are exactly `a y = y` (stabilization) and `m ≤ a y`. -/
theorem good_aChild_term {H k : ℕ} {m c y : α} (h : AEdge F H (k - 2) m c y) (hy : y ≠ a F y) (hm : ¬ m ≤ a F y) :
    Good F H k m (k - 1) y :=
  .term (upAt_of_a (lt_of_le_of_ne (aEdge_le_a h) hy) hm)

/-- **AGood (rooted, conjectural)**: every A-child of a reachable top below the terminal index is good. -/
def AGoodFrom (F : α →o α →o α) (H k : ℕ) (m : α) (j₀ : ℕ) (c₀ : α) : Prop :=
  ∀ j c y, TopReach F H m j₀ c₀ j c → j < k - 1 → AEdge F H j m c y → Good F H k m (j + 1) y

/-- **BOnlyGoodChild (rooted, conjectural)**: a reachable top below the terminal index with a B-child and no A-child
has a good B-child. -/
def BOnlyGoodChild (F : α →o α →o α) (H k : ℕ) (m : α) (j₀ : ℕ) (c₀ : α) : Prop :=
  ∀ j c, TopReach F H m j₀ c₀ j c → j < k - 1 → (∃ y, SibConfig F H (j + 1) m c y) →
    (¬ ∃ y, AEdge F H j m c y) → ∃ y, SibConfig F H (j + 1) m c y ∧ Good F H k m (j + 1) y

/-- **Assembly**: AGood and BOnlyGoodChild give the rooted fork principle. -/
theorem nonemptyForkGoodChild_of_split {H k j₀ : ℕ} {m c₀ : α} (hA : AGoodFrom F H k m j₀ c₀)
    (hB : BOnlyGoodChild F H k m j₀ c₀) : NonemptyForkGoodChild F H k m j₀ c₀ := by
  intro j c hr hj ⟨y, he⟩
  by_cases hAe : ∃ y, AEdge F H j m c y
  · obtain ⟨y', hy'⟩ := hAe
    exact ⟨y', Or.inr hy', hA j c y' hr hj hy'⟩
  · rcases he with hS | hA'
    · obtain ⟨y', hS', hg⟩ := hB j c hr hj ⟨y, hS⟩ hAe
      exact ⟨y', Or.inl hS', hg⟩
    · exact absurd ⟨y, hA'⟩ hAe

/-- **TopGoal from the split**: with a root edge strictly below the terminal index. -/
theorem topGoal_of_split {H k j₀ : ℕ} {m c₀ : α} (hj : j₀ < k - 1) (hroot : ∃ y, TopEdge F H j₀ m c₀ y)
    (hA : AGoodFrom F H k m j₀ c₀) (hB : BOnlyGoodChild F H k m j₀ c₀) : TopGoal F H k m j₀ c₀ :=
  topGoal_of_fork hj hroot (nonemptyForkGoodChild_of_split hA hB)

/-- Top edges strictly increase the order. -/
theorem topEdge_lt {H j : ℕ} {m c y : α} (h : TopEdge F H j m c y) : c < y := by
  rcases h with ⟨-, -, -, -, -, h, -⟩ | ⟨-, -, h, -⟩ <;> exact h

/-- **Root cone**: every top reachable from `c₀` lies above `c₀`. -/
theorem topReach_ge {H j₀ j : ℕ} {m c₀ c : α} (h : TopReach F H m j₀ c₀ j c) : c₀ ≤ c := by
  induction h with
  | root => exact le_rfl
  | step _ he ih => exact ih.trans (topEdge_lt he).le

/-- **ConeForkGood (conjectural)**: every top above the root `c₀` strictly below the terminal index with a top edge has
a good child. An order-theoretic replacement for reachability; all-bad forks in rooted models lie outside the cone
(§34.3z¹⁸⁸, 17/17). -/
def ConeForkGood (F : α →o α →o α) (H k : ℕ) (m : α) (c₀ : α) : Prop :=
  ∀ j c, c₀ ≤ c → c ∈ Rk F (j + 1) → height H c = j + 1 → j < k - 1 → (∃ y, TopEdge F H j m c y) →
    ∃ y, TopEdge F H j m c y ∧ Good F H k m (j + 1) y

/-- **ConeForkGood gives the rooted fork principle** (reachable tops lie in the root cone, `topReach_ge`). -/
theorem nonemptyForkGoodChild_of_cone {H k j₀ : ℕ} {m c₀ : α} (h0 : c₀ ∈ Rk F (j₀ + 1) ∧ height H c₀ = j₀ + 1)
    (h : ConeForkGood F H k m c₀) : NonemptyForkGoodChild F H k m j₀ c₀ := by
  intro j c hr hj he
  obtain ⟨hc, hch⟩ := topReach_top h0 hr
  exact h j c (topReach_ge hr) hc hch hj he

/-- **Early columns contradict lower-stage tightness**: an element of `R_j` of height `j + 1` makes `R_j` non-tight.
The `htf` hypotheses of `singletonLower_of_topFibre` give tightness only at `R_k` and `R_{k+1}`, so the early-column
case (`z ∈ R_{h(z) − 1}`) is genuine there. -/
theorem not_tight_of_early {H j : ℕ} {z : α} (hz : z ∈ Rk F j) (hzh : height H z = j + 1) :
    ¬ ∀ x ∈ Rk F j, height H x ≤ j := fun ht => by have := ht z hz; omega

/-! ### The fibre as a whole (§34.3z¹⁸⁹) -/

/-- **The off-target fibre is down-closed above `c`** (from `source_row_const`): with `p ∈ R_j`, `p < c`, `h(p) = j`,
`h(c) = j + 1`, `F p c = p` and `R_{j+1}` tight, `v ∈ S(p, c; m)` and `c < y ≤ v` give `y ∈ S(p, c; m)`. -/
theorem shadowFibre_downClosed {j H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    {m p c v y : α} (hp : p ∈ Rk F j) (hph : height H p = j) (hch : height H c = j + 1) (hpc : p < c)
    (hpcp : F p c = p) (hv : v ∈ shadowFibre F m p c) (hcy : c < y) (hyv : y ≤ v) : y ∈ shadowFibre F m p c :=
  ⟨hcy, fun hmy => hv.2.1 (hmy.trans hyv),
    source_row_const hn hk hp hch (covBy_of_height hn hpc (by omega)) hpcp hv.2.2 hcy hyv⟩

/-- **FibreTop is a property of the fibre itself**: under the same hypotheses, `FibreTopAt` holds iff some fibre
column is comparable with its row-`c` value. -/
theorem fibreTopAt_iff_mem {j H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    {m p c : α} (hp : p ∈ Rk F j) (hph : height H p = j) (hch : height H c = j + 1) (hpc : p < c)
    (hpcp : F p c = p) :
    FibreTopAt F m p c ↔ ∃ y ∈ shadowFibre F m p c, F c y ≤ y ∨ y ≤ F c y := by
  constructor
  · rintro ⟨v, hv, y, hcy, hyv, hc⟩
    exact ⟨y, shadowFibre_downClosed hn hk hp hph hch hpc hpcp hv hcy hyv, hc⟩
  · rintro ⟨y, hy, hc⟩
    exact ⟨y, hy, y, hy.1, le_rfl, hc⟩

/-- **A stable fibre is an interval**: if `U = ⋁ S` lies in the fibre then `S(p, c; m) = (c, U]`. -/
theorem shadowFibre_eq_Ioc {j H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    {m p c : α} (hp : p ∈ Rk F j) (hph : height H p = j) (hch : height H c = j + 1) (hpc : p < c)
    (hpcp : F p c = p) (hU : sSup (shadowFibre F m p c) ∈ shadowFibre F m p c) :
    shadowFibre F m p c = Set.Ioc c (sSup (shadowFibre F m p c)) := by
  ext y
  refine ⟨fun hy => ⟨hy.1, le_sSup hy⟩, fun ⟨hcy, hyU⟩ => ?_⟩
  exact shadowFibre_downClosed hn hk hp hph hch hpc hpcp hU hcy hyU

/-- **Stable fibre-top** (per configuration; refuted in §34.3z¹⁸⁹ at `|L| = 8`): a stable fibre has a comparable
column. -/
def StableFibreTop (F : α →o α →o α) (H j : ℕ) (m : α) : Prop :=
  ∀ p c, p ∈ Rk F j → height H p = j → c ∈ Rk F (j + 1) → c ∉ Rk F j → height H c = j + 1 → p < c → F p c = p →
    sSup (shadowFibre F m p c) ∈ shadowFibre F m p c → FibreTopAt F m p c

/-- **Jump fibre-top** (per configuration; refuted in §34.3z¹⁸⁹ at `|L| = 11`, with `m ≰ ⋁S`): a fibre whose join leaves
it while staying off `m` has a comparable column. -/
def JumpFibreTop (F : α →o α →o α) (H j : ℕ) (m : α) : Prop :=
  ∀ p c, p ∈ Rk F j → height H p = j → c ∈ Rk F (j + 1) → c ∉ Rk F j → height H c = j + 1 → p < c → F p c = p →
    (shadowFibre F m p c).Nonempty → sSup (shadowFibre F m p c) ∉ shadowFibre F m p c →
      ¬ m ≤ sSup (shadowFibre F m p c) → FibreTopAt F m p c

/-! ### Bad fibres and the configuration family (§34.3z¹⁹⁰) -/

/-- **The `htf` alternative is UpCell.** With `R_k` tight, `UpCell ∨ (k = j + 1 ∧ TopFibre j)` is equivalent to UpCell
at stage `k`: TopFibre is only a route to UpCell (`upCell_of_topFibre`). So a proof of `htf` may assume ¬UpCell, which
is stronger than "every stage configuration is bad". -/
theorem htf_concl_iff {k H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F k, height H z ≤ k) {m : α} :
    (UpCell F H k m ∨ ∃ j, k = j + 1 ∧ TopFibre F H j m) ↔ UpCell F H k m := by
  refine ⟨fun h => ?_, Or.inl⟩
  rcases h with h | ⟨j, rfl, h⟩
  · exact h
  · exact upCell_of_topFibre hn hk h

/-- **¬UpCell makes every stage configuration bad**: if the top `c` of a configuration had a comparable fibre column,
it would be an UpCell witness. -/
theorem fibre_bad_of_not_upCell {j H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    {m p c : α} (hp : p ∈ Rk F j) (hph : height H p = j) (hc : c ∈ Rk F (j + 1)) (hch : height H c = j + 1)
    (hpc : p < c) (hpcp : F p c = p) (hno : ¬ UpCell F H (j + 1) m) :
    ∀ y ∈ shadowFibre F m p c, ¬ (F c y ≤ y ∨ y ≤ F c y) := fun y hy hcmp =>
  hno (upCell_of_topFibre hn hk ⟨p, c, y, y, hp, hph, hc, hch, hpc, hpcp, hy.2.2, hy.2.1, hy.1, le_rfl, hcmp⟩)

/-- **Row values of a bad fibre** (the brief's Step 1): for `y ∈ S(p, c; m)` with `p ≤ c` and `F c y ∥ y`, the row value
`t = F c y` lies strictly above `c`. -/
theorem badFibre_row {m p c y : α} (hpc : p ≤ c) (hy : y ∈ shadowFibre F m p c) (hbad : ¬ (F c y ≤ y ∨ y ≤ F c y)) :
    c < F c y ∧ ¬ F c y ≤ y ∧ ¬ y ≤ F c y := by
  have hle : c ≤ F c y := hy.2.2.symm.le.trans ((F.mono hpc) y)
  refine ⟨lt_of_le_of_ne hle fun e => hbad (Or.inl (e ▸ hy.1.le)), fun h => hbad (Or.inl h), fun h => hbad (Or.inr h)⟩

/-- **No cell of a stage-`j` row above stage `j + 1`**: a column of height `> j + 1` cannot carry a cell of a row of
`R_j` when `R_{j+1}` is tight. -/
theorem no_cell_above {j H : ℕ} (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1) {p t : α} (hp : p ∈ Rk F j)
    (ht : j + 1 < height H t) : ¬ (F p t ≤ p ∨ t ≤ F p t) := fun h => by
  have := hk t (mem_succ_of_cell hp le_rfl h); omega

/-- **The row-value transfer is non-degenerate**: for a configuration source `p` (`F p c = p`, `p ∈ R_j`) and a column
`t > c` with `h(c) = j + 1`, the source value `c′ = F p t` satisfies `p < c′` and `t ≰ c′`. (Whether `(p, c′)` is again
a configuration with `t` in its fibre is *not* forced: §34.3z¹⁹⁰.) -/
theorem rowShadow_source {j H : ℕ} (hn : NoChain α (H + 1)) (hk : ∀ z ∈ Rk F (j + 1), height H z ≤ j + 1)
    {p c t : α} (hp : p ∈ Rk F j) (hch : height H c = j + 1) (hpcp : F p c = p) (hct : c < t) :
    p < F p t ∧ ¬ t ≤ F p t := by
  have hh : j + 1 < height H t := by have := height_strictMono hn hct; omega
  have hno := no_cell_above hk hp hh
  have hle : p ≤ F p t := hpcp.symm.le.trans ((F p).mono hct.le)
  exact ⟨lt_of_le_of_ne hle fun e => hno (Or.inl e.symm.le), fun h => hno (Or.inr h)⟩

/-- **MinUpCell (conjectural)**: the `htf` alternative with only the hypotheses the §34.3z¹⁹⁰ ablation could not drop:
`R_{k+1}` tight, `m` new at stage `k + 1` of height `k + 1`, `m ≠ ⊤` (from `⊤ ∉ R_{k+2}`; needed: the 2-element lattice),
and no interval cell at `m`. (Dropping the last one is
refuted at `|L| = 5`, and at `|L| = 6` even with a nonempty, entirely bad configuration family.) -/
def MinUpCell (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k m, (∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) → m ∈ Rk F (k + 1) → height H m = k + 1 → m ∉ Rk F k → m ≠ ⊤ →
    (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) → UpCell F H k m

/-- **MinUpCell gives SingletonLower** (through `singletonLower_of_topFibre`; `m ≠ ⊤` from `⊤ ∉ R_{k+2}`; the other
`htf` hypotheses are unused). -/
theorem singletonLower_of_minUpCell {H : ℕ} (hn : NoChain α (H + 1)) (h : MinUpCell F H) : SingletonLower F H :=
  singletonLower_of_topFibre hn fun k htop _ hall m hm hmk hnew _ _ _ _ _ hno =>
    Or.inl (h k m hall hm hmk hnew (fun e => htop (e ▸ Rk_mono (Nat.le_succ _) hm)) hno)

/-- **MinUpCell at the first stage** (`k = 0`), proved: for `m ≠ ⊤` with no interval cell, the row `⊥` has a cell at a
column `z ∈ (⊥, w]`, `w = F m y*` (`colOrb_dichotomy`), hence off `m`. Only `m ≠ ⊤` and `¬IC(m)` are used: the row `⊥`
stays above itself (`⊥ ≤ F ⊥ u`), and `F ⊥ w ≤ F m w ≤ F m y* = w`, so `row_cell_of_above` applies below `w`. -/
theorem upCell_zero [WellFoundedLT α] {H : ℕ} (hn : NoChain α (H + 1)) {m : α} (ht : m ≠ ⊤)
    (hno : ¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) : UpCell F H 0 m := by
  rcases colOrb_dichotomy (F := F) ht with hc | ⟨n, -, hfix, -, hup, hlo⟩
  · exact absurd hc hno
  set y := colOrb F m n
  have hwy : F m y ≤ y := le_sup_right.trans hfix.le
  have hFw : F ⊥ (F m y) ≤ F m y := ((F.mono bot_le) (F m y)).trans ((F m).mono hwy)
  have hbw : ⊥ < F m y := bot_lt_iff_ne_bot.2 fun e => hlo (e ▸ bot_le)
  obtain ⟨z, hz, hzw, hcell⟩ :=
    row_cell_of_above hn (x := ⊥) (v := F m y) (fun _ _ _ _ => bot_le) H (height_le _) hbw le_rfl hFw
  exact ⟨⊥, show (⊥ : α) ∈ Set.Iic ⊥ from le_rfl, height_bot_eq_zero, z, hz, fun hmz => hup (hmz.trans hzw), hcell⟩

/-! ### Descent witnesses under the minimal hypotheses (§34.3z¹⁹¹) -/

/-- **MinDescentWitness (conjectural)**: under the MinUpCell hypotheses, a descent witness exists at stage `k`. No
counterexample (sweep 4 16, rank-3 closure lists, with the feeder, `⊤ ∉ R_{K+1}` and `R_k` tightness all dropped).
Its witness column cannot be anchored at `w = F m y*`: `v ≤ w`, `x < w` and `v ≤ y*` all fail (§34.3z¹⁹¹). -/
def MinDescentWitness (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k m, (∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) → m ∈ Rk F (k + 1) → height H m = k + 1 → m ∉ Rk F k → m ≠ ⊤ →
    (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) → DescentWitness F H k m

theorem minUpCell_of_minDescentWitness {H : ℕ} (hn : NoChain α (H + 1)) (h : MinDescentWitness F H) :
    MinUpCell F H := fun k m hall hm hmk hnew ht hno =>
  upCell_of_descentWitness hn (h k m hall hm hmk hnew ht hno)

/-- **An A-entered top above its source is diagonal post-fixed**: `q ≤ x ≤ F q x` gives `x ≤ F x x`; such a row stays
above itself on every column `u ≥ x`. (So the `nopostlayer` residue consists of B-entered tops and of A-entries
`x = a q` with `q ≰ x`.) -/
theorem diag_post_of_aEntry {q x : α} (hqx : q ≤ x) (hU : x ≤ F q x) : x ≤ F x x :=
  hU.trans ((F.mono hqx) x)

theorem above_of_diag_post {x u : α} (hx : x ≤ F x x) (hxu : x ≤ u) : x ≤ F x u :=
  hx.trans ((F x).mono hxu)

/-! ### Saturated shadows and the initial pair (§34.3z¹⁹²) -/

/-- **Saturated shadow** (the provable part of the brief's SaturatedShadow). Without UpCell, every candidate pair
`x < v`, `F x v ≤ v`, `m ≰ v` of a stage-`k` row `x` (height `k`) contains a *saturated drop* `q ∈ (x, v]`:
`q = x ⊔ F x q`, `F x q ≤ q`, `m ≰ q`, and `F x q ∥ x`. Proof: iterate `u ↦ x ⊔ F x u` (it stays pre-fixed, off `m`, and
strictly above `x`, since `x ⊔ F x u = x` would be a lower cell); heights strictly decrease until a fixed point, where an
upper cell is again excluded. Only `NoChain` is used — no tightness, no membership of the iterates in any stage.
(The brief's further claim `b q < x` is refuted, §34.3z¹⁹².) -/
theorem saturated_shadow {k H : ℕ} (hn : NoChain α (H + 1)) {m x v : α} (hnot : ¬ UpCell F H k m)
    (hx : x ∈ Rk F k) (hxk : height H x = k) :
    ∀ (n : ℕ) {u : α}, height H u ≤ n → x < u → u ≤ v → F x u ≤ u → ¬ m ≤ v →
      ∃ q, x < q ∧ q ≤ u ∧ ¬ m ≤ q ∧ F x q ≤ q ∧ x ⊔ F x q = q ∧ ¬ x ≤ F x q ∧ ¬ F x q ≤ x
  | 0, u, hu, hxu, _, _, _ => by have := height_strictMono hn hxu; omega
  | n + 1, u, hu, hxu, huv, hFu, hmv => by
      have hmu : ¬ m ≤ u := fun h => hmv (h.trans huv)
      have hlow : ¬ F x u ≤ x := fun h => hnot ⟨x, hx, hxk, u, hxu, hmu, Or.inl h⟩
      have hle : x ⊔ F x u ≤ u := sup_le hxu.le hFu
      by_cases he : x ⊔ F x u = u
      · refine ⟨u, hxu, le_rfl, hmu, hFu, he, fun h => ?_, hlow⟩
        exact hnot ⟨x, hx, hxk, u, hxu, hmu, Or.inr (he.symm.trans (sup_eq_right.2 h)).le⟩
      · have hlt : x ⊔ F x u < u := lt_of_le_of_ne hle he
        have hxlt : x < x ⊔ F x u := lt_of_le_of_ne le_sup_left fun e => hlow (le_sup_right.trans e.symm.le)
        have hpre : F x (x ⊔ F x u) ≤ x ⊔ F x u := ((F x).mono hle).trans le_sup_right
        have := height_strictMono hn hlt
        obtain ⟨q, h1, h2, h3⟩ := saturated_shadow hn hnot hx hxk n (by omega) hxlt (hlt.le.trans huv) hpre hmv
        exact ⟨q, h1, h2.trans hlt.le, h3⟩

/-- **Saturated source below the row** (the brief's conjectured second half; refuted at `|L| = 6` under ¬UpCell and at
`|L| = 7` for local drops in MinUpCell models, §34.3z¹⁹²). -/
def SatSourceBelow (F : α →o α →o α) (H k : ℕ) (m : α) : Prop :=
  ∀ x q, x ∈ Rk F k → height H x = k → x < q → ¬ m ≤ q → F x q ≤ q → x ⊔ F x q = q → ¬ x ≤ F x q → b F q < x

/-- **Initial pair from a row below `m ⊓ w`**: any row `x ≤ m` strictly below the column-orbit output `w = F m y*`
has `w` as a candidate column (`F x w ≤ w`, `m ≰ w`). In MinUpCell models `m ⊓ w` is a height-`k` row of `R_k` in 830
of 981 cases; the remaining cases need another row. -/
theorem initialPair_of_le {m x y : α} (hxm : x ≤ m) (hy : m ⊔ F m y = y) (hmw : ¬ m ≤ F m y) :
    F x (F m y) ≤ F m y ∧ ¬ m ≤ F m y :=
  ⟨feeder_le_side hxm hy, hmw⟩

/-! ### The join probe: re-entering ¬IC(m) after saturation (§34.3z¹⁹³) -/

/-- **Join probe.** Let `m ⊔ F m y = y` (a column-orbit fixed point, `w = F m y`), `x ≤ m`, and let `q ≤ w` be saturated
for the row `x` (`x ⊔ F x q = q`) with `q ≰ m`. Put `z` = the least fixed point of `Ψ t = m ⊔ F m t` above `m ⊔ q`
(`sInf` of the `Ψ`-pre-fixed points above `m ⊔ q`; no iteration or finiteness needed, since `m ⊔ q ≤ Ψ (m ⊔ q)`).
Then `m ⊔ q ≤ z ≤ y`, `z = m ⊔ F m z`, and with `r = F m z`: `F x q ≤ r ≤ w`, `q ≤ x ⊔ r`, and — using ¬IC(m) a second
time, at `z > m` — `r ∥ m`. -/
theorem joinProbe {m x q y : α} (hy : m ⊔ F m y = y) (hxm : x ≤ m) (hqw : q ≤ F m y) (hq : x ⊔ F x q = q)
    (hqm : ¬ q ≤ m) (hno : ¬ ∃ y', m < y' ∧ (F m y' ≤ m ∨ y' ≤ F m y')) :
    ∃ z, m ⊔ q ≤ z ∧ z ≤ y ∧ m ⊔ F m z = z ∧ ¬ F m z ≤ m ∧ ¬ m ≤ F m z ∧ F m z ≤ F m y ∧ F x q ≤ F m z ∧
      q ≤ x ⊔ F m z := by
  set Ψ : α → α := fun t => m ⊔ F m t
  have hΨ : Monotone Ψ := fun a b h => sup_le_sup_left ((F m).mono h) m
  set t0 := m ⊔ q
  have hwy : F m y ≤ y := le_sup_right.trans hy.le
  have hqy : q ≤ y := hqw.trans hwy
  have ht0y : t0 ≤ y := sup_le (le_sup_left.trans hy.le) hqy
  have hsx : F x q ≤ F m t0 := ((F.mono hxm) q).trans ((F m).mono le_sup_right)
  have ht0 : t0 ≤ Ψ t0 := by
    refine sup_le le_sup_left ?_
    rw [← hq]; exact sup_le (hxm.trans le_sup_left) (hsx.trans le_sup_right)
  set S := {t | t0 ≤ t ∧ Ψ t ≤ t}
  set z := sInf S
  have hyS : y ∈ S := ⟨ht0y, hy.le⟩
  have hzy : z ≤ y := sInf_le hyS
  have ht0z : t0 ≤ z := le_sInf fun t ht => ht.1
  have hΨz : Ψ z ≤ z := le_sInf fun t ht => (hΨ (sInf_le ht)).trans ht.2
  have hzΨ : z ≤ Ψ z := sInf_le ⟨ht0.trans (hΨ ht0z), hΨ hΨz⟩
  have hfix : m ⊔ F m z = z := le_antisymm hΨz hzΨ
  have hmz : m < z := lt_of_le_of_ne (le_sup_left.trans ht0z) fun e => hqm (le_sup_right.trans (ht0z.trans e.symm.le))
  have hr1 : ¬ F m z ≤ m := fun h => hno ⟨z, hmz, Or.inl h⟩
  have hr2 : ¬ m ≤ F m z := fun h => hno ⟨z, hmz, Or.inr (hfix.symm.trans (sup_eq_right.2 h)).le⟩
  have hsr : F x q ≤ F m z := hsx.trans ((F m).mono ht0z)
  refine ⟨z, ht0z, hzy, hfix, hr1, hr2, (F m).mono hzy, hsr, ?_⟩
  rw [← hq]; exact sup_le_sup_left hsr x

/-- **The A1/A2 split of the join probe** for the meet row `x = m ⊓ w`: either `x ≤ r` — then `m ⊓ r = x`, `x < r` and
`r` is a second pre-fixed column of the row `x` off `m` (A1) — or `m ⊓ r < x` (A2). -/
theorem joinProbe_split {m y z : α} (hzy : z ≤ y) (hfix : m ⊔ F m z = z) (hr1 : ¬ F m z ≤ m) :
    (m ⊓ F m y ≤ F m z ∧ m ⊓ F m z = m ⊓ F m y ∧ m ⊓ F m y < F m z ∧
        F (m ⊓ F m y) (F m z) ≤ F m z) ∨
      m ⊓ F m z < m ⊓ F m y := by
  have hrw : F m z ≤ F m y := (F m).mono hzy
  have hmeet : m ⊓ F m z ≤ m ⊓ F m y := inf_le_inf_left m hrw
  by_cases hA : m ⊓ F m y ≤ F m z
  · refine Or.inl ⟨hA, le_antisymm hmeet (le_inf inf_le_left hA), lt_of_le_of_ne hA fun e => hr1 (e ▸ inf_le_left), ?_⟩
    exact ((F.mono inf_le_left) (F m z)).trans ((F m).mono (le_sup_right.trans hfix.le))
  · exact Or.inr (lt_of_le_of_ne hmeet fun e => hA (e ▸ inf_le_right))

/-- **Saturation cannot pass below a saturated point**: if `q = x ⊔ F x q` and `q ≤ u`, then `q ≤ x ⊔ F x u`. So in case A1
(`x ≤ r`, hence `q ≤ r`) re-saturating the row `x` from `r` returns a saturated point `≥ q` (in the corpus: `q` itself). -/
theorem sat_iter_ge {x q u : α} (hq : x ⊔ F x q = q) (hqu : q ≤ u) : q ≤ x ⊔ F x u :=
  hq.symm.le.trans (sup_le_sup_left ((F x).mono hqu) x)

theorem joinProbe_A1_ge {m x q z : α} (hq : q ≤ x ⊔ F m z) (hxr : x ≤ F m z) : q ≤ F m z :=
  hq.trans (sup_le hxr le_rfl)

/-- **Only the meet row can use `w`**: a height-`k` row below `m` that lies below `w` (with `m ≰ w`, `h(m) = k + 1`) is
`m ⊓ w`. Hence outside the meet-row case no height-`k` row below `m` has `w` as a candidate column, and an initial pair must
use a row `x ≰ m` (in the corpus, 219 of 220 such models have no witness row below `m` at all). -/
theorem eq_meet_of_row_below {H k : ℕ} (hn : NoChain α (H + 1)) {m w x : α} (hxm : x ≤ m) (hxw : x ≤ w)
    (hxk : height H x = k) (hmk : height H m = k + 1) (hmw : ¬ m ≤ w) : x = m ⊓ w := by
  have hle : x ≤ m ⊓ w := le_inf hxm hxw
  have hlt : m ⊓ w < m := lt_of_le_of_ne inf_le_left fun e => hmw (e ▸ inf_le_right)
  have h1 := height_strictMono hn hlt
  by_contra hne
  have := height_strictMono hn (lt_of_le_of_ne hle hne); omega

/-! ### The A-response of top rows and the entry of `m` (§34.3z¹⁹⁴) -/

/-- **A-response classification.** With `R_{k+1}` tight, `h(m) = k + 1` and no UpCell, a height-`k` row `x ∈ R_k`
that ascends (`x ≤ a x`) has `a x = x` or `a x = m`: otherwise `F x (a x) = a x` is an upper cell at `a x > x`, which
must lie above `m`, and heights force `a x = m`. -/
theorem noUpCell_aResponse {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m x : α} (hmk : height H m = k + 1) (hnot : ¬ UpCell F H k m) (hx : x ∈ Rk F k) (hxk : height H x = k)
    (hxa : x ≤ a F x) : a F x = x ∨ a F x = m := by
  by_cases he : a F x = x
  · exact Or.inl he
  right
  have hlt : x < a F x := lt_of_le_of_ne hxa (Ne.symm he)
  have hma : m ≤ a F x := by
    by_contra hma
    exact hnot ⟨x, hx, hxk, a F x, hlt, hma, Or.inr (row_a x).ge⟩
  have hR := hall _ (mem_succ_of_a hx le_rfl)
  by_contra hne
  have := height_strictMono hn (lt_of_le_of_ne hma (Ne.symm hne)); omega

/-- In the stationary branch `a x = x` the row is diagonal fixed, so `b x ≤ x`. -/
theorem stationary_b_le {x : α} (h : a F x = x) : F x x = x ∧ b F x ≤ x := by
  have hx : F x x = x := by
    have := row_a (F := F) x; rw [h] at this; exact this
  exact ⟨hx, b_le hx.le⟩

/-- **Entry of `m`**: a new top `m ∈ R_{k+1} ∖ R_k` of height `k + 1` in a tight `R_{k+1}` is either A-entered as an
exact row gfp (`a q = m` for some `q ∈ R_k`), or B-entered (`b m ∈ R_k`) and not A-entered. -/
theorem entry_of_new {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m : α} (hm : m ∈ Rk F (k + 1)) (hmk : height H m = k + 1) (hnew : m ∉ Rk F k) :
    (∃ q ∈ Rk F k, a F q = m) ∨ (b F m ∈ Rk F k ∧ ¬ ∃ q ∈ Rk F k, m ≤ a F q) := by
  by_cases hA : ∃ q ∈ Rk F k, m ≤ a F q
  · obtain ⟨q, hq, hle⟩ := hA
    refine Or.inl ⟨q, hq, ?_⟩
    by_contra hne
    have := height_strictMono hn (lt_of_le_of_ne hle (Ne.symm hne))
    have := hall _ (mem_succ_of_a hq le_rfl); omega
  · rcases mem_succ_iff.1 hm with h | h | h
    · exact absurd h hnew
    · exact absurd h hA
    · exact Or.inr ⟨h, hA⟩

/-- **A diagonal post-fixed row with an initial pair is an UpCell row** (`above_of_diag_post` makes the pair a descent
witness). Applies to stationary rows (`a x = x`, so `F x x = x`) and to A-entered tops above their source
(`diag_post_of_aEntry`). Hence, without UpCell, no diagonal post-fixed height-`k` row has an off-`m` pre-fixed column. -/
theorem upCell_of_diagPost_pair {k H : ℕ} (hn : NoChain α (H + 1)) {m x v : α} (hx : x ∈ Rk F k)
    (hxk : height H x = k) (hd : x ≤ F x x) (hxv : x < v) (hFv : F x v ≤ v) (hmv : ¬ m ≤ v) : UpCell F H k m :=
  upCell_of_descentWitness hn ⟨x, hx, hxk, v, hxv, hFv, hmv, fun _ hxu _ _ => above_of_diag_post hd hxu.le⟩

/-- **Under ¬UpCell the A-response leaves three row types**: stationary rows (`a x = x`) without any initial pair,
target A-parents (`a x = m`), and non-ascending rows (`x ≰ a x`). -/
theorem noUpCell_rowTypes {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m x : α} (hmk : height H m = k + 1) (hnot : ¬ UpCell F H k m) (hx : x ∈ Rk F k) (hxk : height H x = k) :
    (a F x = x ∧ ¬ ∃ v, x < v ∧ F x v ≤ v ∧ ¬ m ≤ v) ∨ a F x = m ∨ ¬ x ≤ a F x := by
  by_cases hxa : x ≤ a F x
  · rcases noUpCell_aResponse hn hall hmk hnot hx hxk hxa with h | h
    · refine Or.inl ⟨h, fun ⟨v, hxv, hFv, hmv⟩ => hnot ?_⟩
      exact upCell_of_diagPost_pair hn hx hxk (stationary_b_le h).1.ge hxv hFv hmv
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr hxa)

/-! ### Non-ascending rows over the pure A-chain (§34.3z¹⁹⁵) -/

theorem pureA_le_succ : ∀ n, (a F)^[n] (⊥ : α) ≤ (a F)^[n + 1] ⊥
  | 0 => bot_le
  | n + 1 => by
      rw [Function.iterate_succ_apply' _ n, Function.iterate_succ_apply' _ (n + 1)]
      exact (a F).mono (pureA_le_succ n)

theorem pureA_mono : Monotone fun n => (a F)^[n] (⊥ : α) := monotone_nat_of_le_succ pureA_le_succ

/-- **An ascending row whose gfp is old is stationary** (no UpCell): `a x = m` is impossible when `a x ∈ R_k ∌ m`. -/
theorem noUpCell_ascending_old {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m x : α} (hmk : height H m = k + 1) (hnew : m ∉ Rk F k) (hnot : ¬ UpCell F H k m) (hx : x ∈ Rk F k)
    (hxk : height H x = k) (hxa : x ≤ a F x) (haR : a F x ∈ Rk F k) : a F x = x :=
  (noUpCell_aResponse hn hall hmk hnot hx hxk hxa).resolve_right fun h => hnew (h ▸ haR)

/-- **The pure A-chain jumps over height `k`.** Without UpCell, let a height-`k` row `x ∈ R_k` be non-ascending
(`x ≰ a x`) and lie below `c_i = a^i ⊥` with `i ≤ k` (the stage-`0` terminal case of `a_normal`). Then for some `j < i`:
`h(c_j) < k`, `c = c_{j+1}` is an *old* element of `R_k` of height `k + 1` with `m ≰ c`, `x < c`, the A-source `c_j` is
not below `x`, and `c = x ⊔ c_j`. (A chain element of height exactly `k` would be an ascending row with an old gfp,
hence stationary, freezing the chain below height `k + 1`; `c_j ≤ x` would make `(x, c)` an upper cell.) -/
theorem noUpCell_pureA_jump {k H i : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m x : α} (hmk : height H m = k + 1) (hnew : m ∉ Rk F k) (hnot : ¬ UpCell F H k m) (hx : x ∈ Rk F k)
    (hxk : height H x = k) (hik : i ≤ k) (hxc : x ≤ (a F)^[i] ⊥) (hna : ¬ x ≤ a F x) :
    ∃ j, j < i ∧ height H ((a F)^[j] (⊥ : α)) < k ∧ height H ((a F)^[j + 1] (⊥ : α)) = k + 1 ∧
      x < (a F)^[j + 1] ⊥ ∧ (a F)^[j + 1] ⊥ ∈ Rk F k ∧ ¬ m ≤ (a F)^[j + 1] ⊥ ∧ ¬ (a F)^[j] (⊥ : α) ≤ x ∧
      x ⊔ (a F)^[j] ⊥ = (a F)^[j + 1] ⊥ := by
  classical
  set c : ℕ → α := fun n => (a F)^[n] ⊥ with hc
  have hcR : ∀ n, n ≤ k → c n ∈ Rk F k := fun n hn' => by
    have := aIter_mem (F := F) (j := 0) (q := ⊥) (show (⊥ : α) ∈ Set.Iic ⊥ from le_rfl) n
    rw [zero_add] at this; exact Rk_mono hn' this
  have hh1 : ∀ n, n ≤ k → height H (c n) ≤ k + 1 := fun n hn' => hall _ (Rk_mono (Nat.le_succ k) (hcR n hn'))
  have hsucc : ∀ n, c (n + 1) = a F (c n) := fun n => Function.iterate_succ_apply' _ n _
  have hne : c i ≠ x := fun e => hna (by rw [← e, ← hsucc]; exact pureA_le_succ i)
  have hxlt : x < c i := lt_of_le_of_ne hxc (Ne.symm hne)
  have hPi : k + 1 ≤ height H (c i) := by have := height_strictMono hn hxlt; omega
  have hex : ∃ n, k + 1 ≤ height H (c n) := ⟨i, hPi⟩
  set n0 := Nat.find hex
  have hn0i : n0 ≤ i := Nat.find_min' hex hPi
  have hP0 : k + 1 ≤ height H (c n0) := Nat.find_spec hex
  have hn00 : n0 ≠ 0 := fun e => by
    have h0 : c 0 = ⊥ := rfl
    rw [e, h0, height_bot_eq_zero] at hP0; omega
  obtain ⟨j, hj⟩ : ∃ j, n0 = j + 1 := ⟨n0 - 1, by omega⟩
  have hnotj : ¬ k + 1 ≤ height H (c j) := Nat.find_min hex (by omega)
  have hcj1 : height H (c (j + 1)) = k + 1 := by
    have := hh1 (j + 1) (by omega); rw [← hj]; rw [← hj] at this; omega
  have hcji : c (j + 1) = c i := by
    have hle : c (j + 1) ≤ c i := pureA_mono (by omega)
    by_contra hne'
    have := height_strictMono hn (lt_of_le_of_ne hle hne'); have := hh1 i hik; omega
  have hjk : height H (c j) < k := by
    by_contra hge
    have hcjk : height H (c j) = k := by omega
    have hst := noUpCell_ascending_old hn hall hmk hnew hnot (hcR j (by omega)) hcjk
      ((pureA_le_succ j).trans (hsucc j).le) ((hsucc j) ▸ hcR (j + 1) (by omega))
    have : c (j + 1) = c j := (hsucc j).trans hst
    rw [this] at hcj1; omega
  have hxc' : x < c (j + 1) := hcji ▸ hxlt
  have hcRk : c (j + 1) ∈ Rk F k := hcR (j + 1) (by omega)
  have hmc : ¬ m ≤ c (j + 1) := fun hle => by
    rcases eq_or_lt_of_le hle with e | hlt
    · exact hnew (e ▸ hcRk)
    · have := height_strictMono hn hlt; omega
  have hrow : F (c j) (c (j + 1)) = c (j + 1) := by rw [hsucc]; exact row_a _
  have hcjx : ¬ c j ≤ x := fun hle =>
    hnot ⟨x, hx, hxk, c (j + 1), hxc', hmc, Or.inr (hrow.symm.le.trans ((F.mono hle) _))⟩
  have hjoin : x ⊔ c j = c (j + 1) := by
    have hle : x ⊔ c j ≤ c (j + 1) := sup_le hxc'.le ((pureA_le_succ j))
    have hlt : x < x ⊔ c j := lt_of_le_of_ne le_sup_left fun e => hcjx (le_sup_right.trans e.symm.le)
    by_contra hne'
    have := height_strictMono hn hlt; have := height_strictMono hn (lt_of_le_of_ne hle hne'); omega
  exact ⟨j, by omega, hjk, hcj1, hxc', hcRk, hmc, hcjx, hjoin⟩

/-- **An old diagonal post-fixed element of height `k + 1` is `⊤`**: `c ∈ R_k`, `h(c) = k + 1`, `c ≤ F c c` and `R_{k+1}`
tight force `c = ⊤` (otherwise `upc_of_le_diag` gives `c` an interval cell, which `old_top_no_cell` forbids). -/
theorem old_diagPost_eq_top [WellFoundedLT α] {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {c : α} (hc : c ∈ Rk F k) (hck : height H c = k + 1)
    (hd : c ≤ F c c) : c = ⊤ := by
  by_contra ht
  exact old_top_no_cell hn hall hc hck (upc_of_le_diag hd ht)

/-- **The pure A-chain stays below height `k + 1` up to stage `k`** whenever some element of `R_{k+1}` is new
(`m ∉ R_k`): an element `c = a^n ⊥` (`n ≤ k`) of height `k + 1` would satisfy `a c = c` (heights), so `F c c = c`, so
`c = ⊤` (`old_diagPost_eq_top`), putting `m` into `R_k`. (SAT check: R_K tight plus a new rank-`K` element already
exclude the jump on every Moore family on 4 points.) -/
theorem pureA_height_le [WellFoundedLT α] {k H n : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m : α} (hnew : m ∉ Rk F k) (hnk : n ≤ k) :
    height H ((a F)^[n] (⊥ : α)) ≤ k := by
  set c := (a F)^[n] (⊥ : α)
  have hcR : c ∈ Rk F k := by
    have := aIter_mem (F := F) (j := 0) (q := ⊥) (show (⊥ : α) ∈ Set.Iic ⊥ from le_rfl) n
    rw [zero_add] at this; exact Rk_mono hnk this
  have hcK := hall c (Rk_mono (Nat.le_succ k) hcR)
  by_contra hgt
  have hck : height H c = k + 1 := by omega
  have hca : c ≤ a F c := by
    have := pureA_le_succ (F := F) n; rwa [Function.iterate_succ_apply'] at this
  have hac : a F c = c := by
    by_contra hne
    have := height_strictMono hn (lt_of_le_of_ne hca (Ne.symm hne))
    have := hall _ (mem_succ_of_a hcR le_rfl); omega
  have hd : c ≤ F c c := by
    have := row_a (F := F) c; rw [hac] at this; exact this.ge
  have htop := old_diagPost_eq_top hn hall hcR hck hd
  exact hnew (Rk_down k le_top (htop ▸ hcR))

/-- **Stage-`0` terminal case closed.** Without UpCell, a non-ascending height-`k` row is never below `a^i ⊥`,
`i ≤ k` (`noUpCell_pureA_jump` would produce a chain element of height `k + 1` in `R_k`). Hence its A-normal terminal
source (`a_normal`) is B-entered at a positive stage. -/
theorem noUpCell_not_below_pureA [WellFoundedLT α] {k H i : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m x : α} (hmk : height H m = k + 1) (hnew : m ∉ Rk F k)
    (hnot : ¬ UpCell F H k m) (hx : x ∈ Rk F k) (hxk : height H x = k) (hik : i ≤ k) (hna : ¬ x ≤ a F x) :
    ¬ x ≤ (a F)^[i] ⊥ := fun hxc => by
  obtain ⟨j, hji, -, hj1, -⟩ := noUpCell_pureA_jump hn hall hmk hnew hnot hx hxk hik hxc hna
  have := pureA_height_le hn hall hnew (n := j + 1) (by omega); omega

/-- **The terminal source of a non-ascending row is B-entered** (no UpCell): in `a_normal`'s form
`x ≤ a^i q'` (`t + i ≤ k`, `ATerminal t q'`) the stage `t` is positive, `q'` is new at `t`, B-entered and not A-entered. -/
theorem noUpCell_nonAscending_terminal [WellFoundedLT α] {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m x : α} (hmk : height H m = k + 1) (hnew : m ∉ Rk F k)
    (hnot : ¬ UpCell F H k m) (hx : x ∈ Rk F k) (hxk : height H x = k) (hna : ¬ x ≤ a F x) :
    ∃ i t' q', t' + 1 + i ≤ k ∧ q' ∈ Rk F (t' + 1) ∧ x ≤ (a F)^[i] q' ∧ q' ∉ Rk F t' ∧ b F q' ∈ Rk F t' ∧
      ¬ ∃ r ∈ Rk F t', q' ≤ a F r := by
  obtain ⟨i, t, q', hti, hq', hle, ht⟩ := a_normal k x hx
  rcases ht with h0 | ⟨t', rfl, h1, h2, h3⟩
  · subst h0
    have hq : q' = ⊥ := le_bot_iff.1 hq'
    subst hq
    exact absurd hle (noUpCell_not_below_pureA hn hall hmk hnew hnot hx hxk (by omega) hna)
  · exact ⟨i, t', q', hti, hq', hle, h1, h2, h3⟩

/-! ### The B-source genealogy of a terminal source (§34.3z¹⁹⁶) -/

/-- **`terminalSource_new`**: the B-source of a terminal source new at stage `t' + 1` (`t' = t'' + 1 > 0`) is new at stage
`t'` (an instance of `source_new`: `b q' ∈ R_{t''}` would put `q'` into `R_{t'}`). -/
theorem terminalSource_new {t'' : ℕ} {q : α} (hq : q ∉ Rk F (t'' + 1)) : b F q ∉ Rk F t'' := source_new hq

/-- **`terminalBAncestry`.** A source `q` new at stage `s + 1` (`q ∈ R_{s+1} ∖ R_s`) has a B-source chain
`q_j = b^j q` with `q_j` new at stage `s + 1 − j` and not A-entered, for `j < d`, ending at `q_d` (`s = d + e`), new at
stage `e + 1`, which is either **A-entered** (`q_d ≤ a r`, `r ∈ R_e`) or **pure-B at the bottom stage** (`e = 0`,
`b q_d ∈ R_0`, i.e. `b q_d = ⊥`). The stage index strictly decreases along the chain. -/
theorem terminalBAncestry : ∀ (s : ℕ) (q : α), q ∈ Rk F (s + 1) → q ∉ Rk F s →
    ∃ d e, s = d + e ∧ (b F)^[d] q ∈ Rk F (e + 1) ∧ (b F)^[d] q ∉ Rk F e ∧
      (∀ j < d, ¬ ∃ r ∈ Rk F (s - j), (b F)^[j] q ≤ a F r) ∧
      ((∃ r ∈ Rk F e, (b F)^[d] q ≤ a F r) ∨ (e = 0 ∧ b F ((b F)^[d] q) ∈ Rk F 0))
  | 0, q, hq, hnew => by
      refine ⟨0, 0, rfl, hq, hnew, fun j hj => absurd hj (Nat.not_lt_zero _), ?_⟩
      rcases mem_succ_iff.1 hq with h | h | h
      · exact absurd h hnew
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩
  | s + 1, q, hq, hnew => by
      by_cases hA : ∃ r ∈ Rk F (s + 1), q ≤ a F r
      · exact ⟨0, s + 1, by omega, hq, hnew, fun j hj => absurd hj (Nat.not_lt_zero _), Or.inl hA⟩
      · have hb : b F q ∈ Rk F (s + 1) := by
          rcases mem_succ_iff.1 hq with h | h | h
          · exact absurd h hnew
          · exact absurd h hA
          · exact h
        obtain ⟨d, e, hse, h1, h2, h3, h4⟩ := terminalBAncestry s (b F q) hb (source_new hnew)
        refine ⟨d + 1, e, by omega, ?_, ?_, ?_, ?_⟩
        · rw [Function.iterate_succ_apply]; exact h1
        · rw [Function.iterate_succ_apply]; exact h2
        · intro j hj
          rcases j with _ | j
          · simpa using hA
          · rw [Function.iterate_succ_apply]
            have := h3 j (by omega)
            rwa [show s + 1 - (j + 1) = s - j by omega]
        · rw [Function.iterate_succ_apply]; exact h4

/-- **Ascending elements of `R_k` have height `≤ k`** (`R_{k+1}` tight, some `m ∉ R_k`): `c ≤ a c` and `h(c) = k + 1` give
`a c = c` (heights), so `F c c = c`, so `c = ⊤` (`old_diagPost_eq_top`) and `m ∈ R_k`. Generalizes `pureA_height_le`;
no UpCell hypothesis. -/
theorem ascending_height_le [WellFoundedLT α] {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m c : α} (hnew : m ∉ Rk F k) (hc : c ∈ Rk F k)
    (hca : c ≤ a F c) : height H c ≤ k := by
  have hcK := hall c (Rk_mono (Nat.le_succ k) hc)
  by_contra hgt
  have hck : height H c = k + 1 := by omega
  have hac : a F c = c := by
    by_contra hne
    have := height_strictMono hn (lt_of_le_of_ne hca (Ne.symm hne))
    have := hall _ (mem_succ_of_a hc le_rfl); omega
  have hd : c ≤ F c c := by
    have := row_a (F := F) c; rw [hac] at this; exact this.ge
  exact hnew (Rk_down k le_top (old_diagPost_eq_top hn hall hc hck hd ▸ hc))

/-- A height-`k` row below an ascending element of `R_k` *is* that element. -/
theorem row_below_ascending_eq [WellFoundedLT α] {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m c x : α} (hnew : m ∉ Rk F k) (hc : c ∈ Rk F k)
    (hca : c ≤ a F c) (hxk : height H x = k) (hxc : x ≤ c) : x = c := by
  have := ascending_height_le hn hall hnew hc hca
  by_contra hne
  have := height_strictMono hn (lt_of_le_of_ne hxc hne); omega

/-- `a` preserves ascent: `y ≤ a y` gives `a y ≤ a (a y)`. -/
theorem a_ascending {y : α} (h : y ≤ a F y) : a F y ≤ a F (a F y) := (a F).mono h

/-- **The A-chain above a non-ascending row is non-ascending throughout** (unconditional: no UpCell hypothesis). If a
non-ascending height-`k` row `x` lies below `a^i q'` with `q' ∈ R_t`, `t + i ≤ k`, then no `a^n q'` (`n ≤ i`) is
ascending; in particular the terminal source `q'` itself satisfies `q' ≰ a q'`. (An ascending `a^n q'` makes every later
iterate ascending, and `x` below the ascending `a^i q' ∈ R_k` would equal it.) This subsumes the stage-`0` case
(`⊥ ≤ a ⊥`). -/
theorem nonAscending_chain [WellFoundedLT α] {k H t i : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m x q : α} (hnew : m ∉ Rk F k) (hxk : height H x = k)
    (hna : ¬ x ≤ a F x) (hq : q ∈ Rk F t) (hti : t + i ≤ k) (hxc : x ≤ (a F)^[i] q) :
    ∀ n ≤ i, ¬ (a F)^[n] q ≤ a F ((a F)^[n] q) := by
  intro n hni hasc
  have hup : ∀ l, (a F)^[n + l] q ≤ a F ((a F)^[n + l] q) := by
    intro l
    induction l with
    | zero => simpa using hasc
    | succ l ih =>
      rw [show n + (l + 1) = (n + l) + 1 by omega, Function.iterate_succ_apply']
      exact a_ascending ih
  have hci := hup (i - n)
  rw [show n + (i - n) = i by omega] at hci
  have hR : (a F)^[i] q ∈ Rk F k := Rk_mono hti (aIter_mem hq i)
  have he := row_below_ascending_eq hn hall hnew hR hci hxk hxc
  exact hna (he ▸ hci)

/-- **The terminal source of a non-ascending row is non-ascending**, and B-entered at a positive stage under ¬UpCell
(combining `noUpCell_nonAscending_terminal` and `nonAscending_chain`). -/
theorem noUpCell_nonAscending_terminal' [WellFoundedLT α] {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m x : α} (hmk : height H m = k + 1) (hnew : m ∉ Rk F k)
    (hnot : ¬ UpCell F H k m) (hx : x ∈ Rk F k) (hxk : height H x = k) (hna : ¬ x ≤ a F x) :
    ∃ i t' q', t' + 1 + i ≤ k ∧ q' ∈ Rk F (t' + 1) ∧ x ≤ (a F)^[i] q' ∧ q' ∉ Rk F t' ∧ b F q' ∈ Rk F t' ∧
      (¬ ∃ r ∈ Rk F t', q' ≤ a F r) ∧ ∀ n ≤ i, ¬ (a F)^[n] q' ≤ a F ((a F)^[n] q') := by
  obtain ⟨i, t', q', h1, h2, h3, h4, h5, h6⟩ := noUpCell_nonAscending_terminal hn hall hmk hnew hnot hx hxk hna
  exact ⟨i, t', q', h1, h2, h3, h4, h5, h6, nonAscending_chain hn hall hnew hxk hna h2 h1 h3⟩

/-! ### The i = 0 case and the first A-entry (§34.3z¹⁹⁷) -/

/-- **The `i = 0` height dichotomy**: a height-`k` row below `q ∈ R_k` (with `R_{k+1}` tight) is either `q` itself (A1),
or `q` has height `k + 1` and covers it (A2). -/
theorem i0_dichotomy {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {q x : α}
    (hq : q ∈ Rk F k) (hxk : height H x = k) (hxq : x ≤ q) : x = q ∨ (height H q = k + 1 ∧ x ⋖ q) := by
  rcases eq_or_lt_of_le hxq with e | hlt
  · exact Or.inl e
  · have h1 := height_strictMono hn hlt; have h2 := hall q (Rk_mono (Nat.le_succ k) hq)
    exact Or.inr ⟨by omega, covBy_of_height hn hlt (by omega)⟩

/-- **The B-source of a new non-ascending element** is neither the element nor above it: `b y ≠ y` (else `F y y = y`
makes `y` ascending) and `y ≰ b y` (`R_t` is a down-set and `y ∉ R_t ∋ b y`). So `b y < y` or `b y ∥ y` (case A1). -/
theorem bSource_of_new_nonAscending {t : ℕ} {y : α} (hna : ¬ y ≤ a F y) (hnew : y ∉ Rk F t) (hb : b F y ∈ Rk F t) :
    b F y ≠ y ∧ ¬ y ≤ b F y := by
  refine ⟨fun e => hna (le_a ?_), fun h => hnew (Rk_down t h hb)⟩
  have := col_b (F := F) y; rw [e] at this; exact this.ge

/-- **Case A2** (`x ⋖ q`, `q` old of height `k + 1`, new at stage `t + 1 ≤ k`, `b q ∈ R_t`), without UpCell:
`b q ≠ x` (else `F x q = x` is a lower cell at `q`, and `m ≰ q` because `q ∈ R_k ∌ m`), and if `x < b q` then `b q` is
another old element of height `k + 1`, incomparable with `q`. -/
theorem noUpCell_i0_cover {k H t : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m x q : α} (hnew : m ∉ Rk F k) (hnot : ¬ UpCell F H k m) (hx : x ∈ Rk F k) (hxk : height H x = k) (hcov : x ⋖ q)
    (hq : q ∈ Rk F k) (hqt : q ∉ Rk F t) (hb : b F q ∈ Rk F t) (htk : t ≤ k) :
    b F q ≠ x ∧ (x < b F q → height H (b F q) = k + 1 ∧ ¬ b F q ≤ q ∧ ¬ q ≤ b F q) := by
  have hmq : ¬ m ≤ q := fun h => hnew (Rk_down k h hq)
  refine ⟨fun e => hnot ⟨x, hx, hxk, q, hcov.lt, hmq, Or.inl ?_⟩, fun hxb => ?_⟩
  · have := col_b (F := F) q; rw [e] at this; exact this.le
  · have hbR : b F q ∈ Rk F k := Rk_mono htk hb
    have h1 := height_strictMono hn hxb; have h2 := hall _ (Rk_mono (Nat.le_succ k) hbR)
    refine ⟨by omega, fun hle => ?_, fun hle => hqt (Rk_down t hle hb)⟩
    rcases eq_or_lt_of_le hle with e | hlt
    · exact hqt (e ▸ hb)
    · exact hcov.2 hxb hlt

/-- **Case A1 with a comparable B-source of height `k − 1`**: `b x ⋖ x` and `F (b x) x = b x`, so `(b x, x)` is a sibling
configuration top. (Its fibre is bad without UpCell only via `fibre_bad_of_not_upCell`, which needs `R_k` tight — not a
MinUpCell hypothesis.) -/
theorem i0_A1_cover {k H : ℕ} (hn : NoChain α (H + 1)) {x : α} (hxk : height H x = k) (hlt : b F x < x)
    (hbk : height H (b F x) + 1 = k) : b F x ⋖ x ∧ F (b F x) x = b F x :=
  ⟨covBy_of_height hn hlt (by omega), col_b x⟩

/-- **The first A-entry parent** (without UpCell): if `q ≤ a r` with `r ∈ R_e`, `q ∉ R_e`, `e + 1 ≤ k`, then `r` is not
an ascending height-`k` row (`noUpCell_ascending_old`: `a r ∈ R_k` would make it stationary, putting `q ≤ r` into `R_e`).
With `ascending_height_le`, an ascending first-A parent has height `< k`. -/
theorem noUpCell_firstA_parent {k H e : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m q r : α} (hmk : height H m = k + 1) (hnew : m ∉ Rk F k) (hnot : ¬ UpCell F H k m) (hr : r ∈ Rk F e)
    (hek : e + 1 ≤ k) (hqa : q ≤ a F r) (hqe : q ∉ Rk F e) (hrk : height H r = k) : ¬ r ≤ a F r := fun hra => by
  have hst := noUpCell_ascending_old hn hall hmk hnew hnot (Rk_mono (by omega) hr) hrk hra
    (Rk_mono hek (mem_succ_of_a hr le_rfl))
  exact hqe (Rk_down e (hst ▸ hqa) hr)

theorem noUpCell_firstA_parent_height [WellFoundedLT α] {k H e : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m q r : α} (hmk : height H m = k + 1) (hnew : m ∉ Rk F k)
    (hnot : ¬ UpCell F H k m) (hr : r ∈ Rk F e) (hek : e + 1 ≤ k) (hqa : q ≤ a F r) (hqe : q ∉ Rk F e)
    (hra : r ≤ a F r) : height H r < k := by
  have := ascending_height_le hn hall hnew (Rk_mono (by omega) hr) hra
  by_contra h
  exact noUpCell_firstA_parent hn hall hmk hnew hnot hr hek hqa hqe (by omega) hra

/-! ### Sibling configurations without `R_k` tightness (§34.3z¹⁹⁸) -/

/-- **The source row on the shadow interval, without tightness**: for `p ⋖ c`, `F p c = p`, `F p u = c` and `c < z ≤ u`,
either `F p z = c`, or `F p z = p` and the column `z` is *exceptional*: `z ∈ R_{j+1}` (a lower cell of the row
`p ∈ R_j`). (`source_row_const` excludes the second case using `R_{j+1}` tightness.) -/
theorem source_row_or {j : ℕ} {p c u z : α} (hp : p ∈ Rk F j) (hcov : p ⋖ c) (hpc : F p c = p) (hpu : F p u = c)
    (hcz : c < z) (hzu : z ≤ u) : F p z = c ∨ (F p z = p ∧ z ∈ Rk F (j + 1)) := by
  have hlo : p ≤ F p z := hpc.symm.le.trans ((F p).mono hcz.le)
  have hhi : F p z ≤ c := ((F p).mono hzu).trans hpu.le
  rcases hcov.eq_or_eq hlo hhi with e | e
  · exact Or.inr ⟨e, mem_succ_of_cell hp le_rfl (Or.inl e.le)⟩
  · exact Or.inl e

/-- **Exceptional columns are old covers of height `k + 1`**: with `R_{k+1}` tight, `j ≤ k`, `h(c) = k`, an exceptional
`z > c` (`z ∈ R_{j+1}`) has `h(z) = k + 1`, `c ⋖ z`, `z ∈ R_k`, and `b z ≤ p`. -/
theorem exceptional_column {k j H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {p c z : α} (hjk : j ≤ k) (hck : height H c = k) (hcz : c < z) (hzR : z ∈ Rk F (j + 1)) (hpz : F p z = p) :
    height H z = k + 1 ∧ c ⋖ z ∧ z ∈ Rk F (k + 1) ∧ b F z ≤ p := by
  have hz1 : z ∈ Rk F (k + 1) := Rk_mono (by omega) hzR
  have h1 := height_strictMono hn hcz; have h2 := hall z hz1
  exact ⟨by omega, covBy_of_height hn hcz (by omega), hz1, b_le hpz.le⟩

/-- **UpCell from a source-constant shadow interval** (the content of `siblingShadow_upCell`, with the tightness
replaced by the explicit hypothesis that the source row is constant `= c` on `(c, u]`, i.e. no exceptional column): a
column of `(c, u]` comparable with its row-`c` value gives UpCell at the height-`k` top `c ∈ R_k`. -/
theorem upCell_of_rowConst {k H : ℕ} (hn : NoChain α (H + 1)) {m p c u : α} (hc : c ∈ Rk F k)
    (hck : height H c = k) (hpc : p ≤ c) (hconst : ∀ z, c < z → z ≤ u → F p z = c) (hmu : ¬ m ≤ u)
    (hcase : ∃ z, c < z ∧ z ≤ u ∧ (F c z ≤ z ∨ z ≤ F c z)) : UpCell F H k m := by
  obtain ⟨z, hcz, hzu, h | h⟩ := hcase
  · refine upCell_of_descentWitness hn ⟨c, hc, hck, z, hcz, h, fun hm => hmu (hm.trans hzu), fun y hcy hyz _ => ?_⟩
    exact (hconst y hcy (hyz.trans hzu)).symm.le.trans ((F.mono hpc) y)
  · exact ⟨c, hc, hck, z, hcz, fun hm => hmu (hm.trans hzu), Or.inr h⟩

/-- **The A1 dichotomy without `R_k` tightness.** For an A1 row `c` (height `k`, `c ∈ R_k`) with B-source `p ⋖ c`,
`F p c = p`, `p ∈ R_j`, `j ≤ k`, and a fibre column `u` (`F p u = c`, `m ≰ u`) carrying a comparable column of row `c` in
`(c, u]`: either UpCell, or `(c, u]` contains an exceptional old cover `z` of `c` (height `k + 1`, `z ∈ R_k`, `b z ≤ p`,
`F p z = p`). -/
theorem a1_upCell_or_exceptional {k j H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m p c u : α} (hp : p ∈ Rk F j) (hjk : j ≤ k) (hc : c ∈ Rk F k) (hck : height H c = k) (hcov : p ⋖ c)
    (hpc : F p c = p) (hpu : F p u = c) (hmu : ¬ m ≤ u) (hcase : ∃ z, c < z ∧ z ≤ u ∧ (F c z ≤ z ∨ z ≤ F c z)) :
    UpCell F H k m ∨ ∃ z, c < z ∧ z ≤ u ∧ F p z = p ∧ height H z = k + 1 ∧ c ⋖ z ∧ z ∈ Rk F (j + 1) ∧ b F z ≤ p := by
  by_cases hex : ∃ z, c < z ∧ z ≤ u ∧ F p z = p
  · obtain ⟨z, hcz, hzu, hpz⟩ := hex
    have hzR : z ∈ Rk F (j + 1) := mem_succ_of_cell hp le_rfl (Or.inl hpz.le)
    obtain ⟨h1, h2, -, h4⟩ := exceptional_column hn hall hjk hck hcz hzR hpz
    exact Or.inr ⟨z, hcz, hzu, hpz, h1, h2, hzR, h4⟩
  · push_neg at hex
    refine Or.inl (upCell_of_rowConst hn hc hck hcov.le (fun z hcz hzu => ?_) hmu hcase)
    rcases source_row_or hp hcov hpc hpu hcz hzu with e | ⟨e, -⟩
    · exact e
    · exact absurd e (hex z hcz hzu)

/-! ### Exceptional covers and the clean A1 fibre (§34.3z¹⁹⁹) -/

/-- **`exceptional_same_source`**: for the actual B-source `p = b c`, an exceptional column `e ≥ c` with `b e ≤ p`
(`exceptional_column`) has `b e = p` (`b` is monotone). -/
theorem exceptional_same_source {c e : α} (hce : c ≤ e) (hbe : b F e ≤ b F c) : b F e = b F c :=
  le_antisymm hbe ((b F).mono hce)

/-- **`exception_join_dichotomy`.** For `p ⋖ c`, `F p c = p`, `F p u = c` (`p ∈ R_j`, `j ≤ k`, `h(c) = k`, `R_{k+1}` tight)
and a nonempty exception set `E = {e | c < e ≤ u ∧ F p e = p}`, its join `e* = ⋁E` satisfies `c < e* ≤ u` and either
* `F p e* = p` — then `e*` is itself exceptional, and **`E = {e*}`** (all exceptions have height `k + 1`); or
* `F p e* = c` — then `e*` is a fibre column (`m ≰ e*` as `e* ≤ u`). -/
theorem exception_join_dichotomy {k j H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {p c u : α} (hp : p ∈ Rk F j) (hjk : j ≤ k) (hck : height H c = k) (hcov : p ⋖ c) (hpc : F p c = p)
    (hpu : F p u = c) (hE : ∃ e, c < e ∧ e ≤ u ∧ F p e = p) :
    let E := {e | c < e ∧ e ≤ u ∧ F p e = p}
    c < sSup E ∧ sSup E ≤ u ∧
      ((F p (sSup E) = p ∧ E = {sSup E}) ∨ F p (sSup E) = c) := by
  intro E
  obtain ⟨e0, he0c, he0u, he0p⟩ := hE
  have he0E : e0 ∈ E := ⟨he0c, he0u, he0p⟩
  have hcs : c < sSup E := lt_of_lt_of_le he0c (le_sSup he0E)
  have hsu : sSup E ≤ u := sSup_le fun e he => he.2.1
  refine ⟨hcs, hsu, ?_⟩
  rcases source_row_or hp hcov hpc hpu hcs hsu with e | ⟨e, hR⟩
  · exact Or.inr e
  · left
    refine ⟨e, ?_⟩
    have hs := (exceptional_column hn hall hjk hck hcs hR e).1
    ext x
    constructor
    · intro hx
      have hxR : x ∈ Rk F (j + 1) := mem_succ_of_cell hp le_rfl (Or.inl hx.2.2.le)
      have hx1 := (exceptional_column hn hall hjk hck hx.1 hxR hx.2.2).1
      have hle : x ≤ sSup E := le_sSup hx
      by_contra hne
      have := height_strictMono hn (lt_of_le_of_ne hle hne); omega
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]; exact ⟨hcs, hsu, e⟩

/-- **`A1CleanFibre`**: an A1-shape configuration with a fibre column `u`, a comparable column `z ∈ (c, u]` of the row `c`,
and **no exceptional column in `(c, u]`**. -/
def A1CleanFibre (F : α →o α →o α) (H k : ℕ) (m : α) : Prop :=
  ∃ j p c u z, p ∈ Rk F j ∧ j ≤ k ∧ p ⋖ c ∧ c ∈ Rk F k ∧ height H c = k ∧ F p c = p ∧ F p u = c ∧ ¬ m ≤ u ∧
    c < z ∧ z ≤ u ∧ (F c z ≤ z ∨ z ≤ F c z) ∧ ∀ e, c < e → e ≤ u → F p e ≠ p

/-- **A clean A1 fibre gives UpCell** (`source_row_or` makes the source row constant on `(c, u]`, then
`upCell_of_rowConst`). No tightness. -/
theorem upCell_of_a1CleanFibre {k H : ℕ} (hn : NoChain α (H + 1)) {m : α} (h : A1CleanFibre F H k m) :
    UpCell F H k m := by
  obtain ⟨j, p, c, u, z, hp, -, hcov, hc, hck, hpc, hpu, hmu, hcz, hzu, hcmp, hclean⟩ := h
  refine upCell_of_rowConst hn hc hck hcov.le (fun e hce heu => ?_) hmu ⟨z, hcz, hzu, hcmp⟩
  rcases source_row_or hp hcov hpc hpu hce heu with r | ⟨r, -⟩
  · exact r
  · exact absurd r (hclean e hce heu)

/-- **`A1Cert`** (the sharp certificate): an A1-shape configuration and a column `z ∈ (c, u]` of a fibre column `u` such
that either `(c, z)` is already a cell, or `z` is row-`c` pre-fixed and `(c, z]` (not all of `(c, u]`) is free of
exceptional columns. -/
def A1Cert (F : α →o α →o α) (H k : ℕ) (m : α) : Prop :=
  ∃ j p c u z, p ∈ Rk F j ∧ p ⋖ c ∧ c ∈ Rk F k ∧ height H c = k ∧ F p c = p ∧ F p u = c ∧ ¬ m ≤ u ∧
    c < z ∧ z ≤ u ∧ ((F c z ≤ c ∨ z ≤ F c z) ∨ (F c z ≤ z ∧ ∀ e, c < e → e ≤ z → F p e ≠ p))

/-- `A1CleanFibre` is a special case of `A1Cert`. -/
theorem a1Cert_of_cleanFibre {k H : ℕ} {m : α} (h : A1CleanFibre F H k m) : A1Cert F H k m := by
  obtain ⟨j, p, c, u, z, hp, -, hcov, hc, hck, hpc, hpu, hmu, hcz, hzu, hcmp, hclean⟩ := h
  refine ⟨j, p, c, u, z, hp, hcov, hc, hck, hpc, hpu, hmu, hcz, hzu, ?_⟩
  rcases hcmp with h1 | h1
  · exact Or.inr ⟨h1, fun e hce hez => hclean e hce (hez.trans hzu)⟩
  · exact Or.inl (Or.inr h1)

/-- **`A1Cert` gives UpCell** (a cell directly; a pre-fixed column through the descent on the exception-free `(c, z]`). -/
theorem upCell_of_a1Cert {k H : ℕ} (hn : NoChain α (H + 1)) {m : α} (h : A1Cert F H k m) : UpCell F H k m := by
  obtain ⟨j, p, c, u, z, hp, hcov, hc, hck, hpc, hpu, hmu, hcz, hzu, hcase⟩ := h
  have hmz : ¬ m ≤ z := fun hm => hmu (hm.trans hzu)
  rcases hcase with hcell | ⟨hpre, hclean⟩
  · exact ⟨c, hc, hck, z, hcz, hmz, hcell⟩
  · refine upCell_of_rowConst hn hc hck hcov.le (u := z) (fun e hce hez => ?_) hmz ⟨z, hcz, le_rfl, Or.inl hpre⟩
    rcases source_row_or hp hcov hpc hpu hce (hez.trans hzu) with r | ⟨r, -⟩
    · exact r
    · exact absurd r (hclean e hce hez)

/-- **`A1RowTypeCert` (conjectural).** Under the MinUpCell hypotheses and the row-type consequences of ¬UpCell
(`noUpCell_rowTypes`: ascending height-`k` rows have `a x ∈ {x, m}`, stationary ones have no initial pair), a *genuine* A1
configuration (`p = b c ⋖ c`, `c` a non-ascending height-`k` row of `R_k`) with a nonempty fibre yields an `A1Cert`.
Exact search (§34.3z¹⁹⁹): no counterexample on every Moore family on 4 points and 8 rank-3/4 closure lists; dropping
¬IC(m) (`|L| = 5`) or the row-type constraints (`|L| = 7`) gives counterexamples. -/
def A1RowTypeCert (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k m, (∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) → m ∈ Rk F (k + 1) → height H m = k + 1 → m ∉ Rk F k → m ≠ ⊤ →
    (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) →
    (∀ x ∈ Rk F k, height H x = k → x ≤ a F x → a F x = x ∨ a F x = m) →
    (∀ x ∈ Rk F k, height H x = k → a F x = x → ¬ ∃ v, x < v ∧ F x v ≤ v ∧ ¬ m ≤ v) →
    ∀ c u, c ∈ Rk F k → height H c = k → b F c ⋖ c → ¬ c ≤ a F c → F (b F c) u = c → ¬ m ≤ u → c < u →
      A1Cert F H k m

/-- **What `A1RowTypeCert` buys**: without UpCell (and under the MinUpCell hypotheses), every genuine A1 configuration has
an *empty* off-`m` fibre — the row-type side conditions are theorems (`noUpCell_rowTypes`), and `A1Cert` would give UpCell
(`upCell_of_a1Cert`). -/
theorem noUpCell_a1_fibre_empty {k H : ℕ} (hn : NoChain α (H + 1)) (hc4 : A1RowTypeCert F H)
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m : α} (hm : m ∈ Rk F (k + 1)) (hmk : height H m = k + 1)
    (hnew : m ∉ Rk F k) (ht : m ≠ ⊤) (hno : ¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) (hnot : ¬ UpCell F H k m)
    {c u : α} (hc : c ∈ Rk F k) (hck : height H c = k) (hcov : b F c ⋖ c) (hna : ¬ c ≤ a F c)
    (hu : F (b F c) u = c) (hmu : ¬ m ≤ u) (hcu : c < u) : False := by
  have hasc : ∀ x ∈ Rk F k, height H x = k → x ≤ a F x → a F x = x ∨ a F x = m :=
    fun x hx hxk hxa => noUpCell_aResponse hn hall hmk hnot hx hxk hxa
  have hstat : ∀ x ∈ Rk F k, height H x = k → a F x = x → ¬ ∃ v, x < v ∧ F x v ≤ v ∧ ¬ m ≤ v :=
    fun x hx hxk hax ⟨v, hxv, hFv, hmv⟩ =>
      hnot (upCell_of_diagPost_pair hn hx hxk (stationary_b_le hax).1.ge hxv hFv hmv)
  exact hnot (upCell_of_a1Cert hn (hc4 k m hall hm hmk hnew ht hno hasc hstat c u hc hck hcov hna hu hmu hcu))

/-! ### The forbidden-row form of A1RowTypeCert (§34.3z²⁰⁰) -/

/-- **`A1BadForbidden`** (the brief's `badA1_forces_forbiddenRowType`): under the MinUpCell hypotheses, a genuine A1
configuration with a nonempty fibre and *no* `A1Cert` forces a forbidden row: an ascending height-`k` row with
`a x ∉ {x, m}`, or a stationary height-`k` row with an initial pair. -/
def A1BadForbidden (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k m, (∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) → m ∈ Rk F (k + 1) → height H m = k + 1 → m ∉ Rk F k → m ≠ ⊤ →
    (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) →
    ∀ c u, c ∈ Rk F k → height H c = k → b F c ⋖ c → ¬ c ≤ a F c → F (b F c) u = c → ¬ m ≤ u → c < u →
      ¬ A1Cert F H k m →
      (∃ x ∈ Rk F k, height H x = k ∧ x ≤ a F x ∧ a F x ≠ x ∧ a F x ≠ m) ∨
      (∃ x ∈ Rk F k, height H x = k ∧ a F x = x ∧ ∃ v, x < v ∧ F x v ≤ v ∧ ¬ m ≤ v)

/-- **`A1RowTypeCert ↔ A1BadForbidden`** (the two forms are contrapositives of each other). -/
theorem a1RowTypeCert_iff : A1RowTypeCert F H ↔ A1BadForbidden F H := by
  constructor
  · intro h k m hall hm hmk hnew ht hno c u hc hck hcov hna hu hmu hcu hnc
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    refine hnc (h k m hall hm hmk hnew ht hno (fun x hx hxk hxa => ?_) (fun x hx hxk hax hv => ?_)
      c u hc hck hcov hna hu hmu hcu)
    · by_contra hne
      push_neg at hne
      exact hne.2 (h1 x hx hxk hxa hne.1)
    · obtain ⟨v, hxv, hFv, hmv⟩ := hv
      exact hmv (h2 x hx hxk hax v hxv hFv)
  · intro h k m hall hm hmk hnew ht hno hasc hstat c u hc hck hcov hna hu hmu hcu
    by_contra hnc
    rcases h k m hall hm hmk hnew ht hno c u hc hck hcov hna hu hmu hcu hnc with
      ⟨x, hx, hxk, hxa, h1, h2⟩ | ⟨x, hx, hxk, hax, hv⟩
    · rcases hasc x hx hxk hxa with e | e
      · exact h1 e
      · exact h2 e
    · exact hstat x hx hxk hax hv

/-- **The A1 row value**: `F c u ≥ c` (from `F (b c) u = c`), and `F c u ≥ c ⊔ a c` when `a c ≤ u`. In the exact
counterexamples the forbidden row is most often `a c` itself, with `F c u = c ⊔ a c` (§34.3z²⁰⁰). -/
theorem a1_rowValue_ge {c u : α} (hu : F (b F c) u = c) (hbc : b F c ≤ c) :
    c ≤ F c u ∧ (a F c ≤ u → c ⊔ a F c ≤ F c u) := by
  have h1 : c ≤ F c u := hu.symm.le.trans ((F.mono hbc) u)
  refine ⟨h1, fun hau => sup_le h1 ?_⟩
  exact (row_a c).symm.le.trans ((F c).mono hau)

/-- The gfp of a non-ascending height-`k` row, if it is itself a height-`k` row, is incomparable with it. -/
theorem nonAscending_gfp_incomparable {H : ℕ} (hn : NoChain α (H + 1)) {c : α} (hna : ¬ c ≤ a F c)
    (hh : height H (a F c) = height H c) : ¬ c ≤ a F c ∧ ¬ a F c ≤ c := by
  refine ⟨hna, fun hle => ?_⟩
  rcases eq_or_lt_of_le hle with e | hlt
  · exact hna e.ge
  · have := height_strictMono hn hlt; omega

/-- **`A1SelfUpCell` (refuted, §34.3z²⁰¹)**: under the hypotheses of `A1RowTypeCert`, the genuine A1 top `c` itself
carries an off-`m` cell. Refuted at `|L| = 7` with the row types imposed (the certificate there comes from a sibling top
with the same source); the same-source sibling rescue is refuted at `|L| = 10`. An earlier SAT encoding that reported no
counterexample was wrong (an `↔` selector made it demand *every* genuine top lack a cell). Kept to record the
statement; `noUpCell_a1_fibre_empty'` is a conditional consequence only. -/
def A1SelfUpCell (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k m, (∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) → m ∈ Rk F (k + 1) → height H m = k + 1 → m ∉ Rk F k → m ≠ ⊤ →
    (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) →
    (∀ x ∈ Rk F k, height H x = k → x ≤ a F x → a F x = x ∨ a F x = m) →
    (∀ x ∈ Rk F k, height H x = k → a F x = x → ¬ ∃ v, x < v ∧ F x v ≤ v ∧ ¬ m ≤ v) →
    ∀ c u, c ∈ Rk F k → height H c = k → b F c ⋖ c → ¬ c ≤ a F c → F (b F c) u = c → ¬ m ≤ u → c < u →
      ∃ z, c < z ∧ ¬ m ≤ z ∧ (F c z ≤ c ∨ z ≤ F c z)

/-- **`A1SelfUpCell` also empties the genuine A1 fibres under ¬UpCell** (same shape as `noUpCell_a1_fibre_empty`). -/
theorem noUpCell_a1_fibre_empty' {k H : ℕ} (hn : NoChain α (H + 1)) (hself : A1SelfUpCell F H)
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m : α} (hm : m ∈ Rk F (k + 1)) (hmk : height H m = k + 1)
    (hnew : m ∉ Rk F k) (ht : m ≠ ⊤) (hno : ¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) (hnot : ¬ UpCell F H k m)
    {c u : α} (hc : c ∈ Rk F k) (hck : height H c = k) (hcov : b F c ⋖ c) (hna : ¬ c ≤ a F c)
    (hu : F (b F c) u = c) (hmu : ¬ m ≤ u) (hcu : c < u) : False := by
  have hasc : ∀ x ∈ Rk F k, height H x = k → x ≤ a F x → a F x = x ∨ a F x = m :=
    fun x hx hxk hxa => noUpCell_aResponse hn hall hmk hnot hx hxk hxa
  have hstat : ∀ x ∈ Rk F k, height H x = k → a F x = x → ¬ ∃ v, x < v ∧ F x v ≤ v ∧ ¬ m ≤ v :=
    fun x hx hxk hax ⟨v, hxv, hFv, hmv⟩ =>
      hnot (upCell_of_diagPost_pair hn hx hxk (stationary_b_le hax).1.ge hxv hFv hmv)
  obtain ⟨z, hcz, hmz, hcell⟩ := hself k m hall hm hmk hnew ht hno hasc hstat c u hc hck hcov hna hu hmu hcu
  exact hnot ⟨c, hc, hck, z, hcz, hmz, hcell⟩

/-- **`DominantA1` (refuted, §34.3z²⁰²)**: the dominant-branch statement. For a genuine A1 configuration with
`y = a c` a height-`k` row of `R_k` and `F c u = c ⊔ y`, either an `A1Cert` exists or `y` itself is a forbidden row. It
holds on every Moore family on 4 points but fails at rank 3 (`|L| = 14`), where the forbidden row is the next A-iterate
`a y`. -/
def DominantA1 (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k m, (∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) → m ∈ Rk F (k + 1) → height H m = k + 1 → m ∉ Rk F k → m ≠ ⊤ →
    (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) →
    ∀ c u, c ∈ Rk F k → height H c = k → b F c ⋖ c → ¬ c ≤ a F c → F (b F c) u = c → ¬ m ≤ u → c < u →
      a F c ∈ Rk F k → height H (a F c) = k → F c u = c ⊔ a F c →
      A1Cert F H k m ∨ (a F c ≤ a F (a F c) ∧ a F (a F c) ≠ a F c ∧ a F (a F c) ≠ m) ∨
        (a F (a F c) = a F c ∧ ∃ v, a F c < v ∧ F (a F c) v ≤ v ∧ ¬ m ≤ v)

/-! ### From forbidden rows to SecondEntry (§34.3z²⁰³) -/

/-- UpCell gives SecondEntry (`canonical_of_upCell`, `secondEntry_of_canonical`). -/
theorem secondEntry_of_upCell {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m : α} (h : UpCell F H k m) : SecondEntry F H k m :=
  secondEntry_of_canonical (canonical_of_upCell hn hall h)

/-- **An other-ascending row is an UpCell row**: `x < a x ≠ m`; `a x ∈ R_{k+1}` has height `k + 1 = h(m)`, so `m ≰ a x`, and
`F x (a x) = a x` is an upper cell. -/
theorem upCell_of_otherAscending {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m x : α} (hmk : height H m = k + 1) (hx : x ∈ Rk F k) (hxk : height H x = k) (hxa : x ≤ a F x)
    (h1 : a F x ≠ x) (h2 : a F x ≠ m) : UpCell F H k m := by
  have hlt : x < a F x := lt_of_le_of_ne hxa (Ne.symm h1)
  have hR := hall _ (mem_succ_of_a hx le_rfl)
  have hma : ¬ m ≤ a F x := fun hle => by
    rcases eq_or_lt_of_le hle with e | hl
    · exact h2 e.symm
    · have := height_strictMono hn hl; omega
  exact ⟨x, hx, hxk, a F x, hlt, hma, Or.inr (row_a x).ge⟩

/-- **`secondEntry_of_A1BadForbidden`**: under the MinUpCell hypotheses, if `A1BadForbidden` holds, every genuine A1
configuration with a nonempty off-`m` fibre forces a second top (`SecondEntry`): an `A1Cert` gives UpCell
(`upCell_of_a1Cert`); an other-ascending row gives UpCell (`upCell_of_otherAscending`); a stationary row with an
initial pair gives UpCell (`upCell_of_diagPost_pair`). -/
theorem secondEntry_of_A1BadForbidden {k H : ℕ} (hn : NoChain α (H + 1)) (hbf : A1BadForbidden F H)
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m : α} (hm : m ∈ Rk F (k + 1)) (hmk : height H m = k + 1)
    (hnew : m ∉ Rk F k) (ht : m ≠ ⊤) (hno : ¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y))
    {c u : α} (hc : c ∈ Rk F k) (hck : height H c = k) (hcov : b F c ⋖ c) (hna : ¬ c ≤ a F c)
    (hu : F (b F c) u = c) (hmu : ¬ m ≤ u) (hcu : c < u) : SecondEntry F H k m := by
  refine secondEntry_of_upCell hn hall ?_
  by_cases hcert : A1Cert F H k m
  · exact upCell_of_a1Cert hn hcert
  · rcases hbf k m hall hm hmk hnew ht hno c u hc hck hcov hna hu hmu hcu hcert with
      ⟨x, hx, hxk, hxa, h1, h2⟩ | ⟨x, hx, hxk, hax, v, hxv, hFv, hmv⟩
    · exact upCell_of_otherAscending hn hall hmk hx hxk hxa h1 h2
    · exact upCell_of_diagPost_pair hn hx hxk (stationary_b_le hax).1.ge hxv hFv hmv

/-- **`SecondEntryOfGenuineA1` (conjectural, §34.3z²⁰³)**: the direct target — under the MinUpCell hypotheses a genuine
A1 configuration with a nonempty off-`m` fibre forces a second top. Implied by `A1BadForbidden`
(`secondEntry_of_A1BadForbidden`). -/
def SecondEntryOfGenuineA1 (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k m, (∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) → m ∈ Rk F (k + 1) → height H m = k + 1 → m ∉ Rk F k → m ≠ ⊤ →
    (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) →
    ∀ c u, c ∈ Rk F k → height H c = k → b F c ⋖ c → ¬ c ≤ a F c → F (b F c) u = c → ¬ m ≤ u → c < u →
      SecondEntry F H k m

theorem secondEntryOfGenuineA1_of_badForbidden {H : ℕ} (hn : NoChain α (H + 1)) (hbf : A1BadForbidden F H) :
    SecondEntryOfGenuineA1 F H := fun _ _ hall hm hmk hnew ht hno _ _ hc hck hcov hna hu hmu hcu =>
  secondEntry_of_A1BadForbidden hn hbf hall hm hmk hnew ht hno hc hck hcov hna hu hmu hcu

/-- **`MinSecondEntry`** (conjectural): the MinUpCell hypotheses force a second top. Weaker than `MinUpCell` (UpCell
gives SecondEntry), and still sufficient for SingletonLower, which only uses the second top against the uniqueness of
`m`. Exact search (§34.3z²⁰³): no model of the MinUpCell hypotheses with `m` the unique top on sweep 4 16 and rank-3
closure lists. -/
def MinSecondEntry (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ k m, (∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) → m ∈ Rk F (k + 1) → height H m = k + 1 → m ∉ Rk F k → m ≠ ⊤ →
    (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) → SecondEntry F H k m

theorem minSecondEntry_of_minUpCell {H : ℕ} (hn : NoChain α (H + 1)) (h : MinUpCell F H) : MinSecondEntry F H :=
  fun k m hall hm hmk hnew ht hno => secondEntry_of_upCell hn hall (h k m hall hm hmk hnew ht hno)

/-- **SingletonLower from MinSecondEntry** (the second top contradicts the uniqueness of `m`). -/
theorem singletonLower_of_minSecondEntry (h : MinSecondEntry F H) : SingletonLower F H := by
  intro k htop _ hall m huniq hm hmk hnew _ _ _ _ _
  by_contra hno
  obtain ⟨z, hzm, hz, hzR⟩ := h k m hall hm hmk hnew (fun e => htop (e ▸ Rk_mono (Nat.le_succ _) hm)) hno
  exact hzm (huniq z hzR hz)

/-- **MinSecondEntry at `k = 0`** (from `upCell_zero`). -/
theorem minSecondEntry_zero [WellFoundedLT α] {H : ℕ} (hn : NoChain α (H + 1)) {m : α}
    (hall : ∀ z ∈ Rk F 1, height H z ≤ 1) (ht : m ≠ ⊤) (hno : ¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) :
    SecondEntry F H 0 m :=
  secondEntry_of_upCell hn hall (upCell_zero hn ht hno)

/-- `SecondEntryOfGenuineA1` is a special case of `MinSecondEntry`. -/
theorem secondEntryOfGenuineA1_of_min {H : ℕ} (h : MinSecondEntry F H) : SecondEntryOfGenuineA1 F H :=
  fun k m hall hm hmk hnew ht hno _ _ _ _ _ _ _ _ _ => h k m hall hm hmk hnew ht hno

/-! ### Uniqueness consequences and the k = 1 anatomy (§34.3z²⁰⁴) -/

/-- **Without a second top, `R_k` is tight.** A height-`(k + 1)` element of `R_k ⊆ R_{k+1}` would be `m`, and
`m ∉ R_k`. So the extra `R_k` tightness needed by `topLayerEntry_iff_fixed_edge` and `secondEntry_iff_switching` is
free in any proof of `MinSecondEntry` by contradiction. -/
theorem tight_of_not_secondEntry {H k : ℕ} {m : α} (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    (hnew : m ∉ Rk F k) (hse : ¬ SecondEntry F H k m) : ∀ z ∈ Rk F k, height H z ≤ k := by
  intro z hz
  have h1 := hall z (Rk_mono (Nat.le_succ k) hz)
  by_contra hlt
  by_cases hzm : z = m
  · exact hnew (hzm ▸ hz)
  · exact hse ⟨z, hzm, by omega, Rk_mono (Nat.le_succ k) hz⟩

/-- **Without a second top, every cell of a height-`k` row of `R_k` above the row is at `m`.** -/
theorem cell_eq_of_not_secondEntry {H k : ℕ} (hn : NoChain α (H + 1)) {m x z : α}
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) (hse : ¬ SecondEntry F H k m)
    (hx : x ∈ Rk F k) (hxk : height H x = k) (hxz : x < z) (hc : F x z ≤ x ∨ z ≤ F x z) : z = m := by
  by_contra hzm
  have hzR := mem_succ_of_cell hx le_rfl hc
  have := height_strictMono hn hxz; have := hall z hzR
  exact hse ⟨z, hzm, by omega, hzR⟩

/-- **Without a second top, a height-`k` row of `R_k` off `m` has no interval cell.** -/
theorem noIC_of_not_secondEntry {H k : ℕ} (hn : NoChain α (H + 1)) {m x : α}
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) (hse : ¬ SecondEntry F H k m)
    (hx : x ∈ Rk F k) (hxk : height H x = k) (hxm : ¬ x ≤ m) : ¬ ∃ z, x < z ∧ (F x z ≤ x ∨ z ≤ F x z) :=
  fun ⟨_, hxz, hc⟩ => hxm ((cell_eq_of_not_secondEntry hn hall hse hx hxk hxz hc) ▸ hxz.le)

/-- **`F ⊥ m ≤ w`** for every column fixed point `y = m ⊔ F m y` (`w = F m y`); no hypothesis on `m`. -/
theorem bot_row_le_side {m y : α} (hy : m ⊔ F m y = y) : F ⊥ m ≤ F m y :=
  ((F ⊥).mono (le_sup_left.trans hy.le)).trans ((F.mono bot_le) y)

/-- **k = 1: `a ⊥ = ⊥` without a second top** (else `a ⊥` is a diagonal post-fixed top of `R_1`,
`secondEntry_of_post_layer`). -/
theorem a_bot_of_not_secondEntry_one [WellFoundedLT α] {H : ℕ} (hn : NoChain α (H + 1)) {m : α}
    (hall : ∀ z ∈ Rk F (1 + 1), height H z ≤ 1 + 1) (hnew : m ∉ Rk F 1) (ht : m ≠ ⊤)
    (hno : ¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) (hse : ¬ SecondEntry F H 1 m) : a F ⊥ = ⊥ := by
  by_contra hne
  have hk1 := tight_of_not_secondEntry hall hnew hse
  have haR : a F ⊥ ∈ Rk F 1 := mem_succ_of_a (k := 0) (show (⊥ : α) ∈ Set.Iic ⊥ from le_rfl) le_rfl
  have h0 := height_strictMono hn (bot_lt_iff_ne_bot.2 hne)
  rw [height_bot_eq_zero] at h0
  have h1 : height H (a F ⊥) = 1 := by have := hk1 _ haR; omega
  exact hse (secondEntry_of_post_layer hn hall hnew ht hno
    ⟨a F ⊥, haR, h1, (row_a ⊥).symm.le.trans ((F.mono bot_le) _)⟩)

/-- **k = 1 anatomy without a second top.** If `m` has no interval cell and there is no second top at stage 1, then
for the column fixed point `y*` (output `w = F m y*`, `m ≰ w`) some `e ∈ R_1` of height 1 lies below `w`, off `m`, and
has no interval cell. Proof: the `⊥`-row descent from `w` gives `d ∈ R_1 ∩ ↓w`; if `d ≤ m`, the saturated shadow of
row `d` from `w` gives `q = d ⊔ g ≤ w` with `g = F d q ∥ d`, and the `⊥`-descent from `g` gives `e ≤ g`. Were `e ≤ m`,
`d ⊔ e = m ≤ w` by heights. -/
theorem exists_cellFree_off_one [WellFoundedLT α] {H : ℕ} (hn : NoChain α (H + 1)) {m : α}
    (hall : ∀ z ∈ Rk F (1 + 1), height H z ≤ 1 + 1) (hmk : height H m = 2) (hnew : m ∉ Rk F 1) (ht : m ≠ ⊤)
    (hno : ¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) (hse : ¬ SecondEntry F H 1 m) :
    ∃ y, m ⊔ F m y = y ∧ ¬ m ≤ F m y ∧ ∃ e ∈ Rk F 1, height H e = 1 ∧ e ≤ F m y ∧ ¬ e ≤ m ∧
      ¬ ∃ z, e < z ∧ (F e z ≤ e ∨ z ≤ F e z) := by
  rcases colOrb_dichotomy (F := F) ht with hc | ⟨n, -, hfix, -, hmw, hwm⟩
  · exact (hno hc).elim
  have hk1 := tight_of_not_secondEntry hall hnew hse
  have desc : ∀ v, ⊥ < v → F ⊥ v ≤ v → ∃ z ∈ Rk F 1, height H z = 1 ∧ z ≤ v := by
    intro v hv hFv
    obtain ⟨z, hz1, hz2, hz3⟩ := row_cell_of_diag_post hn (x := ⊥) bot_le H (height_le _) hv hFv
    have hzR : z ∈ Rk F 1 := mem_succ_of_cell (k := 0) (show (⊥ : α) ∈ Set.Iic ⊥ from le_rfl) le_rfl hz3
    have h0 := height_strictMono hn hz1
    rw [height_bot_eq_zero] at h0
    have := hk1 z hzR
    exact ⟨z, hzR, by omega, hz2⟩
  have hcf : ∀ e ∈ Rk F 1, height H e = 1 → ¬ e ≤ m → ¬ ∃ z, e < z ∧ (F e z ≤ e ∨ z ≤ F e z) :=
    fun e he he1 hem => noIC_of_not_secondEntry hn hall hse he he1 hem
  have hwb : ⊥ < F m (colOrb F m n) := bot_lt_iff_ne_bot.2 fun e => hwm (e ▸ bot_le)
  obtain ⟨d, hdR, hd1, hdw⟩ := desc _ hwb (feeder_le_side bot_le hfix)
  by_cases hdm : d ≤ m
  swap
  · exact ⟨_, hfix, hmw, d, hdR, hd1, hdw, hdm, hcf d hdR hd1 hdm⟩
  have hnot : ¬ UpCell F H 1 m := fun h => hse (secondEntry_of_upCell hn hall h)
  have hdlt : d < F m (colOrb F m n) := lt_of_le_of_ne hdw fun e => hwm (e ▸ hdm)
  obtain ⟨q, hdq, hqw, -, hFq, -, hdg, hgd⟩ :=
    saturated_shadow (v := F m (colOrb F m n)) hn hnot hdR hd1 H (height_le _) hdlt le_rfl
      (feeder_le_side hdm hfix) hmw
  have hFg : F ⊥ (F d q) ≤ F d q := ((F.mono bot_le) _).trans ((F d).mono hFq)
  have hgb : ⊥ < F d q := bot_lt_iff_ne_bot.2 fun e => hgd (e ▸ bot_le)
  obtain ⟨z, hzR, hz1, hzg⟩ := desc _ hgb hFg
  have hzm : ¬ z ≤ m := by
    intro hzm
    have hzd : ¬ z ≤ d := fun h => by
      have : z = d := by
        by_contra hne; have := height_strictMono hn (lt_of_le_of_ne h hne); omega
      exact hdg (this ▸ hzg)
    have hlt1 : d < d ⊔ z := lt_of_le_of_ne le_sup_left fun e => hzd (e ▸ le_sup_right)
    have hle : d ⊔ z ≤ m := sup_le hdm hzm
    have heq : d ⊔ z = m := by
      by_contra hne
      have := height_strictMono hn hlt1; have := height_strictMono hn (lt_of_le_of_ne hle hne); omega
    exact hmw (heq.ge.trans ((sup_le hdq.le (hzg.trans hFq)).trans hqw))
  exact ⟨_, hfix, hmw, z, hzR, hz1, hzg.trans (hFq.trans hqw), hzm, hcf z hzR hz1 hzm⟩

/-! ### The k = 1 bottom-row descent and LT pairs (§34.3z²⁰⁵) -/

/-- **Bottom-row descent at k = 1.** With `R_1` tight, let `x` have height 1, `x < v`, `F x v ≤ v` and `F ⊥ v ≤ x`.
Then row `x` has a cell in `(x, v]`. Along the descent `u ↦ F x u` from `v`, each `u > x` has height `≥ 2`, so `u ∉ R_1`
and `F ⊥ u ≠ ⊥`; since `F ⊥ u ≤ F ⊥ v ≤ x` and `x` has height 1, `F ⊥ u = x`, whence `x ≤ F x u`. (The descent-witness
condition of `DescentWitness` is thus supplied by the bottom row.) -/
theorem row_cell_of_bot_le_one {H : ℕ} (hn : NoChain α (H + 1)) (hk1 : ∀ z ∈ Rk F 1, height H z ≤ 1) {x : α}
    (hx1 : height H x = 1) :
    ∀ (n : ℕ) {v : α}, height H v ≤ n → x < v → F x v ≤ v → F ⊥ v ≤ x →
      ∃ z, x < z ∧ z ≤ v ∧ (F x z ≤ x ∨ z ≤ F x z)
  | 0, v, hv, hxv, _, _ => by have := height_strictMono hn hxv; omega
  | n + 1, v, hv, hxv, hFv, hbv => by
      by_cases h1 : F x v ≤ x
      · exact ⟨v, hxv, le_rfl, Or.inl h1⟩
      by_cases h2 : v ≤ F x v
      · exact ⟨v, hxv, le_rfl, Or.inr h2⟩
      have hvx := height_strictMono hn hxv
      have hbx : F ⊥ v = x := by
        rcases eq_or_ne (F ⊥ v) ⊥ with h0 | h0
        · have hvR : v ∈ Rk F 1 :=
            mem_succ_of_cell (k := 0) (show (⊥ : α) ∈ Set.Iic ⊥ from le_rfl) le_rfl (Or.inl h0.le)
          have := hk1 v hvR; omega
        · by_contra hne
          have h3 := height_strictMono hn (lt_of_le_of_ne hbv hne)
          have h4 := height_strictMono hn (bot_lt_iff_ne_bot.2 h0)
          rw [height_bot_eq_zero] at h4; omega
      have hxg : x < F x v := lt_of_le_not_ge (hbx.symm.le.trans ((F.mono bot_le) v)) h1
      have hgv : F x v < v := lt_of_le_not_ge hFv h2
      have := height_strictMono hn hgv
      obtain ⟨z, hz1, hz2, hz3⟩ := row_cell_of_bot_le_one hn hk1 hx1 n (by omega) hxg ((F x).mono hFv)
        (((F ⊥).mono hgv.le).trans hbv)
      exact ⟨z, hz1, hz2.trans hgv.le, hz3⟩

/-- **A height-1 bound of a bottom-row value lies in `R_1`**: if `F ⊥ v ≤ x ≤ v` and `h(x) = 1`, then `F ⊥ x ≤ x`, so
`F ⊥ x ∈ {⊥, x}` is a cell of row `⊥` at `x`. -/
theorem mem_one_of_bot_value {H : ℕ} (hn : NoChain α (H + 1)) {x v : α} (hx1 : height H x = 1) (hxv : x ≤ v)
    (hbv : F ⊥ v ≤ x) : x ∈ Rk F 1 := by
  have hpre : F ⊥ x ≤ x := ((F ⊥).mono hxv).trans hbv
  refine mem_succ_of_cell (k := 0) (m := ⊥) (x := ⊥) (y := x) (show (⊥ : α) ∈ Set.Iic ⊥ from le_rfl) le_rfl ?_
  by_cases he : F ⊥ x = x
  · exact Or.inr he.ge
  · left
    by_contra h0
    have h3 := height_strictMono hn (lt_of_le_of_ne hpre he)
    have h4 := height_strictMono hn (bot_lt_iff_ne_bot.2 fun e => h0 e.le)
    rw [height_bot_eq_zero] at h4; omega

/-- **UpCell at k = 1 from the bottom-row value of `w`** (no uniqueness). Let `y = m ⊔ F m y`, `w = F m y ≱ m`, and
`x = F ⊥ w ≠ w` of height 1 with `F x w ≤ w`. Then `(x, w)` is an LT pair, and row `x ∈ R_1` has a cell in `(x, w]`. -/
theorem upCell_of_bot_side_one {H : ℕ} (hn : NoChain α (H + 1)) (hk1 : ∀ z ∈ Rk F 1, height H z ≤ 1) {m y : α}
    (hy : m ⊔ F m y = y) (hmw : ¬ m ≤ F m y) (hx1 : height H (F ⊥ (F m y)) = 1) (hne : F ⊥ (F m y) ≠ F m y)
    (hpre : F (F ⊥ (F m y)) (F m y) ≤ F m y) : UpCell F H 1 m := by
  have hxw : F ⊥ (F m y) < F m y := lt_of_le_of_ne (feeder_le_side bot_le hy) hne
  have hxR := mem_one_of_bot_value hn hx1 hxw.le le_rfl
  obtain ⟨z, hz1, hz2, hz3⟩ := row_cell_of_bot_le_one hn hk1 hx1 H (height_le _) hxw hpre le_rfl
  exact ⟨_, hxR, hx1, z, hz1, fun h => hmw (h.trans hz2), hz3⟩

/-- **The same when `F ⊥ w ≤ m`**: then `F (F ⊥ w) w ≤ F m y = w` automatically (`feeder_le_side`). -/
theorem upCell_of_bot_side_le_one {H : ℕ} (hn : NoChain α (H + 1)) (hk1 : ∀ z ∈ Rk F 1, height H z ≤ 1) {m y : α}
    (hy : m ⊔ F m y = y) (hmw : ¬ m ≤ F m y) (hwm : ¬ F m y ≤ m) (hx1 : height H (F ⊥ (F m y)) = 1)
    (hxm : F ⊥ (F m y) ≤ m) : UpCell F H 1 m :=
  upCell_of_bot_side_one hn hk1 hy hmw hx1 (fun e => hwm (e.symm.le.trans hxm)) (feeder_le_side hxm hy)

/-- **The k = 1 residue of the bottom-row value.** Without a second top at stage 1, the bottom-row value `x = F ⊥ w` of
any column output `w = F m y ≱ m` (`y = m ⊔ F m y`) is `w` itself, or not of height 1, or has `F x w ≰ w`. -/
theorem bot_side_residue_one {H : ℕ} (hn : NoChain α (H + 1)) {m y : α}
    (hall : ∀ z ∈ Rk F (1 + 1), height H z ≤ 1 + 1) (hnew : m ∉ Rk F 1) (hse : ¬ SecondEntry F H 1 m)
    (hy : m ⊔ F m y = y) (hmw : ¬ m ≤ F m y) :
    F ⊥ (F m y) = F m y ∨ height H (F ⊥ (F m y)) ≠ 1 ∨ ¬ F (F ⊥ (F m y)) (F m y) ≤ F m y := by
  by_contra h
  push_neg at h
  obtain ⟨hne, hx1, hpre⟩ := h
  exact hse (secondEntry_of_upCell hn hall
    (upCell_of_bot_side_one hn (tight_of_not_secondEntry hall hnew hse) hy hmw hx1 hne hpre))

/-- **LT pair** at stage 1: `x ∈ R_1` of height 1 and `v ≱ m` with `x < v`, `F x v ≤ v`, `F ⊥ v ≤ x`. -/
def LTPair (F : α →o α →o α) (H : ℕ) (m : α) : Prop :=
  ∃ x ∈ Rk F 1, height H x = 1 ∧ ∃ v, x < v ∧ ¬ m ≤ v ∧ F x v ≤ v ∧ F ⊥ v ≤ x

/-- **An LT pair gives a second top** (k = 1; no uniqueness, no tightness of `R_1` assumed: without a second top it
holds by `tight_of_not_secondEntry`). -/
theorem secondEntry_of_LTPair {H : ℕ} (hn : NoChain α (H + 1)) {m : α}
    (hall : ∀ z ∈ Rk F (1 + 1), height H z ≤ 1 + 1) (hnew : m ∉ Rk F 1) (h : LTPair F H m) : SecondEntry F H 1 m := by
  by_contra hse
  obtain ⟨x, hx, hx1, v, hxv, hmv, hFv, hbv⟩ := h
  have hk1 := tight_of_not_secondEntry hall hnew hse
  obtain ⟨z, hz1, hz2, hz3⟩ := row_cell_of_bot_le_one hn hk1 hx1 H (height_le _) hxv hFv hbv
  have hzm := cell_eq_of_not_secondEntry hn hall hse hx hx1 hz1 hz3
  exact hmv (hzm ▸ hz2)

/-- **MinLT (conjectural)**: the MinUpCell hypotheses at k = 1, with `R_1` tight and uniqueness dropped, give an LT
pair. No counterexample (exact search, §34.3z²⁰⁵). -/
def MinLT (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ m, (∀ z ∈ Rk F (1 + 1), height H z ≤ 1 + 1) → (∀ z ∈ Rk F 1, height H z ≤ 1) → m ∈ Rk F (1 + 1) →
    height H m = 1 + 1 → m ∉ Rk F 1 → m ≠ ⊤ → (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) → LTPair F H m

/-- **MinLT gives MinSecondEntry at k = 1.** -/
theorem secondEntry_one_of_minLT {H : ℕ} (hn : NoChain α (H + 1)) (h : MinLT F H) {m : α}
    (hall : ∀ z ∈ Rk F (1 + 1), height H z ≤ 1 + 1) (hm : m ∈ Rk F (1 + 1)) (hmk : height H m = 1 + 1)
    (hnew : m ∉ Rk F 1) (ht : m ≠ ⊤) (hno : ¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) : SecondEntry F H 1 m := by
  by_contra hse
  exact hse (secondEntry_of_LTPair hn hall hnew
    (h m hall (tight_of_not_secondEntry hall hnew hse) hm hmk hnew ht hno))

/-! ### RowLT2: the row of the bottom-row descent from `w*` (§34.3z²⁰⁶) -/

/-- The bottom-row iterates of a `⊥`-pre-fixed column decrease. -/
theorem bot_iter_le {v : α} (hv : F ⊥ v ≤ v) : ∀ i, (F ⊥)^[i + 1] v ≤ (F ⊥)^[i] v
  | 0 => hv
  | i + 1 => by
      have h := bot_iter_le hv i
      rw [Function.iterate_succ_apply'] at h
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact (F ⊥).mono h

/-- **The bottom-row descent passes through height 1.** With `R_1` tight and `a ⊥ = ⊥`, the descent `v ↦ F ⊥ v` from a
`⊥`-pre-fixed `v ≠ ⊥` reaches `⊥` (its fixed point lies below `a ⊥`), and its last nonzero term has height 1: it is sent
to `⊥`, so it lies in `R_1`. -/
theorem exists_bot_descent_atom {H : ℕ} (hn : NoChain α (H + 1)) (hk1 : ∀ z ∈ Rk F 1, height H z ≤ 1)
    (hab : a F ⊥ = ⊥) {v : α} (hv : F ⊥ v ≤ v) (hvb : v ≠ ⊥) : ∃ i, height H ((F ⊥)^[i] v) = 1 := by
  classical
  obtain ⟨N, hN⟩ := exists_iter_fix hn (x := ⊥) H (height_le _) hv
  have hs : (F ⊥)^[N] v = ⊥ := le_bot_iff.1 ((le_a hN.ge).trans hab.le)
  have hex : ∃ i, (F ⊥)^[i] v = ⊥ := ⟨N, hs⟩
  obtain ⟨j, hj, hmin⟩ : ∃ j, (F ⊥)^[j] v = ⊥ ∧ ∀ i < j, (F ⊥)^[i] v ≠ ⊥ :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  rcases j with _ | i
  · exact absurd hj hvb
  have hi := hmin i (Nat.lt_succ_self i)
  rw [Function.iterate_succ_apply'] at hj
  have hR := mem_succ_of_cell (k := 0) (m := ⊥) (x := ⊥) (y := (F ⊥)^[i] v)
    (show (⊥ : α) ∈ Set.Iic ⊥ from le_rfl) le_rfl (Or.inl hj.le)
  have h1 := hk1 _ hR
  have h0 := height_strictMono hn (bot_lt_iff_ne_bot.2 hi)
  rw [height_bot_eq_zero] at h0
  exact ⟨i, by omega⟩

/-- **RowLT2 (conjectural).** At k = 1, let `y` be the greatest post-fixed point of `y ↦ m ⊔ F m y` with `w = F m y ≱ m`,
and let `x` be a height-1 term of the bottom-row descent from `w`. If `m` has no interval cell, row `x` carries an LT
pair. No counterexample (exact search, §34.3z²⁰⁶); `¬IC(m)` is needed (`|L| = 4` without it). Fixing the column instead
is refuted: `v = w` (DescLT, `|L| = 7`) and the orbit of `x` from `w` (OrbitLT, `|L| = 10`). -/
def RowLT2 (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ m y, (∀ z ∈ Rk F (1 + 1), height H z ≤ 1 + 1) → (∀ z ∈ Rk F 1, height H z ≤ 1) → m ∈ Rk F (1 + 1) →
    height H m = 1 + 1 → m ∉ Rk F 1 → (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) →
    m ⊔ F m y = y → (∀ z, z ≤ m ⊔ F m z → z ≤ y) → ¬ m ≤ F m y →
    ∀ i, height H ((F ⊥)^[i] (F m y)) = 1 →
      ∃ v, (F ⊥)^[i] (F m y) < v ∧ ¬ m ≤ v ∧ F ((F ⊥)^[i] (F m y)) v ≤ v ∧ F ⊥ v ≤ (F ⊥)^[i] (F m y)

/-- **RowLT2 gives MinSecondEntry at k = 1.** Without a second top, `R_1` is tight and `a ⊥ = ⊥`, the column orbit gives
`y*`, the bottom-row descent from `w*` passes through height 1, and RowLT2 supplies an LT pair there. -/
theorem secondEntry_one_of_rowLT2 [WellFoundedLT α] {H : ℕ} (hn : NoChain α (H + 1)) (h : RowLT2 F H) {m : α}
    (hall : ∀ z ∈ Rk F (1 + 1), height H z ≤ 1 + 1) (hm : m ∈ Rk F (1 + 1)) (hmk : height H m = 1 + 1)
    (hnew : m ∉ Rk F 1) (ht : m ≠ ⊤) (hno : ¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) : SecondEntry F H 1 m := by
  by_contra hse
  have hk1 := tight_of_not_secondEntry hall hnew hse
  have hab := a_bot_of_not_secondEntry_one hn hall hnew ht hno hse
  rcases colOrb_dichotomy (F := F) ht with hc | ⟨n, -, hfix, hgfp, hmw, hwm⟩
  · exact hno hc
  have hpre : F ⊥ (F m (colOrb F m n)) ≤ F m (colOrb F m n) := feeder_le_side bot_le hfix
  have hwb : F m (colOrb F m n) ≠ ⊥ := fun e => hwm (e.le.trans bot_le)
  obtain ⟨i, hi1⟩ := exists_bot_descent_atom hn hk1 hab hpre hwb
  obtain ⟨v, hxv, hmv, hFv, hbv⟩ := h m _ hall hk1 hm hmk hnew hno hfix hgfp hmw i hi1
  have hxx := bot_iter_le hpre i
  rw [Function.iterate_succ_apply'] at hxx
  have hxR := mem_one_of_bot_value hn hi1 le_rfl hxx
  exact hse (secondEntry_of_LTPair hn hall hnew ⟨_, hxR, hi1, v, hxv, hmv, hFv, hbv⟩)

/-! ### TightRowCell2: a bare two-stage lemma (§34.3z²⁰⁷) -/

/-- **TightRowCell2 (conjectural).** Let `R_1` and `R_2` be tight and `m` of height 2 with no interval cell. Let `y` be
the greatest post-fixed point of `y ↦ m ⊔ F m y`, with `w = F m y ≱ m`, and let `x` be a height-1 term of the
bottom-row descent from `w`. Then row `x` has an interval cell at some `z > x` with `m ≰ z`. Neither `m ∈ R_2` nor
`m ∉ R_1` is assumed. No counterexample (exact, `bare_rowcell.py cell2`, §34.3z²⁰⁷). It fails without `R_1` tightness
(`|L| = 10`), without `R_2` tightness (`|L| = 7`), and without `¬IC(m)` (the degenerate `y* = m`). -/
def TightRowCell2 (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ m y, (∀ z ∈ Rk F 1, height H z ≤ 1) → (∀ z ∈ Rk F (1 + 1), height H z ≤ 1 + 1) → height H m = 1 + 1 →
    (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) → m ⊔ F m y = y → (∀ z, z ≤ m ⊔ F m z → z ≤ y) → ¬ m ≤ F m y →
    ∀ i, height H ((F ⊥)^[i] (F m y)) = 1 →
      ∃ z, (F ⊥)^[i] (F m y) < z ∧ ¬ m ≤ z ∧ (F ((F ⊥)^[i] (F m y)) z ≤ (F ⊥)^[i] (F m y) ∨ z ≤ F ((F ⊥)^[i] (F m y)) z)

/-- **TightRowCell2 gives MinSecondEntry at k = 1.** As in `secondEntry_one_of_rowLT2`, with the cell given directly:
the descent term is in `R_1`, so its cell is a top of `R_2` other than `m`. -/
theorem secondEntry_one_of_tightRowCell2 [WellFoundedLT α] {H : ℕ} (hn : NoChain α (H + 1)) (h : TightRowCell2 F H)
    {m : α} (hall : ∀ z ∈ Rk F (1 + 1), height H z ≤ 1 + 1) (hmk : height H m = 1 + 1) (hnew : m ∉ Rk F 1)
    (ht : m ≠ ⊤) (hno : ¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) : SecondEntry F H 1 m := by
  by_contra hse
  have hk1 := tight_of_not_secondEntry hall hnew hse
  have hab := a_bot_of_not_secondEntry_one hn hall hnew ht hno hse
  rcases colOrb_dichotomy (F := F) ht with hc | ⟨n, -, hfix, hgfp, hmw, hwm⟩
  · exact hno hc
  have hpre : F ⊥ (F m (colOrb F m n)) ≤ F m (colOrb F m n) := feeder_le_side bot_le hfix
  have hwb : F m (colOrb F m n) ≠ ⊥ := fun e => hwm (e.le.trans bot_le)
  obtain ⟨i, hi1⟩ := exists_bot_descent_atom hn hk1 hab hpre hwb
  obtain ⟨z, hxz, hmz, hc⟩ := h m _ hk1 hall hmk hno hfix hgfp hmw i hi1
  have hxx := bot_iter_le hpre i
  rw [Function.iterate_succ_apply'] at hxx
  have hxR := mem_one_of_bot_value hn hi1 le_rfl hxx
  exact hmz ((cell_eq_of_not_secondEntry hn hall hse hxR hi1 hxz hc) ▸ le_rfl)

/-! ### The split IC3 + DeepFree (§34.3z²⁰⁸) -/

/-- **IC3 (conjectural).** Let `y` be the greatest post-fixed point of `y ↦ m ⊔ F m y` with `w = F m y ≱ m`, and let `x`
be a height-1 term of the bottom-row descent from `w` with `x ≰ m`. If every `z` with `F ⊥ z = ⊥` has height `≤ 1`, then
row `x` has an interval cell. Nothing else is assumed: no stage, no height of `m`, no `¬IC(m)`. No counterexample
(exact, `bare_rowcell.py ic3`, §34.3z²⁰⁸). -/
def IC3 (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ m y, (∀ z, F ⊥ z = ⊥ → height H z ≤ 1) → m ⊔ F m y = y → (∀ z, z ≤ m ⊔ F m z → z ≤ y) → ¬ m ≤ F m y →
    ∀ i, height H ((F ⊥)^[i] (F m y)) = 1 → ¬ (F ⊥)^[i] (F m y) ≤ m →
      ∃ z, (F ⊥)^[i] (F m y) < z ∧ (F ((F ⊥)^[i] (F m y)) z ≤ (F ⊥)^[i] (F m y) ∨ z ≤ F ((F ⊥)^[i] (F m y)) z)

/-- **DeepFree (conjectural).** With `R_2` tight, `h(m) = 2` and `¬IC(m)`, a height-1 term of the bottom-row descent from
`w = F m y*` that lies below `m` is the first term `F ⊥ w`. No counterexample (exact, `bare_rowcell.py deep`); it fails
without `¬IC(m)` (`|L| = 4`) and without `R_2` tightness (`|L| = 6`), §34.3z²⁰⁸. -/
def DeepFree (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ m y, (∀ z ∈ Rk F (1 + 1), height H z ≤ 1 + 1) → height H m = 1 + 1 → (¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) →
    m ⊔ F m y = y → (∀ z, z ≤ m ⊔ F m z → z ≤ y) → ¬ m ≤ F m y →
    ∀ i, height H ((F ⊥)^[i] (F m y)) = 1 → (F ⊥)^[i] (F m y) ≤ m → (F ⊥)^[i] (F m y) = F ⊥ (F m y)

/-- **IC3 and DeepFree give MinSecondEntry at k = 1.** Without a second top, take the height-1 descent term `x` from `w*`
(`exists_bot_descent_atom`), which lies in `R_1`. If `x ≰ m`, IC3 (with `F ⊥ z = ⊥ ⇒ z ∈ R_1`) gives a cell of `x`,
necessarily at `m` (`cell_eq_of_not_secondEntry`), so `x ≤ m`: contradiction. If `x ≤ m`, DeepFree makes `x = F ⊥ w*`, and
`upCell_of_bot_side_le_one` gives UpCell. -/
theorem secondEntry_one_of_IC3_deepFree [WellFoundedLT α] {H : ℕ} (hn : NoChain α (H + 1)) (h3 : IC3 F H)
    (hd : DeepFree F H) {m : α} (hall : ∀ z ∈ Rk F (1 + 1), height H z ≤ 1 + 1) (hmk : height H m = 1 + 1)
    (hnew : m ∉ Rk F 1) (ht : m ≠ ⊤) (hno : ¬ ∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) : SecondEntry F H 1 m := by
  by_contra hse
  have hk1 := tight_of_not_secondEntry hall hnew hse
  have hab := a_bot_of_not_secondEntry_one hn hall hnew ht hno hse
  have ht1b : ∀ z, F ⊥ z = ⊥ → height H z ≤ 1 := fun z hz =>
    hk1 z (mem_succ_of_cell (k := 0) (m := ⊥) (x := ⊥) (y := z) (show (⊥ : α) ∈ Set.Iic ⊥ from le_rfl) le_rfl
      (Or.inl hz.le))
  rcases colOrb_dichotomy (F := F) ht with hc | ⟨n, -, hfix, hgfp, hmw, hwm⟩
  · exact hno hc
  have hpre : F ⊥ (F m (colOrb F m n)) ≤ F m (colOrb F m n) := feeder_le_side bot_le hfix
  have hwb : F m (colOrb F m n) ≠ ⊥ := fun e => hwm (e.le.trans bot_le)
  obtain ⟨i, hi1⟩ := exists_bot_descent_atom hn hk1 hab hpre hwb
  have hxx := bot_iter_le hpre i
  rw [Function.iterate_succ_apply'] at hxx
  have hxR := mem_one_of_bot_value hn hi1 le_rfl hxx
  by_cases hxm : (F ⊥)^[i] (F m (colOrb F m n)) ≤ m
  · have he := hd m _ hall hmk hno hfix hgfp hmw i hi1 hxm
    rw [he] at hi1 hxm
    exact hse (secondEntry_of_upCell hn hall (upCell_of_bot_side_le_one hn hk1 hfix hmw hwm hi1 hxm))
  · obtain ⟨z, hxz, hc⟩ := h3 m _ ht1b hfix hgfp hmw i hi1 hxm
    have hzm := cell_eq_of_not_secondEntry hn hall hse hxR hi1 hxz hc
    exact hxm (hzm ▸ hxz.le)

/-! ### The IC-lemma: meet facts for a cell-free row (§34.3z²⁰⁹) -/

/-- A height-1 element meets anything it does not lie below in `⊥`. -/
theorem inf_eq_bot_of_height_one {H : ℕ} (hn : NoChain α (H + 1)) {x v : α} (hx1 : height H x = 1)
    (hxv : ¬ x ≤ v) : x ⊓ v = ⊥ := by
  by_contra h
  have h1 := height_strictMono hn (bot_lt_iff_ne_bot.2 h)
  have h2 := height_strictMono hn (lt_of_le_of_ne inf_le_left fun e => hxv (e.symm.le.trans inf_le_right))
  rw [height_bot_eq_zero] at h1; omega

/-- An element above a height-1 element `x` with height `≤ 1` is `x`. -/
theorem eq_of_le_height_one {H : ℕ} (hn : NoChain α (H + 1)) {x z : α} (hx1 : height H x = 1) (hxz : x ≤ z)
    (hz : height H z ≤ 1) : z = x := by
  by_contra hne
  have := height_strictMono hn (lt_of_le_of_ne hxz (Ne.symm hne)); omega

/-- **Meet facts for the IC-lemma.** Let `y = m ⊔ F m y`, `w = F m y`, `x = F ⊥ w` of height 1, and let `y_x = x ⊔ F x y_x`
be a column fixed point of `x` whose output `w_x = F x y_x` is not above `x` (as for a cell-free `x`). If `F ⊥ z = ⊥`
forces height `≤ 1` (T1b), then `w ⊓ y_x = x`, `w ⊓ w_x = ⊥` and `y ⊓ y_x = x`. Proof: `F ⊥` is bounded by `w` on `↓y`
and by `w_x` on `↓y_x`, and `x ⊓ w_x = ⊥`. No greatest-fixed-point property is used. -/
theorem icLemma_meets {H : ℕ} (hn : NoChain α (H + 1)) (ht1b : ∀ z, F ⊥ z = ⊥ → height H z ≤ 1) {m y yx : α}
    (hy : m ⊔ F m y = y) (hx1 : height H (F ⊥ (F m y)) = 1) (hyx : F ⊥ (F m y) ⊔ F (F ⊥ (F m y)) yx = yx)
    (hxw : ¬ F ⊥ (F m y) ≤ F (F ⊥ (F m y)) yx) :
    F m y ⊓ yx = F ⊥ (F m y) ∧ F m y ⊓ F (F ⊥ (F m y)) yx = ⊥ ∧ y ⊓ yx = F ⊥ (F m y) := by
  set w := F m y with hw
  set x := F ⊥ w with hxdef
  set wx := F x yx with hwx
  have hxw' : x ≤ w := feeder_le_side bot_le hy
  have hwy : w ≤ y := le_sup_right.trans hy.le
  have hxyx : x ≤ yx := le_sup_left.trans hyx.le
  have hwxyx : wx ≤ yx := le_sup_right.trans hyx.le
  have hxwx : x ⊓ wx = ⊥ := inf_eq_bot_of_height_one hn hx1 hxw
  have bY : ∀ z, z ≤ y → F ⊥ z ≤ w := fun z hz => ((F.mono bot_le) z).trans ((F m).mono hz)
  have bX : ∀ z, z ≤ yx → F ⊥ z ≤ wx := fun z hz => ((F.mono bot_le) z).trans ((F x).mono hz)
  -- (a) w ⊓ y_x = x
  have ha : w ⊓ yx = x := by
    have h0 : F ⊥ (w ⊓ yx) = ⊥ :=
      le_bot_iff.1 ((le_inf ((F ⊥).mono inf_le_left) (bX _ inf_le_right)).trans hxwx.le)
    exact eq_of_le_height_one hn hx1 (le_inf hxw' hxyx) (ht1b _ h0)
  -- (b) w ⊓ w_x = ⊥
  have hb : w ⊓ wx = ⊥ := by
    have h0 : F ⊥ (w ⊓ wx) = ⊥ :=
      le_bot_iff.1 ((le_inf ((F ⊥).mono inf_le_left) (bX _ (inf_le_right.trans hwxyx))).trans hxwx.le)
    have hc1 := ht1b _ h0
    have hle : x ⊔ w ⊓ wx ≤ x := (le_inf (sup_le hxw' inf_le_left) (sup_le hxyx (inf_le_right.trans hwxyx))).trans ha.le
    have hcx : w ⊓ wx ≤ x := le_sup_right.trans hle
    exact le_bot_iff.1 ((le_inf hcx inf_le_right).trans hxwx.le)
  -- (c) y ⊓ y_x = x
  have hc : y ⊓ yx = x := by
    have h0 : F ⊥ (y ⊓ yx) = ⊥ := le_bot_iff.1 ((le_inf (bY _ inf_le_left) (bX _ inf_le_right)).trans hb.le)
    exact eq_of_le_height_one hn hx1 (le_inf (hxw'.trans hwy) hxyx) (ht1b _ h0)
  exact ⟨ha, hb, hc⟩

/-- **Key lemma of the IC-lemma.** Let `x = F ⊥ w` have height 1, `F ⊥ w ≤ w`, and assume T1b (`F ⊥ z = ⊥` forces
height `≤ 1`). If row `x` has no interval cell, then it has no pre-fixed column `z > x` with `F ⊥ z ≤ w`. Proof: if
`x ≤ F x z`, descend to `F x z` (a cell unless `x < F x z < z`; `F ⊥` stays below `w`). Otherwise `x ⊓ F x z = ⊥`, so
`F ⊥ (w ⊓ z) ≤ x ⊓ F x z = ⊥` and T1b gives `w ⊓ z = x`; then `w ⊓ F x z ≤ x ⊓ F x z = ⊥`, so `F ⊥ z ≤ w ⊓ F x z = ⊥`,
and T1b contradicts `z > x`. No greatest-fixed-point property and no hypothesis on `m` is used. -/
theorem no_preColumn_of_cellFree {H : ℕ} (hn : NoChain α (H + 1)) (ht1b : ∀ z, F ⊥ z = ⊥ → height H z ≤ 1) {w : α}
    (hx1 : height H (F ⊥ w) = 1) (hpre : F ⊥ w ≤ w)
    (hcf : ¬ ∃ z, F ⊥ w < z ∧ (F (F ⊥ w) z ≤ F ⊥ w ∨ z ≤ F (F ⊥ w) z)) :
    ∀ (n : ℕ) {z : α}, height H z ≤ n → F ⊥ w < z → F (F ⊥ w) z ≤ z → F ⊥ z ≤ w → False
  | 0, z, hz, hxz, _, _ => by have := height_strictMono hn hxz; omega
  | n + 1, z, hz, hxz, hFz, hbz => by
      by_cases hxF : F ⊥ w ≤ F (F ⊥ w) z
      · by_cases h1 : F (F ⊥ w) z ≤ F ⊥ w
        · exact hcf ⟨z, hxz, Or.inl h1⟩
        by_cases h2 : z ≤ F (F ⊥ w) z
        · exact hcf ⟨z, hxz, Or.inr h2⟩
        have hlt : F (F ⊥ w) z < z := lt_of_le_not_ge hFz h2
        have := height_strictMono hn hlt
        exact no_preColumn_of_cellFree hn ht1b hx1 hpre hcf n (by omega) (lt_of_le_not_ge hxF h1)
          ((F (F ⊥ w)).mono hFz) (((F ⊥).mono hlt.le).trans hbz)
      · have hm := inf_eq_bot_of_height_one hn hx1 hxF
        have ha : w ⊓ z = F ⊥ w := by
          have h0 : F ⊥ (w ⊓ z) = ⊥ := le_bot_iff.1 ((le_inf ((F ⊥).mono inf_le_left)
            (((F.mono bot_le) _).trans ((F (F ⊥ w)).mono inf_le_right))).trans hm.le)
          exact eq_of_le_height_one hn hx1 (le_inf hpre hxz.le) (ht1b _ h0)
        have hc : w ⊓ F (F ⊥ w) z = ⊥ :=
          le_bot_iff.1 ((le_inf ((le_inf inf_le_left (inf_le_right.trans hFz)).trans ha.le) inf_le_right).trans hm.le)
        have h0 : F ⊥ z = ⊥ := le_bot_iff.1 ((le_inf hbz ((F.mono bot_le) z)).trans hc.le)
        have := ht1b z h0
        have := height_strictMono hn hxz; omega

/-- **The IC-lemma from a pre-fixed column.** Under T1b, with `x = F ⊥ w` of height 1 and `F ⊥ w ≤ w`, any pre-fixed
column `z > x` of row `x` with `F ⊥ z ≤ w` forces an interval cell of row `x`. -/
theorem ic_of_preColumn {H : ℕ} (hn : NoChain α (H + 1)) (ht1b : ∀ z, F ⊥ z = ⊥ → height H z ≤ 1) {w z : α}
    (hx1 : height H (F ⊥ w) = 1) (hpre : F ⊥ w ≤ w) (hxz : F ⊥ w < z) (hFz : F (F ⊥ w) z ≤ z) (hbz : F ⊥ z ≤ w) :
    ∃ z, F ⊥ w < z ∧ (F (F ⊥ w) z ≤ F ⊥ w ∨ z ≤ F (F ⊥ w) z) := by
  by_contra hcf
  exact no_preColumn_of_cellFree hn ht1b hx1 hpre hcf H (height_le _) hxz hFz hbz

/-- **The IC-lemma below `y`.** For `y = m ⊔ F m y`, `w = F m y` and `x = F ⊥ w` of height 1, under T1b, any pre-fixed
column of row `x` in `(x, y]` forces an interval cell of row `x` (`F ⊥ z ≤ F m z ≤ F m y`). In particular this holds when
`F x y ≤ y`, or when a column fixed point `y_x` of `x` lies below `y`. -/
theorem ic_of_preColumn_le {H : ℕ} (hn : NoChain α (H + 1)) (ht1b : ∀ z, F ⊥ z = ⊥ → height H z ≤ 1) {m y z : α}
    (hy : m ⊔ F m y = y) (hx1 : height H (F ⊥ (F m y)) = 1) (hxz : F ⊥ (F m y) < z) (hzy : z ≤ y)
    (hFz : F (F ⊥ (F m y)) z ≤ z) :
    ∃ z, F ⊥ (F m y) < z ∧ (F (F ⊥ (F m y)) z ≤ F ⊥ (F m y) ∨ z ≤ F (F ⊥ (F m y)) z) :=
  ic_of_preColumn hn ht1b hx1 (feeder_le_side bot_le hy) hxz hFz
    (((F.mono bot_le) z).trans ((F m).mono hzy))

/-- **The KL2 branch.** Under T1b, with `y = m ⊔ F m y`, `w = F m y`, `x = F ⊥ w` of height 1 and a column fixed point
`y_x = x ⊔ F x y_x` with `x ≰ F x y_x`: no `z > x` has `F ⊥ z ≤ w`, `F x z ≤ y_x` and `x ≰ F x z`. For
`F ⊥ z ≤ w ⊓ F x z ≤ w ⊓ y_x = x` (`icLemma_meets`) and `x ⊓ F x z = ⊥`, so `F ⊥ z = ⊥`, against T1b. -/
theorem no_kl2Column {H : ℕ} (hn : NoChain α (H + 1)) (ht1b : ∀ z, F ⊥ z = ⊥ → height H z ≤ 1) {m y yx z : α}
    (hy : m ⊔ F m y = y) (hx1 : height H (F ⊥ (F m y)) = 1) (hyx : F ⊥ (F m y) ⊔ F (F ⊥ (F m y)) yx = yx)
    (hxw : ¬ F ⊥ (F m y) ≤ F (F ⊥ (F m y)) yx) (hxz : F ⊥ (F m y) < z) (hbz : F ⊥ z ≤ F m y)
    (hzy : F (F ⊥ (F m y)) z ≤ yx) (hxF : ¬ F ⊥ (F m y) ≤ F (F ⊥ (F m y)) z) : False := by
  obtain ⟨ha, -, -⟩ := icLemma_meets hn ht1b hy hx1 hyx hxw
  have hb : F ⊥ z ≤ F (F ⊥ (F m y)) z := (F.mono bot_le) z
  have h1 : F ⊥ z ≤ F ⊥ (F m y) := (le_inf hbz (hb.trans hzy)).trans ha.le
  have h0 : F ⊥ z = ⊥ := le_bot_iff.1 ((le_inf h1 hb).trans (inf_eq_bot_of_height_one hn hx1 hxF).le)
  have := ht1b z h0
  have := height_strictMono hn hxz; omega

/-- **KL2E (conjectural; no T1b).** For `y*` the greatest post-fixed point of `y ↦ m ⊔ F m y` with `w = F m y* ≱ m`,
`x = F ⊥ w` of height 1 with `x ≰ m`, and `y_x` the greatest post-fixed point of `y ↦ x ⊔ F x y` with `x ≰ F x y_x`: if
row `x` has no interval cell, some `z > x` with `F ⊥ z ≤ w` has `F x z ≤ z` or (`F x z ≤ y_x` and `x ≰ F x z`). No
counterexample (exact, `bare_rowcell.py kl2`: sweep 184, closures 28, §34.3z²¹⁰). The canonical choices `z ∈ {w, F x w}` and
`z` on the column orbit of `x` are refuted (`|L| = 8`, `9`). -/
def KL2E (F : α →o α →o α) (H : ℕ) : Prop :=
  ∀ m y yx, m ⊔ F m y = y → (∀ z, z ≤ m ⊔ F m z → z ≤ y) → ¬ m ≤ F m y → height H (F ⊥ (F m y)) = 1 →
    ¬ F ⊥ (F m y) ≤ m → F ⊥ (F m y) ⊔ F (F ⊥ (F m y)) yx = yx →
    (∀ z, z ≤ F ⊥ (F m y) ⊔ F (F ⊥ (F m y)) z → z ≤ yx) → ¬ F ⊥ (F m y) ≤ F (F ⊥ (F m y)) yx →
    (¬ ∃ z, F ⊥ (F m y) < z ∧ (F (F ⊥ (F m y)) z ≤ F ⊥ (F m y) ∨ z ≤ F (F ⊥ (F m y)) z)) →
    ∃ z, F ⊥ (F m y) < z ∧ F ⊥ z ≤ F m y ∧
      (F (F ⊥ (F m y)) z ≤ z ∨ (F (F ⊥ (F m y)) z ≤ yx ∧ ¬ F ⊥ (F m y) ≤ F (F ⊥ (F m y)) z))

/-- **KL2E gives the IC-lemma.** Under T1b, with `y*`, `w`, `x = F ⊥ w` as in `KL2E`, row `x` has an interval cell: if
not, `colOrb_dichotomy` gives `y_x`, KL2E gives a column, and both kinds are excluded (`no_preColumn_of_cellFree`,
`no_kl2Column`). -/
theorem ic_of_KL2E [WellFoundedLT α] {H : ℕ} (hn : NoChain α (H + 1)) (hk : KL2E F H)
    (ht1b : ∀ z, F ⊥ z = ⊥ → height H z ≤ 1) {m y : α} (hy : m ⊔ F m y = y) (hgfp : ∀ z, z ≤ m ⊔ F m z → z ≤ y)
    (hmw : ¬ m ≤ F m y) (hx1 : height H (F ⊥ (F m y)) = 1) (hxm : ¬ F ⊥ (F m y) ≤ m) :
    ∃ z, F ⊥ (F m y) < z ∧ (F (F ⊥ (F m y)) z ≤ F ⊥ (F m y) ∨ z ≤ F (F ⊥ (F m y)) z) := by
  by_contra hcf
  have hpre : F ⊥ (F m y) ≤ F m y := feeder_le_side bot_le hy
  have hxt : F ⊥ (F m y) ≠ ⊤ := fun e => hmw (le_top.trans (e ▸ hpre))
  rcases colOrb_dichotomy (F := F) hxt with hc | ⟨n, -, hfix, hg, hxw, -⟩
  · exact hcf hc
  obtain ⟨z, hxz, hbz, hz | ⟨hzy, hxF⟩⟩ := hk m y _ hy hgfp hmw hx1 hxm hfix hg hxw hcf
  · exact no_preColumn_of_cellFree hn ht1b hx1 hpre hcf H (height_le _) hxz hz hbz
  · exact no_kl2Column hn ht1b hy hx1 hfix hxw hxz hbz hzy hxF

/-- **The KL3 column (general form).** Under T1b, with `x = F ⊥ w` of height 1, no `z > x` has `F ⊥ z ≤ w`,
`x ≰ F x z` and `w ⊓ F x z ≤ x`: then `F ⊥ z ≤ w ⊓ F x z ≤ x` and `F ⊥ z ≤ F x z`, so `F ⊥ z ≤ x ⊓ F x z = ⊥`. The KL2 column
(`F x z ≤ y_x`, via `w ⊓ y_x = x`) and the second branch of the key lemma (`F x z ≤ z`, via `w ⊓ z = x`) are instances. -/
theorem no_kl3Column {H : ℕ} (hn : NoChain α (H + 1)) (ht1b : ∀ z, F ⊥ z = ⊥ → height H z ≤ 1) {w z : α}
    (hx1 : height H (F ⊥ w) = 1) (hxz : F ⊥ w < z) (hbz : F ⊥ z ≤ w) (hxF : ¬ F ⊥ w ≤ F (F ⊥ w) z)
    (hwF : w ⊓ F (F ⊥ w) z ≤ F ⊥ w) : False := by
  have hb : F ⊥ z ≤ F (F ⊥ w) z := (F.mono bot_le) z
  have h0 : F ⊥ z = ⊥ :=
    le_bot_iff.1 ((le_inf ((le_inf hbz hb).trans hwF) hb).trans (inf_eq_bot_of_height_one hn hx1 hxF).le)
  have := ht1b z h0
  have := height_strictMono hn hxz; omega

/-- A monotone self-map's iteration from a pre-fixed point stabilizes (finite edge-height). -/
theorem exists_iter_fix_mono {H : ℕ} (hn : NoChain α (H + 1)) {φ : α → α} (hφ : Monotone φ) :
    ∀ (k : ℕ) {v : α}, height H v ≤ k → φ v ≤ v → ∃ N, φ (φ^[N] v) = φ^[N] v
  | 0, v, hv, hφv => by
      refine ⟨0, le_antisymm hφv ?_⟩
      by_contra hne
      have := height_strictMono hn (lt_of_le_not_ge hφv hne); omega
  | k + 1, v, hv, hφv => by
      by_cases he : φ v = v
      · exact ⟨0, he⟩
      have hlt : φ v < v := lt_of_le_of_ne hφv he
      have := height_strictMono hn hlt
      obtain ⟨N, hN⟩ := exists_iter_fix_mono hn hφ k (by omega) (hφ hφv)
      exact ⟨N + 1, by rw [Function.iterate_succ_apply]; exact hN⟩

/-- **The gap configuration.** Under T1b, let `y = m ⊔ F m y`, `w = F m y ≱ m`, `x = F ⊥ w` of height 1 with `x ≰ m`,
and let `y_x = x ⊔ F x y_x` be the greatest post-fixed point of `u ↦ x ⊔ F x u` with `x ≰ F x y_x` (as for a cell-free
`x`). Then some `v` with `x < v ≤ y` has `F ⊥ v = x`, `x ≤ F x v` and `y ⊓ F x v = x`. Proof: the descent
`u ↦ y ⊓ (x ⊔ F x u)` from `y` stabilizes at a post-fixed point of `u ↦ x ⊔ F x u`, hence below `y ⊓ y_x = x`
(`icLemma_meets`); at its last step above `x`, `F ⊥ v ≤ w ⊓ (x ⊔ F x v) ≤ x`, and T1b excludes `F ⊥ v = ⊥`. So the
IC-lemma for such `x` is equivalent to the impossibility of this configuration. -/
theorem exists_gap {H : ℕ} (hn : NoChain α (H + 1)) (ht1b : ∀ z, F ⊥ z = ⊥ → height H z ≤ 1) {m y yx : α}
    (hy : m ⊔ F m y = y) (hmw : ¬ m ≤ F m y) (hx1 : height H (F ⊥ (F m y)) = 1) (hxm : ¬ F ⊥ (F m y) ≤ m)
    (hyx : F ⊥ (F m y) ⊔ F (F ⊥ (F m y)) yx = yx) (hgx : ∀ z, z ≤ F ⊥ (F m y) ⊔ F (F ⊥ (F m y)) z → z ≤ yx)
    (hxw : ¬ F ⊥ (F m y) ≤ F (F ⊥ (F m y)) yx) :
    ∃ v, F ⊥ (F m y) < v ∧ v ≤ y ∧ F ⊥ v = F ⊥ (F m y) ∧ F ⊥ (F m y) ≤ F (F ⊥ (F m y)) v ∧
      y ⊓ F (F ⊥ (F m y)) v = F ⊥ (F m y) := by
  classical
  set w := F m y with hw
  set x := F ⊥ w with hxdef
  obtain ⟨-, -, hc⟩ := icLemma_meets hn ht1b hy hx1 hyx hxw
  have hxw' : x ≤ w := feeder_le_side bot_le hy
  have hwy : w ≤ y := le_sup_right.trans hy.le
  have hxy : x ≤ y := hxw'.trans hwy
  let φ : α → α := fun u => y ⊓ (x ⊔ F x u)
  have hφ : Monotone φ := fun a b hab => inf_le_inf_left _ (sup_le_sup_left ((F x).mono hab) _)
  have hφy : ∀ u, φ u ≤ y := fun u => inf_le_left
  have hxφ : ∀ u, x ≤ φ u := fun u => le_inf hxy le_sup_left
  have hiy : ∀ i, φ^[i] y ≤ y := fun i => by
    cases i with
    | zero => exact le_rfl
    | succ i => rw [Function.iterate_succ_apply']; exact hφy _
  have hix : ∀ i, x ≤ φ^[i] y := fun i => by
    cases i with
    | zero => exact hxy
    | succ i => rw [Function.iterate_succ_apply']; exact hxφ _
  obtain ⟨N, hN⟩ := exists_iter_fix_mono hn hφ H (height_le _) (hφy y)
  -- the limit is post-fixed for `u ↦ x ⊔ F x u`, hence `≤ y ⊓ y_x = x`
  have hlim : φ^[N] y ≤ x := by
    have h1 : φ^[N] y ≤ x ⊔ F x (φ^[N] y) := hN.symm.le.trans inf_le_right
    exact hc.le.trans' (le_inf (hiy N) (hgx _ h1))
  have hex : ∃ i, φ^[i] y ≤ x := ⟨N, hlim⟩
  obtain ⟨j, hj, hmin⟩ : ∃ j, φ^[j] y ≤ x ∧ ∀ i < j, ¬ φ^[i] y ≤ x :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hyx' : ¬ y ≤ x := by
    intro h
    have hmx : m ≤ x := le_sup_left.trans (hy.le.trans h)
    rcases eq_or_lt_of_le hmx with e | hlt
    · exact hxm e.ge
    · have := height_strictMono hn hlt
      have hm0 : m = ⊥ := by
        by_contra hne
        have := height_strictMono hn (bot_lt_iff_ne_bot.2 hne); rw [height_bot_eq_zero] at this; omega
      exact hmw (hm0 ▸ bot_le)
  rcases j with _ | i
  · exact absurd hj hyx'
  set v := φ^[i] y with hv
  have hvx : ¬ v ≤ x := hmin i (Nat.lt_succ_self i)
  have hxv : x < v := lt_of_le_not_ge (hix i) hvx
  have hφv : φ v ≤ x := by rw [hv, ← Function.iterate_succ_apply' φ i y]; exact hj
  have hvy : v ≤ y := hiy i
  have hbv : F ⊥ v ≤ x := by
    have h1 : F ⊥ v ≤ w := ((F.mono bot_le) v).trans ((F m).mono hvy)
    exact (le_inf (h1.trans hwy) (((F.mono bot_le) v).trans le_sup_right)).trans hφv
  have hbx : F ⊥ v = x := by
    by_contra hne
    have hlt : F ⊥ v < x := lt_of_le_of_ne hbv hne
    have h3 := height_strictMono hn hlt
    have h0 : F ⊥ v = ⊥ := by
      by_contra h0
      have := height_strictMono hn (bot_lt_iff_ne_bot.2 h0); rw [height_bot_eq_zero] at this; omega
    have := ht1b v h0
    have := height_strictMono hn hxv; omega
  have hxF : x ≤ F x v := hbx.symm.le.trans ((F.mono bot_le) v)
  refine ⟨v, hxv, hvy, hbx, hxF, le_antisymm ?_ (le_inf hxy hxF)⟩
  exact (inf_le_inf_left _ le_sup_right).trans hφv

/-- At the terminal index a top with any outgoing top edge (to stage `k + 1`) is good (`upCell_of_topEdge` locally). -/
theorem good_term_of_topEdge {H k : ℕ} {m c y : α} (he : TopEdge F H (k - 1) m c y) : Good F H k m (k - 1) c := by
  refine .term ?_
  rcases he with ⟨-, -, -, -, -, hcy, hcyc, v, hyv, hmv, -⟩ | ⟨-, -, hcy, hU, hmy, -⟩
  · exact ⟨y, hcy, fun hmy => hmv (hmy.trans hyv.le), Or.inl hcyc.le⟩
  · exact ⟨y, hcy, hmy, Or.inr hU⟩

end Mordor.OrbitHeight
