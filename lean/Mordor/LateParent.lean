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

end Mordor.OrbitHeight
