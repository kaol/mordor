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

end Mordor.OrbitHeight
