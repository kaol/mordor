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

end Mordor.OrbitHeight
