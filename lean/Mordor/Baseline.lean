import Mordor.Envelope

/-!
# The independent row-orbit baseline (round 26, §34.3z⁹⁰)

Response to the brief "independent row-orbit baseline".

* `independent_row_baseline` (DCC): the `F pⱼ`-orbit of `⊤` enters `D` from a last point `v` with
  `H = F pⱼ v ∈ D`, `H ≰ pⱼ`, and `v` is **`pⱼ`-contracting** (`H ≤ v`, the orbit descends). For every `x` and every
  generator `k` above `H`, the pair row value `b = F (pₓ ⊓ pⱼ) v ≤ H ≤ pₖ`; for two generators `k = x`, and
  `b ≰ pⱼ` (no witness at `m`).
* `opposite_label_diamond`: two outside columns `t, v` whose `m = pₓ ⊓ p_y` values are oppositely labelled
  (`e ≤ p_y`, `e ≰ pₓ`, `b ≤ pₓ`, `b ≰ p_y`) are incomparable, meet in `D` (`lastpoint_meet`), and
  `e ⊔ b ≤ F m (t ⊔ v)` with `e ⊔ b` below no `pₓ`, `p_y`.
* `pair_triangle`, `common_column_exit`: pair states `(i,j)` and `(j,k)` at a common column `z` cannot be completed
  by `(k,i)` (the triple meet row would be below itself), so for three generators `F p_k z ∉ D`: switching at `z`
  stops after one step and `switch_terminal` continues by clipped descent.
* `baseline_meet_cone`: the baseline column transfers for `j` (`F cⱼ v ≤ H`), so on a sink cone of `j` the meet
  `t ⊓ v` with any cone column lies in `D`.
* Since `v` is `pⱼ`-contracting, `SinkCone.noContract` keeps it out of every sink cone of `j`: the three-generator
  continuation of this baseline lives outside the region where the crossing case is open.
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF nw in
/-- **The independent generator-row baseline.** -/
theorem independent_row_baseline [WellFoundedLT α] (htop : ¬ ∃ i, ⊤ ≤ p i) (j : ι) :
    ∃ v k, (¬ ∃ i, v ≤ p i) ∧ F (p j) v ≤ v ∧ F (p j) v ≤ p k ∧ k ≠ j ∧
      ∀ x, F (p x ⊓ p j) v ≤ p k ∧ ¬ F (p x ⊓ p j) v ≤ p x ⊓ p j := by
  have hmono : Monotone (F (p j)) := fun _ _ h => hF _ _ _ _ le_rfl h
  obtain ⟨n, hU, k, hk⟩ := FGTwo.orbit_end (InD := fun x => ∃ i, x ≤ p i) hF ⟨j, le_rfl⟩ nw ⊤ htop le_top
  have hanti := Monotone.antitone_iterate_of_map_le hmono (le_top : F (p j) ⊤ ≤ ⊤)
  have hv := hU n le_rfl
  have hcon : F (p j) ((F (p j))^[n] ⊤) ≤ (F (p j))^[n] ⊤ := by
    rw [← Function.iterate_succ_apply' (F (p j)) n ⊤]; exact hanti (Nat.le_succ n)
  have hkj : k ≠ j := fun e => (nw _ ⟨j, le_rfl⟩ _ hv).1 (e ▸ hk)
  exact ⟨_, k, hv, hcon, hk, hkj, fun x =>
    ⟨(hF _ _ _ _ inf_le_right le_rfl).trans hk, (nw _ ⟨x, inf_le_left⟩ _ hv).1⟩⟩

include hF nw in
/-- **The opposite-label diamond.** -/
theorem opposite_label_diamond {x y : ι} {t v : α} (ht : ¬ ∃ i, t ≤ p i)
    (he : F (p x ⊓ p y) t ≤ p y) (he' : ¬ F (p x ⊓ p y) t ≤ p x)
    (hb : F (p x ⊓ p y) v ≤ p x) (hb' : ¬ F (p x ⊓ p y) v ≤ p y) :
    ¬ t ≤ v ∧ ¬ v ≤ t ∧ (∃ k, t ⊓ v ≤ p k) ∧ (¬ ∃ k, t ⊔ v ≤ p k) ∧
      F (p x ⊓ p y) t ⊔ F (p x ⊓ p y) v ≤ F (p x ⊓ p y) (t ⊔ v) ∧
      ¬ F (p x ⊓ p y) t ⊔ F (p x ⊓ p y) v ≤ p x ∧ ¬ F (p x ⊓ p y) t ⊔ F (p x ⊓ p y) v ≤ p y := by
  have hm : Monotone (F (p x ⊓ p y)) := fun _ _ h => hF _ _ _ _ le_rfl h
  refine ⟨fun h => he' ((hm h).trans hb), fun h => hb' ((hm h).trans he), ?_, fun ⟨k, hk⟩ => ht ⟨k, le_sup_left.trans hk⟩,
    sup_le (hm le_sup_left) (hm le_sup_right), fun h => he' (le_sup_left.trans h), fun h => hb' (le_sup_right.trans h)⟩
  have := lastpoint_meet hF p nw (i := x) (j := y) (ws := v) (wt := t) hb he
  obtain ⟨k, hk⟩ := this
  exact ⟨k, (inf_comm t v) ▸ hk⟩

include hF nw in
/-- **No pair-state triangle at one column.** -/
theorem pair_triangle {i j k : ι} {z : α} (hz : ¬ ∃ l, z ≤ p l) (h1 : F (p i ⊓ p j) z ≤ p j)
    (h2 : F (p j ⊓ p k) z ≤ p k) (h3 : F (p k ⊓ p i) z ≤ p i) : False := by
  have hb : p i ⊓ p j ⊓ p k ≤ p i ⊓ p j := inf_le_left
  have hb2 : p i ⊓ p j ⊓ p k ≤ p j ⊓ p k := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hb3 : p i ⊓ p j ⊓ p k ≤ p k ⊓ p i := le_inf inf_le_right (inf_le_left.trans inf_le_left)
  have hle : F (p i ⊓ p j ⊓ p k) z ≤ p i ⊓ p j ⊓ p k :=
    le_inf (le_inf ((hF _ _ _ _ hb3 le_rfl).trans h3) ((hF _ _ _ _ hb le_rfl).trans h1))
      ((hF _ _ _ _ hb2 le_rfl).trans h2)
  exact (nw _ ⟨i, inf_le_left.trans inf_le_left⟩ z hz).1 hle

include hF nw in
/-- **At a common column the switch from `(j, k)` must leave `D`** (three generators). -/
theorem common_column_exit {i j k : ι} (hall : ∀ l, l = i ∨ l = j ∨ l = k) {z : α} (hz : ¬ ∃ l, z ≤ p l)
    (h1 : F (p i ⊓ p j) z ≤ p j) (h2 : F (p j ⊓ p k) z ≤ p k) : ¬ ∃ l, F (p k) z ≤ p l := by
  rintro ⟨l, hl⟩
  obtain ⟨hx, hy, -⟩ := switched_row_escape hF p nw hz h2
  rcases hall l with rfl | rfl | rfl
  · exact pair_triangle hF p nw hz h1 h2 ((hF _ _ _ _ inf_le_left le_rfl).trans hl)
  · exact hx hl
  · exact hy hl

include hF in
/-- The baseline column transfers for `j`; so on a sink cone of `j` everything below it is in `D`. -/
theorem baseline_meet_cone {u₀ v : α} {j k : ι} (hC : SinkCone F p u₀ j) (hv : ¬ ∃ i, v ≤ p i)
    (hH : F (p j) v ≤ p k) (hkj : k ≠ j) : ∀ x, x ≤ v → x ≤ u₀ → ∃ i, x ≤ p i := by
  intro x hxv hxu
  by_contra hx
  exact hC.noTransfer x hxu (transfer_down hF p hxv hx
    ⟨hv, k, hkj, (hF _ _ _ _ (anchor_le p j) le_rfl).trans hH⟩)

end Mordor.Profile
