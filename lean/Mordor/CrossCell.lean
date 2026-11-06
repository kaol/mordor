import Mordor.AxisCapture

/-!
# Cross cells of a mixed pivot (round 26, §34.3z¹¹⁸)

ChatGPT brief "cross-cell closure and boundary interaction", Work Package A/B.

Outside points `xᵢ ∉ D` (`i ∈ S`, `S` nonempty), `c = ⋀_S x ∈ D`, a row `q ∈ D` with `c ≤ q`, and `y = ⋁_S x`.

* `sup_not_mem`: `y ∉ D`.
* `cross_rectangle_bounds`: `F(c, xᵢ) ≤ F(c, y) ≤ F(q, y)`, `F(q, xᵢ) ≤ F(q, y)`, and no witness at `(c, y)`, `(q, y)`.
* `cross_envelope_escape`: some `i₀ ∈ S` has `x_{i₀} ≰ F(q, y)`, hence `x_{i₀} ≰ F(c, xᵢ)` and `x_{i₀} ≰ F(q, xᵢ)` for all
  `i ∈ S`. Only the cell `(q, y)` and monotonicity are used; maximality of `q` is not.
* `meet_side_escape` (row-side dual): for every outside `z`, some `i₁ ∈ S` has `F(c, z) ≰ x_{i₁}`.
* `cross_output_boundary_extension` (B): `z = F(q, x)` with `q` maximal and `x ∉ D` is either in `D` and below a
  maximal `q' ∈ D` incomparable with `q`, or outside `D` and above a minimal `w ∉ D` with `x ≰ w`.
* `blind_two_point_form` (A3): for a minimal-support mixed pivot (`|S| ≥ 2`, `xᵢ = uᵢ(tᵢ)`) and the blind coordinate
  `i₀`, the complementary partial meet `c' = ⋀_{S∖{i₀}} x` lies outside `D`, `x_{i₀} ⊓ c' = c`, and
  `x_{i₀} ≰ F(q, x_{i₀} ⊔ c')`: the pivot is a two-point meet of outside elements whose blind side escapes the
  response at their join.
-/

namespace Mordor.CrossCell
open Finset Mordor.BoundedSupport

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [DecidableEq ι] {F : α → α → α}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set α}
  (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
  (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hD in
theorem sup_not_mem {S : Finset ι} (hS : S.Nonempty) {x : ι → α} (hx : ∀ i ∈ S, x i ∉ D) : S.sup x ∉ D := by
  obtain ⟨i, hi⟩ := hS
  exact fun h => hx i hi (hD _ _ (Finset.le_sup hi) h)

include hF hD nw in
theorem cross_rectangle_bounds {S : Finset ι} (hS : S.Nonempty) {x : ι → α} (hx : ∀ i ∈ S, x i ∉ D) {c q : α}
    (hc : c ∈ D) (hq : q ∈ D) (hcq : c ≤ q) :
    (∀ i ∈ S, F c (x i) ≤ F c (S.sup x) ∧ F q (x i) ≤ F q (S.sup x)) ∧ F c (S.sup x) ≤ F q (S.sup x) ∧
    (¬ F c (S.sup x) ≤ c ∧ ¬ S.sup x ≤ F c (S.sup x)) ∧ (¬ F q (S.sup x) ≤ q ∧ ¬ S.sup x ≤ F q (S.sup x)) := by
  have hy := sup_not_mem hD hS hx
  exact ⟨fun i hi => ⟨hF _ _ _ _ le_rfl (Finset.le_sup hi), hF _ _ _ _ le_rfl (Finset.le_sup hi)⟩,
    hF _ _ _ _ hcq le_rfl, nw _ hc _ hy, nw _ hq _ hy⟩

include hF hD nw in
/-- **The cross-envelope lemma.** -/
theorem cross_envelope_escape {S : Finset ι} (hS : S.Nonempty) {x : ι → α} (hx : ∀ i ∈ S, x i ∉ D) {c q : α}
    (hc : c ∈ D) (hq : q ∈ D) (hcq : c ≤ q) :
    ∃ i₀ ∈ S, ¬ x i₀ ≤ F q (S.sup x) ∧ ∀ i ∈ S, ¬ x i₀ ≤ F c (x i) ∧ ¬ x i₀ ≤ F q (x i) := by
  obtain ⟨hcol, hAB, -, -, hyB⟩ := cross_rectangle_bounds hF hD nw hS hx hc hq hcq
  have : ∃ i₀ ∈ S, ¬ x i₀ ≤ F q (S.sup x) := by
    by_contra h; push_neg at h; exact hyB (Finset.sup_le h)
  obtain ⟨i₀, hi₀, hesc⟩ := this
  exact ⟨i₀, hi₀, hesc, fun i hi => ⟨fun h => hesc (h.trans ((hcol i hi).1.trans hAB)),
    fun h => hesc (h.trans (hcol i hi).2)⟩⟩

include nw in
/-- **Row-side dual.** Since `c` is the meet of the `xᵢ`, every outside response of `c` escapes some coordinate. -/
theorem meet_side_escape {S : Finset ι} {x : ι → α} (hc : S.inf x ∈ D) {z : α} (hz : z ∉ D) :
    ∃ i ∈ S, ¬ F (S.inf x) z ≤ x i := by
  by_contra h; push_neg at h; exact (nw _ hc _ hz).1 (Finset.le_inf h)

include hD nw in
/-- **Boundary extension of a cross output** (B). -/
theorem cross_output_boundary_extension [WellFoundedLT α] [WellFoundedGT α] {q x : α} (hq : q ∈ D)
    (hmax : ∀ r ∈ D, q ≤ r → r = q) (hx : x ∉ D) :
    (F q x ∈ D ∧ ∃ q' ∈ D, F q x ≤ q' ∧ (∀ r ∈ D, q' ≤ r → r = q') ∧ ¬ q' ≤ q ∧ ¬ q ≤ q') ∨
    (F q x ∉ D ∧ ∃ w ∉ D, w ≤ F q x ∧ (∀ v ∉ D, v ≤ w → v = w) ∧ ¬ x ≤ w) := by
  obtain ⟨hzq, hxz⟩ := nw q hq x hx
  by_cases hz : F q x ∈ D
  · obtain ⟨q', hq', hzq', hmax'⟩ := Mordor.InfCapture.exists_maximal_above (D := D) hz
    refine Or.inl ⟨hz, q', hq', hzq', hmax', fun h => hzq (hzq'.trans h), fun h => ?_⟩
    exact hzq (hzq'.trans (hmax q' hq' h).le)
  · obtain ⟨w, hw, hwz, hmin⟩ := Mordor.InfCapture.exists_minimal_below (D := D) hz
    exact Or.inr ⟨hz, w, hw, hwz, hmin, fun h => hxz (h.trans hwz)⟩

include hF hD nw in
/-- **Two-point form at the blind coordinate** (A3). -/
theorem blind_two_point_form {k : ℕ} (g : Fin k → α) {v : Fin k → α} {S : Finset (Fin k)}
    (hP : Good (D := D) g (S.inf v)) (hmin : ∀ S' ⊂ S, ¬ Good (D := D) g (S'.inf v)) (h2 : 2 ≤ S.card)
    {q : α} (hq : q ∈ D) (hcq : S.inf v ≤ q) :
    ∃ i₀ ∈ S, (S.erase i₀).inf v ∉ D ∧ v i₀ ⊓ (S.erase i₀).inf v = S.inf v ∧
      ¬ v i₀ ≤ F q (v i₀ ⊔ (S.erase i₀).inf v) ∧ ∀ i ∈ S, ¬ v i₀ ≤ F q (v i) := by
  have hS : S.Nonempty := Finset.card_pos.1 (by omega)
  have hout : ∀ i ∈ S, v i ∉ D := fun i hi => by
    have hss : ({i} : Finset (Fin k)) ⊂ S :=
      Finset.ssubset_iff_subset_ne.2 ⟨Finset.singleton_subset_iff.2 hi, fun h => by
        rw [← h, Finset.card_singleton] at h2; omega⟩
    simpa using proper_partial_meet_outside g hP hmin hss
  obtain ⟨i₀, hi₀, hesc, hall⟩ := cross_envelope_escape hF hD nw hS hout hP.1 hq hcq
  have hss : S.erase i₀ ⊂ S := Finset.erase_ssubset hi₀
  refine ⟨i₀, hi₀, proper_partial_meet_outside g hP hmin hss, ?_, ?_, fun i hi => (hall i hi).2⟩
  · rw [← Finset.inf_insert, Finset.insert_erase hi₀]
  · intro h
    refine hesc (h.trans (hF _ _ _ _ le_rfl (sup_le (Finset.le_sup hi₀) ?_)))
    obtain ⟨j, hj⟩ : (S.erase i₀).Nonempty := Finset.card_pos.1 (by rw [Finset.card_erase_of_mem hi₀]; omega)
    exact (Finset.inf_le hj).trans (Finset.le_sup (Finset.mem_of_mem_erase hj))

end Mordor.CrossCell
