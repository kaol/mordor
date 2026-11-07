import Mordor.FiniteQuotient

/-!
# Extremal separators (round 26, §34.3z¹²⁰)

ChatGPT brief "finite separators and boundary uniformization", Work Package A1–A2.

For a cross pair `(x, y)` (`x ∈ D`, `y ∉ D`) of a witness-free `F`:
* `exists_upper_separator` (ACC): some `s ≥ F x y` with `y ≰ s` and `y ≤ t` for every `t > s`.
* `exists_lower_separator` (DCC): some `s ≤ F x y` with `s ≰ x` and `t ≤ x` for every `t < s`.
* `upper_separator_iff`: `s` is a maximal upper separator of `(x, y)` iff `F x y ≤ s` and `s` is maximal in
  `V(y) = {s | y ≰ s}` — the separator depends on `x` only through the constraint `F x y ≤ s`.
* `upper_separator_inf_irreducible`, `upper_separator_cover`: a maximal element of `V(y)` is ⊓-irreducible
  (`s = a ⊓ b ⇒ s = a ∨ s = b`), and every `t > s` lies above `s ⊔ y > s` (unique upper cover direction).
  Duals: `lower_separator_sup_irreducible`, `lower_separator_cover`.
* `upper_separator_mono_col`: a separator for `y₀` separates every `y ≥ y₀` (`y₀ ≰ s ⇒ y ≰ s`).
* `common_separator_iff` / `common_lower_separator_iff` (A4): finitely many pairs share one landmark iff the join of
  their responses lies above none of their columns (dually: the meet below none of their rows). The brief's "Case 2"
  (every `y_α ≤ ⋁ S₀`) is exactly the failure of this criterion for the recorded pairs.
* `separated_iff_cl` / `dual_separated_iff_int` (A2): for a finite meet-closed `T ∋ ⊤`, the pair is separated by `T`
  iff `y ≰ cl_T (F x y)`; dually for join-closed `T ∋ ⊥`, iff `int_T (F x y) ≰ x`.
-/

namespace Mordor.ExtremalSeparators
open Finset Mordor.FiniteQuotient

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] {F : α → α → α} {D : Set α}
  (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include nw in
/-- **Extremal upper separator** (ACC). -/
theorem exists_upper_separator [WellFoundedGT α] {x y : α} (hx : x ∈ D) (hy : y ∉ D) :
    ∃ s, F x y ≤ s ∧ ¬ y ≤ s ∧ ∀ t, s < t → y ≤ t := by
  obtain ⟨s, ⟨hFs, hys⟩, hmax⟩ := (wellFounded_gt (α := α)).has_min {s | F x y ≤ s ∧ ¬ y ≤ s}
    ⟨F x y, le_rfl, (nw x hx y hy).2⟩
  refine ⟨s, hFs, hys, fun t hst => ?_⟩
  by_contra hyt
  exact hmax t ⟨hFs.trans hst.le, hyt⟩ hst

include nw in
/-- **Extremal lower separator** (DCC). -/
theorem exists_lower_separator [WellFoundedLT α] {x y : α} (hx : x ∈ D) (hy : y ∉ D) :
    ∃ s, s ≤ F x y ∧ ¬ s ≤ x ∧ ∀ t, t < s → t ≤ x := by
  obtain ⟨s, ⟨hsF, hsx⟩, hmin⟩ := (wellFounded_lt (α := α)).has_min {s | s ≤ F x y ∧ ¬ s ≤ x}
    ⟨F x y, le_rfl, (nw x hx y hy).1⟩
  refine ⟨s, hsF, hsx, fun t hts => ?_⟩
  by_contra htx
  exact hmin t ⟨hts.le.trans hsF, htx⟩ hts

/-- A maximal upper separator is exactly a maximal element of `V(y)` above `F x y`. -/
theorem upper_separator_iff {z y s : α} :
    (z ≤ s ∧ ¬ y ≤ s ∧ ∀ t, s < t → y ≤ t) ↔
    (z ≤ s ∧ ¬ y ≤ s ∧ ∀ t, ¬ y ≤ t → s ≤ t → t = s) := by
  constructor
  · rintro ⟨hz, hy, hmax⟩
    exact ⟨hz, hy, fun t hyt hst => by
      by_contra hne; exact hyt (hmax t (lt_of_le_of_ne hst (Ne.symm hne)))⟩
  · rintro ⟨hz, hy, hmax⟩
    exact ⟨hz, hy, fun t hst => by
      by_contra hyt; exact (ne_of_lt hst) (hmax t hyt hst.le).symm⟩

/-- A maximal element of `V(y)` is ⊓-irreducible. -/
theorem upper_separator_inf_irreducible {y s : α} (hy : ¬ y ≤ s) (hmax : ∀ t, s < t → y ≤ t) {a b : α}
    (hab : s = a ⊓ b) : s = a ∨ s = b := by
  by_contra h
  push_neg at h
  have ha : s < a := lt_of_le_of_ne (hab ▸ inf_le_left) h.1
  have hb : s < b := lt_of_le_of_ne (hab ▸ inf_le_right) h.2
  exact hy (hab ▸ le_inf (hmax a ha) (hmax b hb))

/-- Every strict upper bound of a maximal element of `V(y)` lies above `s ⊔ y`, and `s < s ⊔ y`. -/
theorem upper_separator_cover {y s : α} (hy : ¬ y ≤ s) (hmax : ∀ t, s < t → y ≤ t) :
    s < s ⊔ y ∧ ∀ t, s < t → s ⊔ y ≤ t :=
  ⟨lt_of_le_of_ne le_sup_left fun h => hy (h ▸ le_sup_right), fun t hst => sup_le hst.le (hmax t hst)⟩

/-- A minimal lower separator is ⊔-irreducible. -/
theorem lower_separator_sup_irreducible {x s : α} (hx : ¬ s ≤ x) (hmin : ∀ t, t < s → t ≤ x) {a b : α}
    (hab : s = a ⊔ b) : s = a ∨ s = b := by
  by_contra h
  push_neg at h
  have ha : a < s := lt_of_le_of_ne (hab ▸ le_sup_left) (Ne.symm h.1)
  have hb : b < s := lt_of_le_of_ne (hab ▸ le_sup_right) (Ne.symm h.2)
  exact hx (hab ▸ sup_le (hmin a ha) (hmin b hb))

theorem lower_separator_cover {x s : α} (hx : ¬ s ≤ x) (hmin : ∀ t, t < s → t ≤ x) :
    s ⊓ x < s ∧ ∀ t, t < s → t ≤ s ⊓ x :=
  ⟨lt_of_le_of_ne inf_le_left fun h => hx (h ▸ inf_le_right), fun t hts => le_inf hts.le (hmin t hts)⟩

/-- A separator for `y₀` separates every `y ≥ y₀`. -/
theorem upper_separator_mono_col {y₀ y s : α} (hy : y₀ ≤ y) (h : ¬ y₀ ≤ s) : ¬ y ≤ s :=
  fun h' => h (hy.trans h')

/-- **Aggregation criterion.** Finitely many pairs `(zᵢ, yᵢ)` (`zᵢ = F xᵢ yᵢ`) share one upper landmark iff the join
of the responses lies above none of the columns; the join is then such a landmark. -/
theorem common_separator_iff [OrderBot α] {ι : Type*} (A : Finset ι) (z y : ι → α) :
    (∃ s, ∀ i ∈ A, z i ≤ s ∧ ¬ y i ≤ s) ↔ ∀ i ∈ A, ¬ y i ≤ A.sup z := by
  constructor
  · rintro ⟨s, hs⟩ i hi h
    exact (hs i hi).2 (h.trans (Finset.sup_le fun j hj => (hs j hj).1))
  · intro h; exact ⟨A.sup z, fun i hi => ⟨Finset.le_sup hi, h i hi⟩⟩

/-- **Aggregation criterion, dual.** Pairs `(xᵢ, zᵢ)` share one lower landmark iff the meet of the responses lies
below none of the rows. -/
theorem common_lower_separator_iff [OrderTop α] {ι : Type*} (A : Finset ι) (z x : ι → α) :
    (∃ s, ∀ i ∈ A, s ≤ z i ∧ ¬ s ≤ x i) ↔ ∀ i ∈ A, ¬ A.inf z ≤ x i := by
  constructor
  · rintro ⟨s, hs⟩ i hi h
    exact (hs i hi).2 ((Finset.le_inf fun j hj => (hs j hj).1).trans h)
  · intro h; exact ⟨A.inf z, fun i hi => ⟨Finset.inf_le hi, h i hi⟩⟩

section Closure

variable [BoundedOrder α] [DecidableEq α] [DecidableLE α]

/-- **A2.** Separation by a finite meet-closed `T ∋ ⊤` is the closure-defect condition. -/
theorem separated_iff_cl {T : Finset α} (htT : ⊤ ∈ T) (hcl : ∀ a ∈ T, ∀ b ∈ T, a ⊓ b ∈ T) (z y : α) :
    (∃ s ∈ T, z ≤ s ∧ ¬ y ≤ s) ↔ ¬ y ≤ cl T z := by
  constructor
  · rintro ⟨s, hs, hzs, hys⟩ h; exact hys (h.trans (cl_le hs hzs))
  · intro h
    exact ⟨cl T z, inf_mem_of_closed htT hcl _ (Finset.filter_subset _ _), le_cl T z, h⟩

/-- **A2, dual.** -/
theorem dual_separated_iff_int {T : Finset α} (hbT : ⊥ ∈ T) (hcl : ∀ a ∈ T, ∀ b ∈ T, a ⊔ b ∈ T) (z x : α) :
    (∃ s ∈ T, s ≤ z ∧ ¬ s ≤ x) ↔ ¬ int T z ≤ x := by
  constructor
  · rintro ⟨s, hs, hsz, hsx⟩ h; exact hsx ((le_int hs hsz).trans h)
  · intro h
    exact ⟨int T z, sup_mem_of_closed hbT hcl _ (Finset.filter_subset _ _), int_le T z, h⟩

end Closure

end Mordor.ExtremalSeparators
