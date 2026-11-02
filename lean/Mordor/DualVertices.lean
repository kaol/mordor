import Mordor.FaceLabels

/-!
# Second-order face incidence (round 26, §34.3z⁹³)

Response to the brief "second-order face incidence and the dual triangular frame". Three outside face columns
`y : Fin 3 → α`, edges `u i j = y i ⊔ y j`, dual vertices `v i = u i (i+1) ⊓ u i (i+2)`, lower vertices
`r i j = v i ⊓ v j`.

* `dual_vertex_geometry` (lattice only, no `F`): `y i ≤ v i`, `v i ⊔ v j = u i j` for `i ≠ j`, and
  `v 0 ⊓ v 1 ⊓ v 2 = u 0 1 ⊓ u 1 2 ⊓ u 0 2`. In particular the second triangle has the **same edges** as the first:
  the construction is idempotent.
* `dual_vertex_label`: if the full-meet row maps each edge into a petal (`F m (u (i+1) (i+2)) ≤ p (lab i)`), then
  `F m (v i) ≤ p (lab (i+1)) ⊓ p (lab (i+2))`.
* `second_order_collapse` (lattice only): with `yᵢ = ⋀_{j≠i} wⱼ`, every edge `yᵢ ⊔ yⱼ` lies below the opposite last point
  `w_k` (so `F m (u_ij) ≤ e_k ∈ D` holds automatically) and `vᵢ = yᵢ`. The second-order frame is the first-order one.
* `lower_vertex_in_D`: if moreover `lab` is a permutation, every lower vertex `r i j` (`i ≠ j`) lies in `D`: its value
  is below all three generators (correction of the brief's Branch A, whose label inclusion runs the other way).
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

section Geometry
variable {α : Type*} [Lattice α]

theorem dual_vertex_geometry (y : Fin 3 → α) :
    let u := fun i j => y i ⊔ y j
    let v := fun i : Fin 3 => u i (i + 1) ⊓ u i (i + 2)
    (∀ i, y i ≤ v i) ∧ (∀ i j, i ≠ j → v i ⊔ v j = u i j) ∧ v 0 ⊓ v 1 ⊓ v 2 = u 0 1 ⊓ u 1 2 ⊓ u 0 2 := by
  intro u v
  have hy : ∀ i, y i ≤ v i := fun i => le_inf le_sup_left le_sup_left
  have hvu : ∀ i j, i ≠ j → v i ≤ u i j := fun i j hij => by
    have : j = i + 1 ∨ j = i + 2 := by fin_cases i <;> fin_cases j <;> simp_all
    rcases this with rfl | rfl
    · exact inf_le_left
    · exact inf_le_right
  refine ⟨hy, fun i j hij => le_antisymm (sup_le (hvu i j hij) ?_) (sup_le_sup (hy i) (hy j)), ?_⟩
  · have := hvu j i (Ne.symm hij); simp only [u] at this ⊢; rwa [sup_comm] at this
  · show ((y 0 ⊔ y (0 + 1)) ⊓ (y 0 ⊔ y (0 + 2))) ⊓ ((y 1 ⊔ y (1 + 1)) ⊓ (y 1 ⊔ y (1 + 2))) ⊓
        ((y 2 ⊔ y (2 + 1)) ⊓ (y 2 ⊔ y (2 + 2))) = (y 0 ⊔ y 1) ⊓ (y 1 ⊔ y 2) ⊓ (y 0 ⊔ y 2)
    have e : ((0 : Fin 3) + 1 = 1) ∧ ((0 : Fin 3) + 2 = 2) ∧ ((1 : Fin 3) + 1 = 2) ∧ ((1 : Fin 3) + 2 = 0) ∧
        ((2 : Fin 3) + 1 = 0) ∧ ((2 : Fin 3) + 2 = 1) := by decide
    rw [e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2.1, e.2.2.2.2.2, sup_comm (y 1) (y 0), sup_comm (y 2) (y 0),
      sup_comm (y 2) (y 1)]
    apply le_antisymm
    · exact le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_left))
        (inf_le_left.trans (inf_le_right.trans inf_le_left)))
        (inf_le_left.trans (inf_le_left.trans inf_le_right))
    · exact le_inf (le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)))
        (le_inf inf_le_right (inf_le_left.trans inf_le_right))

end Geometry

variable {α : Type*} [Lattice α] [BoundedOrder α] {F : α → α → α}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')

include hF in
/-- **Dual-vertex labels.** -/
theorem dual_vertex_label (p : Fin 3 → α) (m : α) (y : Fin 3 → α) (lab : Fin 3 → Fin 3)
    (hedge : ∀ i, F m (y (i + 1) ⊔ y (i + 2)) ≤ p (lab i)) (i : Fin 3) :
    F m ((y i ⊔ y (i + 1)) ⊓ (y i ⊔ y (i + 2))) ≤ p (lab (i + 1)) ⊓ p (lab (i + 2)) := by
  have h1 : (y i ⊔ y (i + 1)) ⊓ (y i ⊔ y (i + 2)) ≤ y (i + 1 + 1) ⊔ y (i + 1 + 2) := by
    have e1 : i + 1 + 1 = i + 2 := by fin_cases i <;> rfl
    have e2 : i + 1 + 2 = i := by fin_cases i <;> rfl
    rw [e1, e2]; exact inf_le_right.trans (le_of_eq (sup_comm _ _))
  have h2 : (y i ⊔ y (i + 1)) ⊓ (y i ⊔ y (i + 2)) ≤ y (i + 2 + 1) ⊔ y (i + 2 + 2) := by
    have e1 : i + 2 + 1 = i := by fin_cases i <;> rfl
    have e2 : i + 2 + 2 = i + 1 := by fin_cases i <;> rfl
    rw [e1, e2]; exact inf_le_left
  exact le_inf ((hF _ _ _ _ le_rfl h1).trans (hedge _)) ((hF _ _ _ _ le_rfl h2).trans (hedge _))

include hF in
/-- **Lower vertices lie in `D`.** With `m = p 0 ⊓ p 1 ⊓ p 2` and `lab` bijective, `r i j ∉ D` would give
`F m (r i j) ≤ m`, a witness. -/
theorem lower_vertex_in_D (p : Fin 3 → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (y : Fin 3 → α) (lab : Fin 3 → Fin 3) (hlab : Function.Bijective lab)
    (hedge : ∀ i, F (p 0 ⊓ p 1 ⊓ p 2) (y (i + 1) ⊔ y (i + 2)) ≤ p (lab i)) {i j : Fin 3} (hij : i ≠ j) :
    ∃ k, ((y i ⊔ y (i + 1)) ⊓ (y i ⊔ y (i + 2))) ⊓ ((y j ⊔ y (j + 1)) ⊓ (y j ⊔ y (j + 2))) ≤ p k := by
  by_contra hr
  set m := p 0 ⊓ p 1 ⊓ p 2
  set Vi := (y i ⊔ y (i + 1)) ⊓ (y i ⊔ y (i + 2))
  set Vj := (y j ⊔ y (j + 1)) ⊓ (y j ⊔ y (j + 2))
  have hi : F m (Vi ⊓ Vj) ≤ p (lab (i + 1)) ⊓ p (lab (i + 2)) :=
    (hF _ _ _ _ le_rfl (inf_le_left (a := Vi) (b := Vj))).trans (dual_vertex_label hF p m y lab hedge i)
  have hj : F m (Vi ⊓ Vj) ≤ p (lab (j + 1)) ⊓ p (lab (j + 2)) :=
    (hF _ _ _ _ le_rfl (inf_le_right (a := Vi) (b := Vj))).trans (dual_vertex_label hF p m y lab hedge j)
  have hall : ∀ k, F m (Vi ⊓ Vj) ≤ p k := by
    intro k
    obtain ⟨t, rfl⟩ := hlab.2 k
    have : t = i + 1 ∨ t = i + 2 ∨ t = j + 1 ∨ t = j + 2 := by
      fin_cases i <;> fin_cases j <;> fin_cases t <;> simp_all
    rcases this with rfl | rfl | rfl | rfl
    · exact hi.trans inf_le_left
    · exact hi.trans inf_le_right
    · exact hj.trans inf_le_left
    · exact hj.trans inf_le_right
  exact (nw m ⟨0, inf_le_left.trans inf_le_left⟩ _ hr).1 (le_inf (le_inf (hall 0) (hall 1)) (hall 2))


section Collapse
variable {α : Type*} [Lattice α]

/-- **Second-order collapse (lattice only).** For faces `y_a = b ⊓ c`, `y_b = c ⊓ a`, `y_c = a ⊓ b` of three last points
`a, b, c`: each edge lies below the opposite last point, `y_a ⊔ y_b ≤ c`, and the dual vertex equals the face:
`(y_a ⊔ y_b) ⊓ (y_a ⊔ y_c) = y_a`. So `vᵢ = yᵢ`, `r_ij = yᵢ ⊓ yⱼ = a ⊓ b ⊓ c = v_J` and `z = v_J`: the
second-order frame of §34.3z⁹³ is the first-order one. -/
theorem second_order_collapse (a b c : α) :
    (b ⊓ c) ⊔ (c ⊓ a) ≤ c ∧ ((b ⊓ c) ⊔ (c ⊓ a)) ⊓ ((b ⊓ c) ⊔ (a ⊓ b)) = b ⊓ c ∧
      (b ⊓ c) ⊓ (c ⊓ a) = a ⊓ b ⊓ c := by
  refine ⟨sup_le inf_le_right inf_le_left, le_antisymm ?_ (le_inf le_sup_left le_sup_left), ?_⟩
  · exact le_inf (inf_le_right.trans (sup_le inf_le_left inf_le_right)) (inf_le_left.trans (sup_le inf_le_right inf_le_left))
  · apply le_antisymm
    · exact le_inf (le_inf (inf_le_right.trans inf_le_right) (inf_le_left.trans inf_le_left)) (inf_le_left.trans inf_le_right)
    · exact le_inf (le_inf (inf_le_left.trans inf_le_right) inf_le_right) (le_inf inf_le_right (inf_le_left.trans inf_le_left))

end Collapse

end Mordor.Profile
