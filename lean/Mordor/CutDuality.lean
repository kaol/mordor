import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Set.Defs
import Mathlib.Order.Defs.PartialOrder

/-!
# The Cut Lemma is self-dual per F (log §33.3)

For a preorder and **arbitrary** maps `a b` (monotonicity, completeness and finiteness are not needed):
`Φ D = ↓(D ∪ a D ∪ b⁻¹ D)` on down-sets, `Ψ U = ↑(U ∪ b U ∪ a⁻¹ U)` on up-sets.
* `adjunction`: `Φ D ∩ U = ∅ ↔ D ∩ Ψ U = ∅`, i.e. `Φ ⊣ c ∘ Ψ ∘ c`.
* `k_plus_j`: `Φᵏ D ∩ Ψʲ U = ∅ ↔ D ∩ Ψᵏ⁺ʲ U = ∅ ↔ Φᵏ⁺ʲ D ∩ U = ∅`.
With `D = ↓⊥`, `U = ↑⊤` the down-set and up-set closures of the Cut Lemma reach the whole lattice at the same stage.
The log (§33.3) stated this for monotone `a b` on finite lattices; neither hypothesis is used.
-/

namespace Mordor.CutDual
variable {α : Type*} [Preorder α] (a b : α → α)

def IsDown (D : Set α) : Prop := ∀ ⦃x y⦄, x ≤ y → y ∈ D → x ∈ D
def IsUp (U : Set α) : Prop := ∀ ⦃x y⦄, x ≤ y → x ∈ U → y ∈ U
def Disj (A B : Set α) : Prop := ∀ x, x ∈ A → x ∈ B → False

/-- `Φ D = ↓(D ∪ a(D) ∪ b⁻¹(D))`. -/
def Phi (D : Set α) : Set α := {x | ∃ y, x ≤ y ∧ (y ∈ D ∨ (∃ z ∈ D, y = a z) ∨ b y ∈ D)}
/-- `Ψ U = ↑(U ∪ b(U) ∪ a⁻¹(U))`. -/
def Psi (U : Set α) : Set α := {x | ∃ y, y ≤ x ∧ (y ∈ U ∨ (∃ z ∈ U, y = b z) ∨ a y ∈ U)}

theorem phi_down (D : Set α) : IsDown (Phi a b D) :=
  fun _ _ hxy ⟨w, hyw, h⟩ => ⟨w, le_trans hxy hyw, h⟩

theorem psi_up (U : Set α) : IsUp (Psi a b U) :=
  fun _ _ hxy ⟨w, hwx, h⟩ => ⟨w, le_trans hwx hxy, h⟩

/-- **Adjunction lemma.** -/
theorem adjunction (D U : Set α) (hD : IsDown D) (hU : IsUp U) :
    Disj (Phi a b D) U ↔ Disj D (Psi a b U) := by
  constructor
  · intro h x hDx ⟨y, hyx, hy⟩
    rcases hy with hUy | ⟨z, hUz, rfl⟩ | hUay
    · exact h y ⟨x, hyx, Or.inl hDx⟩ hUy
    · exact h z ⟨z, le_rfl, Or.inr (Or.inr (hD hyx hDx))⟩ hUz
    · exact h (a y) ⟨a y, le_rfl, Or.inr (Or.inl ⟨y, hD hyx hDx, rfl⟩)⟩ hUay
  · intro h x ⟨y, hxy, hy⟩ hUx
    have hUy : y ∈ U := hU hxy hUx
    rcases hy with hDy | ⟨z, hDz, rfl⟩ | hDby
    · exact h y hDy ⟨y, le_rfl, Or.inl hUy⟩
    · exact h z hDz ⟨z, le_rfl, Or.inr (Or.inr hUy)⟩
    · exact h (b y) hDby ⟨b y, le_rfl, Or.inr (Or.inl ⟨y, hUy, rfl⟩)⟩

theorem iter_down (D : Set α) (hD : IsDown D) : ∀ k, IsDown ((Phi a b)^[k] D)
  | 0 => hD
  | k + 1 => by rw [Function.iterate_succ_apply']; exact phi_down a b _

theorem iter_up (U : Set α) (hU : IsUp U) : ∀ j, IsUp ((Psi a b)^[j] U)
  | 0 => hU
  | j + 1 => by rw [Function.iterate_succ_apply']; exact psi_up a b _

/-- Move `k` steps of `Φ` across the disjointness as `k` steps of `Ψ`. -/
theorem shift : ∀ (k : ℕ) (D U : Set α), IsDown D → IsUp U →
    (Disj ((Phi a b)^[k] D) U ↔ Disj D ((Psi a b)^[k] U))
  | 0, _, _, _, _ => Iff.rfl
  | k + 1, D, U, hD, hU => by
      rw [Function.iterate_succ_apply', adjunction a b _ _ (iter_down a b D hD k) hU,
        shift k D _ hD (psi_up a b U), ← Function.iterate_succ_apply]

/-- **The `k + j` law (§33.3).** -/
theorem k_plus_j (D U : Set α) (hD : IsDown D) (hU : IsUp U) (k j : ℕ) :
    (Disj ((Phi a b)^[k] D) ((Psi a b)^[j] U) ↔ Disj D ((Psi a b)^[k + j] U)) ∧
    (Disj D ((Psi a b)^[k + j] U) ↔ Disj ((Phi a b)^[k + j] D) U) := by
  refine ⟨?_, (shift a b (k + j) D U hD hU).symm⟩
  rw [shift a b k D _ hD (iter_up a b U hU j), ← Function.iterate_add_apply]

end Mordor.CutDual
