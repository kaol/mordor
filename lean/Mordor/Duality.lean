import Mordor.Derived

/-!
# The Duality Theorem (log §22.1)

`Fᵈ x y = h (F (h y) (h x))` on `αᵒᵈ` (order reversal and transpose). Its derived maps are the conjugates of
`b` and `a`, and `mᵈ = h n`, `nᵈ = h m`. So `m = n` and commutation transfer between `L` and `Lᵒᵖ`.
-/

namespace Mordor
open OrderDual
variable {α : Type*} [CompleteLattice α]

/-- The dual bifunction on `αᵒᵈ`. -/
def dualF (F : α →o α →o α) : αᵒᵈ →o αᵒᵈ →o αᵒᵈ where
  toFun x := ⟨fun y => toDual (F (ofDual y) (ofDual x)),
    fun _ _ h => toDual_le_toDual.mpr (F.mono (ofDual_le_ofDual.mpr h) _)⟩
  monotone' _ _ h y := toDual_le_toDual.mpr ((F (ofDual y)).mono (ofDual_le_ofDual.mpr h))

variable {F : α →o α →o α}

@[simp] theorem dualF_apply (x y : αᵒᵈ) : dualF F x y = toDual (F (ofDual y) (ofDual x)) := rfl

/-- `aᵈ = h ∘ b ∘ h⁻¹`. -/
theorem a_dual (x : αᵒᵈ) : a (dualF F) x = toDual (b F (ofDual x)) := by
  apply le_antisymm
  · -- ofDual (aᵈ x) is a fixed point of column `ofDual x`, so b ≤ it
    change toDual (ofDual (a (dualF F) x)) ≤ _
    rw [toDual_le_toDual]
    apply (col F (ofDual x)).lfp_le_fixed
    show F (ofDual (a (dualF F) x)) (ofDual x) = ofDual (a (dualF F) x)
    exact congrArg ofDual (row_a (F := dualF F) x)
  · apply le_a
    show toDual (b F (ofDual x)) ≤ toDual (F (ofDual (toDual (b F (ofDual x)))) (ofDual x))
    rw [ofDual_toDual, col_b]

/-- `bᵈ = h ∘ a ∘ h⁻¹`. -/
theorem b_dual (y : αᵒᵈ) : b (dualF F) y = toDual (a F (ofDual y)) := by
  apply le_antisymm
  · apply b_le
    show toDual (F (ofDual y) (ofDual (toDual (a F (ofDual y))))) ≤ toDual (a F (ofDual y))
    rw [ofDual_toDual, row_a]
  · change _ ≤ toDual (ofDual (b (dualF F) y))
    rw [toDual_le_toDual]
    apply le_a
    show ofDual (b (dualF F) y) ≤ F (ofDual y) (ofDual (b (dualF F) y))
    exact (congrArg ofDual (col_b (F := dualF F) y)).ge

/-- `mᵈ = h n`. -/
theorem m_dual : m (dualF F) = toDual (n F) := by
  apply le_antisymm
  · apply (a (dualF F)).lfp_le_fixed
    show a (dualF F) (toDual (n F)) = toDual (n F)
    rw [a_dual, ofDual_toDual, b_n]
  · change toDual (n F) ≤ toDual (ofDual (m (dualF F)))
    rw [toDual_le_toDual]
    apply common_le_n
    have := congrArg ofDual (a_m (F := dualF F))
    rw [a_dual, ofDual_toDual] at this
    exact this

/-- `nᵈ = h m`. -/
theorem n_dual : n (dualF F) = toDual (m F) := by
  apply le_antisymm
  · change toDual (ofDual (n (dualF F))) ≤ toDual (m F)
    rw [toDual_le_toDual]
    apply m_le_common
    have := congrArg ofDual (b_n (F := dualF F))
    rw [b_dual, ofDual_toDual] at this
    exact this
  · apply (b (dualF F)).le_gfp
    show toDual (m F) ≤ b (dualF F) (toDual (m F))
    rw [b_dual, ofDual_toDual, a_m]

/-- **CL transfers between `L` and `Lᵒᵖ`.** -/
theorem m_eq_n_dual_iff : m (dualF F) = n (dualF F) ↔ m F = n F := by
  rw [m_dual, n_dual, toDual_inj]; exact eq_comm

/-- Commutation transfers: `aᵈ ∘ bᵈ = bᵈ ∘ aᵈ ⟺ a ∘ b = b ∘ a`. -/
theorem comm_dual_iff :
    (∀ x, a (dualF F) (b (dualF F) x) = b (dualF F) (a (dualF F) x)) ↔ ∀ x, a F (b F x) = b F (a F x) := by
  simp only [a_dual, b_dual, ofDual_toDual]
  constructor
  · intro h x; have := h (toDual x); rw [ofDual_toDual, toDual_inj] at this; exact this.symm
  · intro h x; rw [toDual_inj]; exact (h _).symm

end Mordor
