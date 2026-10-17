import Mordor.Cut
import Mathlib.Order.Preorder.Finite

/-!
# Principal cuts (log §30.4)

On a finite lattice the Cut Lemma holds for every principal cut: `D = {x | ¬ u ≤ x}` (that is, `U = ↑u`) or
`D = ↓d`. The log's proof iterates `τ x = F x (x ⊔ u)` from `⊥`; here a maximal `x ∈ D` with `x ≤ τ x` replaces the
iteration (dually a minimal `y ∈ U` with `σ y ≤ y`, `σ y = F (y ⊓ d) y`), which needs only finiteness.
-/

namespace Mordor
variable {α : Type*} [CompleteLattice α] [Finite α] (F : α →o α →o α)

/-- **Principal cut `U = ↑u`.** -/
theorem cut_principal_up (u : α) (hu : u ≠ ⊥) :
    ∃ x, ¬ u ≤ x ∧ ∃ y, u ≤ y ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  let τ : α → α := fun x => F x (x ⊔ u)
  have τmono : Monotone τ := fun x x' h => (F.mono h _).trans ((F x').mono (sup_le_sup_right h u))
  let S : Set α := {x | ¬ u ≤ x ∧ x ≤ τ x}
  have hS : S.Nonempty := ⟨⊥, fun h => hu (le_bot_iff.mp h), bot_le⟩
  obtain ⟨x, hxS, hmax⟩ := Set.Finite.exists_maximal S.toFinite hS
  refine ⟨x, hxS.1, x ⊔ u, le_sup_right, ?_⟩
  by_cases hτ : u ≤ τ x
  · exact Or.inr (sup_le hxS.2 hτ)
  · -- τ x ∈ D and τ x ≤ τ (τ x), so maximality gives τ x = x: a fixed point in D
    have hmem : τ x ∈ S := ⟨hτ, τmono hxS.2⟩
    exact Or.inl (hmax hmem hxS.2)

/-- **Principal cut `D = ↓d`.** -/
theorem cut_principal_down (d : α) (hd : d ≠ ⊤) :
    ∃ x, x ≤ d ∧ ∃ y, ¬ y ≤ d ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  let σ : α → α := fun y => F (y ⊓ d) y
  have σmono : Monotone σ := fun y y' h => (F.mono (inf_le_inf_right d h) _).trans ((F _).mono h)
  let S : Set α := {y | ¬ y ≤ d ∧ σ y ≤ y}
  have hS : S.Nonempty := ⟨⊤, fun h => hd (top_le_iff.mp h), le_top⟩
  obtain ⟨y, hyS, hmin⟩ := Set.Finite.exists_minimal S.toFinite hS
  refine ⟨y ⊓ d, inf_le_right, y, hyS.1, ?_⟩
  by_cases hσ : σ y ≤ d
  · exact Or.inl (le_inf hyS.2 hσ)
  · have hmem : σ y ∈ S := ⟨hσ, σmono hyS.2⟩
    exact Or.inr (hmin hmem hyS.2)

end Mordor
