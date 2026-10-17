import Mathlib.Order.FixedPoints
import Mathlib.Order.GaloisConnection.Basic

/-!
# The dialgebraic layer, thin model (log §32.2–§32.4)

In a lattice viewed as a category, an `(f, g)`-dialgebra is an `x` with `f x ≤ g x`; the initial one is the least
such `x`, and `δ₀` is iso iff `f x = g x`.
-/

namespace Mordor.Dial
variable {α : Type*}

/-- **Transposition (§32.2).** If `g` has a left adjoint `l`, the least `(f, g)`-dialgebra is `μ (l ∘ f)`. -/
theorem isLeast_dial [CompleteLattice α] (f g l : α →o α) (gc : GaloisConnection l g) :
    IsLeast {x | f x ≤ g x} (l.comp f).lfp :=
  ⟨(gc _ _).1 (l.comp f).map_lfp.le, fun _ hx => (l.comp f).lfp_le ((gc _ _).2 hx)⟩

/-- **Dual transposition.** If `f` has a right adjoint `r`, the greatest `(f, g)`-dialgebra is `ν (r ∘ g)`. -/
theorem isGreatest_dial [CompleteLattice α] (f g r : α →o α) (gc : GaloisConnection f r) :
    IsGreatest {x | f x ≤ g x} (r.comp g).gfp :=
  ⟨(gc _ _).2 (r.comp g).map_gfp.ge, fun _ hx => (r.comp g).le_gfp ((gc _ _).1 hx)⟩

/-- **Failure-zone theorem (§32.3).** If `g` preserves binary meets and `A₀` is the least `(f, g)`-dialgebra,
then `δ₀` is iso iff `f A₀` lies in the image of `g`. -/
theorem failure_zone [SemilatticeInf α] {f g : α → α} (hf : Monotone f) (hg : ∀ x y, g (x ⊓ y) = g x ⊓ g y)
    {A₀ : α} (hA : IsLeast {x | f x ≤ g x} A₀) : f A₀ = g A₀ ↔ f A₀ ∈ Set.range g := by
  refine ⟨fun h => ⟨A₀, h.symm⟩, fun ⟨z, hz⟩ => ?_⟩
  have hdial : f A₀ ≤ g A₀ := hA.1
  have h1 : f (A₀ ⊓ z) ≤ f A₀ := hf inf_le_left
  have hx : A₀ ⊓ z ∈ {x | f x ≤ g x} := by
    show f (A₀ ⊓ z) ≤ g (A₀ ⊓ z)
    rw [hg]; exact le_inf (h1.trans hdial) (hz ▸ h1)
  have hAz : A₀ ≤ z := (hA.2 hx).trans inf_le_right
  have hmono : g A₀ ≤ g z := by
    have := hg A₀ z; rw [inf_eq_left.mpr hAz] at this; rw [this]; exact inf_le_right
  exact le_antisymm hdial (hz ▸ hmono)

/-- **Dual failure-zone theorem.** If `f` preserves binary joins and `A₁` is the greatest `(f, g)`-dialgebra,
then `δ₁` is iso iff `g A₁` lies in the image of `f`. -/
theorem failure_zone_dual [SemilatticeSup α] {f g : α → α} (hg : Monotone g) (hf : ∀ x y, f (x ⊔ y) = f x ⊔ f y)
    {A₁ : α} (hA : IsGreatest {x | f x ≤ g x} A₁) : f A₁ = g A₁ ↔ g A₁ ∈ Set.range f := by
  refine ⟨fun h => ⟨A₁, h⟩, fun ⟨z, hz⟩ => ?_⟩
  have hdial : f A₁ ≤ g A₁ := hA.1
  have h1 : g A₁ ≤ g (A₁ ⊔ z) := hg le_sup_left
  have hx : A₁ ⊔ z ∈ {x | f x ≤ g x} := by
    show f (A₁ ⊔ z) ≤ g (A₁ ⊔ z)
    rw [hf]; exact sup_le (hdial.trans h1) (hz ▸ h1)
  have hzA : z ≤ A₁ := le_sup_right.trans (hA.2 hx)
  have hmono : f z ≤ f A₁ := by
    have := hf A₁ z; rw [sup_eq_left.mpr hzA] at this; rw [this]; exact le_sup_right
  exact le_antisymm hdial (hz ▸ hmono)

/-- **D5 (§32.4).** Reversing the order sends `(f, g)`-dialgebras to `(g, f)`-dialgebras (functors swapped), so the
least `(f, g)`-dialgebra of `α` is the greatest `(gᵒᵈ, fᵒᵈ)`-dialgebra of `αᵒᵈ`. -/
theorem d5 [Preorder α] (f g : α → α) (A : α) :
    IsLeast {x | f x ≤ g x} A ↔
      IsGreatest {y : αᵒᵈ | OrderDual.toDual (g (OrderDual.ofDual y)) ≤ OrderDual.toDual (f (OrderDual.ofDual y))}
        (OrderDual.toDual A) := by
  simp only [IsLeast, IsGreatest, upperBounds, lowerBounds, Set.mem_setOf_eq, OrderDual.toDual_le_toDual]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun y hy => h2 hy⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun y hy => h2 (a := OrderDual.toDual y) hy⟩

end Mordor.Dial
