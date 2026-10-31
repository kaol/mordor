import Mathlib.Algebra.Group.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.List.Basic

/-!
# The unital Leibniz law collapses in cancellative ambients (round 26, §34.3z⁵⁵)

An outside framework ("Frodo") takes as its di-mode crossing law the infinitesimal (Leibniz) law
`ν(μ(x, y)) = x₁ ⊗ μ(x₂, y) + μ(x, y₁) ⊗ y₂` together with a two-sided unit `η` for `μ` and a counit `ε` for `ν`.

* **`leibniz_collapse`.** An abelian group with a unital biadditive `μ`, an additive left counit for `ν`, and the
  Leibniz law is zero. At `x = y = η` the law reads `ν η = ν η + ν η`, so `ν η = 0`; the counit then gives
  `η = 0`, and `x = μ η x = 0`. This is Aguiar's observation that unital counital ε-bialgebras vanish; Loday–Ronco's
  unital infinitesimal law subtracts `x ⊗ y` for exactly this reason. Only additive cancellation is used, so the
  same argument kills the law in every semi-additive category with cancellative hom-monoids.
* **`deconcat_leibniz`, `deconcat_counit`, `deconcat_seed`.** In `Rel` (sum = union, idempotent) the law has a
  nonzero exact model: words, concatenation, deconcatenation. **`deconcat_not_bialg`**: the bialgebra law fails there.

So the law is consistent exactly where sums are idempotent, i.e. in the order-theoretic ambients of this program,
and there the framework's mode-exclusion theorem (which assumes cancellation and `2 ≠ 0`) has no instance.
-/

namespace Mordor.Axioms.Leibniz

section Linear
variable {A T : Type*} [Zero A] [AddCommGroup T]

/-- Unital Leibniz law + left counit ⇒ the carrier is zero.

`T` plays `A ⊗ A`. `Lm y` and `Rm x` are the two maps of the Leibniz law, `id ⊗ μ(–, y)` and `μ(x, –) ⊗ id`, and
`c` is `(ε ⊗ id)` followed by the unitor. The unit laws enter only through `Lm η = id` and `Rm η = id`, and additivity only through `μ 0 x = 0` and `c 0 = 0`, which is
`μ(–, η) = id`, `μ(η, –) = id` and functoriality of `⊗`. Nothing else about tensors is used; in particular the
statement covers every module over every commutative ring. -/
theorem leibniz_collapse (μ : A → A → A) (η : A) (hl : ∀ x, μ η x = x) (hμ : ∀ x, μ 0 x = 0)
    (ν : A → T) (c : T → A) (hc : c 0 = 0) (hcounit : ∀ x, c (ν x) = x)
    (Lm Rm : A → T → T) (hL : Lm η = id) (hR : Rm η = id)
    (hleib : ∀ x y, ν (μ x y) = Lm y (ν x) + Rm x (ν y)) :
    ∀ x : A, x = 0 := by
  have hνη : ν η = 0 := by
    have h := hleib η η
    rw [hl η, hL, hR] at h
    simp only [id] at h
    exact (left_eq_add.mp h)
  have hη : η = 0 := by rw [← hcounit η, hνη, hc]
  intro x
  rw [← hl x, hη, hμ]

end Linear

section Rel
variable {α : Type*}

/-- Deconcatenation, as a relation `List α → List α × List α` (a morphism of `Rel`). -/
def split (w : List α) : Set (List α × List α) := {p | p.1 ++ p.2 = w}

/-- The Leibniz law in `Rel`, sum = union: the splits of `x ++ y` are the splits inside `x` followed by `y`,
together with `x` followed by the splits inside `y`. -/
theorem deconcat_leibniz (x y : List α) :
    split (x ++ y) = {p | ∃ q ∈ split x, p = (q.1, q.2 ++ y)} ∪ {p | ∃ q ∈ split y, p = (x ++ q.1, q.2)} := by
  refine Set.ext fun p => ?_
  obtain ⟨u, v⟩ := p
  simp only [split, Set.mem_setOf_eq, Set.mem_union, Prod.exists, Prod.mk.injEq]
  constructor
  · intro h
    rcases List.append_eq_append_iff.mp h with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
    · exact Or.inl ⟨u, a', rfl, rfl, rfl⟩
    · exact Or.inr ⟨c', v, rfl, rfl, rfl⟩
  · rintro (⟨a, b, rfl, rfl, rfl⟩ | ⟨a, b, rfl, rfl, rfl⟩) <;> simp

/-- Counit: the drain relates only `[]`; draining the left factor of a split returns the word. -/
theorem deconcat_counit (w : List α) : {v | ∃ u, (u, v) ∈ split w ∧ u = []} = {w} := by
  refine Set.ext fun v => ?_; simp [split, Set.mem_singleton_iff]

/-- Seed compatibility: `ν η = η ⊗ η`. -/
theorem deconcat_seed : split ([] : List α) = {([], [])} := by
  refine Set.ext fun ⟨u, v⟩ => ?_; simp [split, Set.mem_singleton_iff]

/-- The bialgebra (duplication) law `ν(xy) = Σ x₁y₁ ⊗ x₂y₂` fails for deconcatenation. -/
theorem deconcat_not_bialg {a b : α} (hab : a ≠ b) :
    ([b], [a]) ∉ split ([a] ++ [b]) ∧
    ∃ q ∈ split [a], ∃ r ∈ split [b], ([b], [a]) = (q.1 ++ r.1, q.2 ++ r.2) := by
  refine ⟨?_, ([], [a]), by simp [split, Set.mem_setOf_eq], ([b], []), by simp [split, Set.mem_setOf_eq], by simp⟩
  simp [split, Set.mem_setOf_eq, hab.symm]

end Rel
end Mordor.Axioms.Leibniz
