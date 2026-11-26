import Mordor.Derived

/-!
# The companion of the ν-layer map is vacuous for the Commutation Lemma (§34.3z²⁸⁷)

Semi-commutation `b ∘ a ≤ a ∘ b` says that `b` is `a`-compatible in Pous's sense (`f ∘ a ≤ a ∘ f`). Its weakening
"`b` lies below the companion of `a`" (the largest `a`-compatible map) carries no information on the interval
`[m, n]`, where the Commutation Lemma can fail: the constant map at `n` is `a`-compatible (`a n = n`), and `b` is
below it on `↓ n` (`b n = n`). So on `[m, n]` the companion hypothesis holds for every monotone `F`.
-/

namespace Mordor
variable {α : Type*} [CompleteLattice α] (F : α →o α →o α)

/-- The constant map at `n` is `a`-compatible: `n ≤ a(n)` for every argument. -/
theorem const_n_compatible (x : α) : (fun _ : α => n F) (a F x) ≤ a F ((fun _ : α => n F) x) :=
  le_of_eq (a_n (F := F)).symm

/-- `b` lies below the constant map at `n` on `↓ n`, so `b ≤ t_a` there for every monotone `F`. -/
theorem b_le_const_n {y : α} (hy : y ≤ n F) : b F y ≤ n F :=
  ((b F).mono hy).trans (le_of_eq (b_n (F := F)))

end Mordor
