import Mathlib.Order.Basic

/-!
# Pivot directions under adaptive capture (round 26, §34.3z¹⁰⁷, work package A)

In the finite Sperner argument (`FinGen.captured`), a good word for `(A, B)` has a pivot value `z*` with `z* ≰ p` for
every `p ∈ A` and `u ≰ z*` for every `u ∈ B`. The brief's tail argument (A4) needs the pivots of a compatible chain to
be monotone, so that chain-finiteness stabilizes them. Under *adaptive* capture (add a maximal `p ≥ z*` when
`z* ∈ D`, a minimal `u ≤ z*` otherwise) the next pivot moves in opposite directions on the two sides:

* `pivot_not_le_of_P_capture`: after adding `p ≥ z*`, the new pivot `z'` (which avoids `↓p`) satisfies `z' ≰ z*`;
* `pivot_not_ge_of_U_capture`: after adding `u ≤ z*`, the new pivot (which avoids `↑u`) satisfies `z* ≰ z'`.

So a pivot sequence produced by adaptive capture can only be monotone if it stays on one side of the cut, and then
only in the direction the respective lemma allows (increasing in `D`, decreasing outside). A proof along A4 must
show that capture keeps the pivot on one side, which is again the capture problem.
-/

namespace Mordor.GoodWordPivot

theorem pivot_not_le_of_P_capture {α : Type*} [Preorder α] {z z' p : α} (hcap : z ≤ p) (hnew : ¬ z' ≤ p) :
    ¬ z' ≤ z := fun h => hnew (h.trans hcap)

theorem pivot_not_ge_of_U_capture {α : Type*} [Preorder α] {z z' u : α} (hcap : u ≤ z) (hnew : ¬ u ≤ z') :
    ¬ z ≤ z' := fun h => hnew (hcap.trans h)

end Mordor.GoodWordPivot
