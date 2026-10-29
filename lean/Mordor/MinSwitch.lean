import Mordor.Crossing

/-!
# Minimal orbit states (log §34.3z²¹)

DCC is used here as minimality on an *orbit-defined* set: states `s ∉ D` with a contracting row `a` (`F a s ≤ s`) whose
orbit under a lower row `r` enters `D` at a value with a downward-closed property `Good` (e.g. "below every `pᵢ`,
`i ∈ A`"). For `x < s`, monotonicity bounds the orbit of `x` by that of `s`, so membership of smaller columns is a
finite condition; this is what makes the minimal state usable.

* `interval_in_D`: at a minimal state whose `r`-orbit enters `D` at once (`F r s ∈ D`), every column in `[F a s, s)` lies
  in `D`. Any such column outside `D` would be a smaller state: `F a x ≤ F a s ≤ x`, and `F r x ≤ F r s` inherits
  membership of `D` and `Good`.
  Since every such column lies above `F a s`, its labels are among those of `F a s`.
-/

namespace Mordor.MinSwitch

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α]

theorem interval_in_D {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {InD Good : α → Prop} (hdown : ∀ x y, x ≤ y → InD y → InD x) (hgood : ∀ x y, x ≤ y → Good y → Good x)
    {a r s : α} (hD : InD (F r s)) (hG : Good (F r s))
    (hmin : ∀ x, x < s → ¬ InD x → F a x ≤ x → InD (F r x) → Good (F r x) → False) :
    ∀ x, F a s ≤ x → x < s → InD x := by
  intro x hlo hlt
  by_contra hx
  have hrx : F r x ≤ F r s := hF _ _ _ _ le_rfl hlt.le
  exact hmin x hlt hx ((hF _ _ _ _ le_rfl hlt.le).trans hlo) (hdown _ _ hrx hD) (hgood _ _ hrx hG)

end Mordor.MinSwitch
