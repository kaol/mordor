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

namespace Mordor.MinSwitch

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α]

/-- **The squeeze along a contracting step.** If `r ≤ a` and `F a s ≤ s`, the `F r`-orbit of `x = F a s` lies between
consecutive terms of the `F r`-orbit of `s`: `(F r)^[k+1] s ≤ (F r)^[k] x ≤ (F r)^[k] s`. -/
theorem squeeze {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {a r s : α} (hra : r ≤ a)
    (hsa : F a s ≤ s) (k : ℕ) :
    (F r)^[k + 1] s ≤ (F r)^[k] (F a s) ∧ (F r)^[k] (F a s) ≤ (F r)^[k] s := by
  have hmono : Monotone (F r) := fun y y' hy => hF _ _ _ _ le_rfl hy
  refine ⟨?_, (hmono.iterate k) hsa⟩
  rw [Function.iterate_succ_apply]; exact (hmono.iterate k) (hF _ _ _ _ hra le_rfl)

/-- **Entry after a contracting step.** If the `F r`-orbit of `s` stays outside `D` for steps `0..n` and enters at
`n + 1`, the orbit of `x = F a s` stays outside for steps `< n` and either enters at step `n` at a value above the old
endpoint, or enters at step `n + 1` at a value below it. -/
theorem entry_after_step {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {InD : α → Prop}
    (hdown : ∀ x y, x ≤ y → InD y → InD x) {a r s : α} (hra : r ≤ a) (hsa : F a s ≤ s) {n : ℕ}
    (hU : ∀ k ≤ n, ¬ InD ((F r)^[k] s)) (hin : InD ((F r)^[n + 1] s)) :
    (∀ k < n, ¬ InD ((F r)^[k] (F a s))) ∧
      ((InD ((F r)^[n] (F a s)) ∧ (F r)^[n + 1] s ≤ (F r)^[n] (F a s)) ∨
       (¬ InD ((F r)^[n] (F a s)) ∧ InD ((F r)^[n + 1] (F a s)) ∧ (F r)^[n + 1] (F a s) ≤ (F r)^[n + 1] s)) := by
  refine ⟨fun k hk hk' => hU (k + 1) (by omega) (hdown _ _ (squeeze hF hra hsa k).1 hk'), ?_⟩
  by_cases h : InD ((F r)^[n] (F a s))
  · exact Or.inl ⟨h, (squeeze hF hra hsa n).1⟩
  · exact Or.inr ⟨h, hdown _ _ (squeeze hF hra hsa (n + 1)).2 hin, (squeeze hF hra hsa (n + 1)).2⟩

/-- **A meet row whose value has only label `i` forces row `i` to escape.** If `F m x ≤ F (pᵢ) x`, `x ∉ D`, and every
generator above `F m x` is `pᵢ`, then `F (pᵢ) x ∉ D` (a `D`-value of row `i` lies below some `pⱼ`, `j ≠ i`, by W1). -/
theorem escapes_of_low_labels {ι : Type*} {p : ι → α} {F : α → α → α}
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {m x : α} {i : ι} (hx : ¬ ∃ j, x ≤ p j) (hle : F m x ≤ F (p i) x) (hlab : ∀ j, F m x ≤ p j → j = i) :
    ¬ ∃ j, F (p i) x ≤ p j := by
  rintro ⟨j, hj⟩
  obtain rfl := hlab j (hle.trans hj)
  exact (nw (p j) ⟨j, le_rfl⟩ x hx).1 hj

end Mordor.MinSwitch
