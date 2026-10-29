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

namespace Mordor.MinSwitch

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α]

/-- The terminal strict-switch state of §34.3z²² (three generators, row `p₁` exhausted into petal `2`):
`x ∉ D`, `g₁ x ≤ x`, `g₁ x` below `p₂` only, and `h x = F (p₁ ⊓ p₂ ⊓ p₃) x` below `p₁` and `p₂` but not `p₃`. -/
structure Terminal (F : α → α → α) (p₁ p₂ p₃ x : α) : Prop where
  hx : ¬ (x ≤ p₁ ∨ x ≤ p₂ ∨ x ≤ p₃)
  g1le : F p₁ x ≤ x
  g1p2 : F p₁ x ≤ p₂
  g1np1 : ¬ F p₁ x ≤ p₁
  g1np3 : ¬ F p₁ x ≤ p₃
  h1 : F (p₁ ⊓ p₂ ⊓ p₃) x ≤ p₁
  h2 : F (p₁ ⊓ p₂ ⊓ p₃) x ≤ p₂
  h3 : ¬ F (p₁ ⊓ p₂ ⊓ p₃) x ≤ p₃

section Terminal
variable {F : α → α → α} {p₁ p₂ p₃ x : α}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
  (nw : ∀ a, (a ≤ p₁ ∨ a ≤ p₂ ∨ a ≤ p₃) → ∀ y, ¬ (y ≤ p₁ ∨ y ≤ p₂ ∨ y ≤ p₃) → ¬ F a y ≤ a ∧ ¬ y ≤ F a y)
  (T : Terminal F p₁ p₂ p₃ x)
include hF nw T

/-- **At the terminal state row `p₂` escapes:** `v = g₂ x ∉ D`. -/
theorem terminal_v_notin : ¬ (F p₂ x ≤ p₁ ∨ F p₂ x ≤ p₂ ∨ F p₂ x ≤ p₃) := by
  have hhv : F (p₁ ⊓ p₂ ⊓ p₃) x ≤ F p₂ x := hF _ _ _ _ (inf_le_left.trans inf_le_right) le_rfl
  rintro (h | h | h)
  · have h12 : F (p₁ ⊓ p₂) x ≤ p₁ ⊓ p₂ :=
      le_inf ((hF _ _ _ _ inf_le_right le_rfl).trans h) ((hF _ _ _ _ inf_le_left le_rfl).trans T.g1p2)
    exact (nw _ (Or.inl inf_le_left) x T.hx).1 h12
  · exact (nw p₂ (Or.inr (Or.inl le_rfl)) x T.hx).1 h
  · exact T.h3 (hhv.trans h)

/-- **The meet candidate.** In case II (`g₂ x ≰ x`) the meet `w = x ⊓ g₂ x` lies strictly below `x` and `g₂ x`, above
`h x`; row 1 is bounded by `x` and row 2 by `g₂ x` at `w`; and if `w ∈ D` then `w` lies below `p₂` and neither `p₁` nor
`p₃`. -/
theorem terminal_meet (hvx : ¬ F p₂ x ≤ x) :
    x ⊓ F p₂ x < x ∧ x ⊓ F p₂ x < F p₂ x ∧ F (p₁ ⊓ p₂ ⊓ p₃) x ≤ x ⊓ F p₂ x ∧
    F p₁ (x ⊓ F p₂ x) ≤ x ∧ F p₂ (x ⊓ F p₂ x) ≤ F p₂ x ∧
    ¬ x ⊓ F p₂ x ≤ p₁ ∧ ¬ x ⊓ F p₂ x ≤ p₃ := by
  have hxv : ¬ x ≤ F p₂ x := (nw p₂ (Or.inr (Or.inl le_rfl)) x T.hx).2
  have hr1 : p₁ ⊓ p₂ ⊓ p₃ ≤ p₁ := inf_le_left.trans inf_le_left
  have hr2 : p₁ ⊓ p₂ ⊓ p₃ ≤ p₂ := inf_le_left.trans inf_le_right
  have hhw : F (p₁ ⊓ p₂ ⊓ p₃) x ≤ x ⊓ F p₂ x :=
    le_inf ((hF _ _ _ _ hr1 le_rfl).trans T.g1le) (hF _ _ _ _ hr2 le_rfl)
  have h12w : F (p₁ ⊓ p₂) x ≤ x ⊓ F p₂ x :=
    le_inf ((hF _ _ _ _ inf_le_left le_rfl).trans T.g1le) (hF _ _ _ _ inf_le_right le_rfl)
  refine ⟨lt_of_le_of_ne inf_le_left fun h => hxv (h.symm.le.trans inf_le_right),
    lt_of_le_of_ne inf_le_right fun h => hvx (h.symm.le.trans inf_le_left), hhw,
    (hF _ _ _ _ le_rfl inf_le_left).trans T.g1le, hF _ _ _ _ le_rfl inf_le_left, fun h => ?_,
    fun h => T.h3 (hhw.trans h)⟩
  have : F (p₁ ⊓ p₂) x ≤ p₁ ⊓ p₂ :=
    le_inf (h12w.trans h) ((hF _ _ _ _ inf_le_left le_rfl).trans T.g1p2)
  exact (nw _ (Or.inl inf_le_left) x T.hx).1 this

/-- **The cross-row transfer is exactly contraction at the meet.** `g₁ w ≤ g₂ x` makes row 1 contract at `w`, and
`g₂ w ≤ x` makes row 2 contract at `w`. (Whether either holds is open: a near-model with no-witness at `x`, `g₂ x`,
`w`, `⊤` violates both, §34.3z²³.) -/
theorem terminal_transfer (hvx : ¬ F p₂ x ≤ x) :
    (F p₁ (x ⊓ F p₂ x) ≤ F p₂ x → F p₁ (x ⊓ F p₂ x) ≤ x ⊓ F p₂ x) ∧
    (F p₂ (x ⊓ F p₂ x) ≤ x → F p₂ (x ⊓ F p₂ x) ≤ x ⊓ F p₂ x) := by
  obtain ⟨-, -, -, h1, h2, -, -⟩ := terminal_meet hF nw T hvx
  exact ⟨fun h => le_inf h1 h, fun h => le_inf h h2⟩

end Terminal
end Mordor.MinSwitch
