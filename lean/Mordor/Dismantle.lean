import Mathlib.Order.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Dismantling the Cut Lemma on posets (log §34.3z³²)

The Cut Lemma on a poset `α`: for a down-set `D` and monotone `F`, some `x ∈ D`, `y ∉ D` has `F x y ≤ x` or
`y ≤ F x y`. A counterexample is a witness-free `F`.

* `dismantle_D`: if `x ∈ D` has a least strict upper bound `x⁺` (a unique upper cover, in a finite poset) and
  `x⁺ ∈ D`, a counterexample on `α` gives one on `{y // y ≠ x}`, with values pushed up by `r x = x⁺`. Pushing up
  keeps W1 (`r z ≤ m → z ≤ m`) and leaves W2 untouched.
* `dismantle_C`: dually, `y ∉ D` with a greatest strict lower bound `y⁻ ∉ D` can be deleted, values pushed down.

So the finite-poset Cut Lemma reduces to *cores*: posets in which no element of `D` below a `D`-element has a unique
upper cover inside `D`, and no column above a column has a unique lower cover among columns.
-/

namespace Mordor.Dismantle

variable {α : Type*} [PartialOrder α]

/-- A witness-free monotone `F` for the down-set `D`. -/
def Cx (D : Set α) (F : α → α → α) : Prop :=
  (∀ a a' b b', a ≤ a' → b ≤ b' → F a b ≤ F a' b') ∧
  ∀ a ∈ D, ∀ b ∉ D, ¬ F a b ≤ a ∧ ¬ b ≤ F a b

/-- Push `x` to `x⁺`. -/
noncomputable def up (x xp : α) (z : α) : α := by classical exact if z = x then xp else z

theorem up_mono {x xp : α} (hx : x < xp) (hcov : ∀ y, x < y → xp ≤ y) : Monotone (up x xp) := by
  classical
  intro a b hab
  unfold up
  by_cases ha : a = x <;> by_cases hb : b = x
  · simp [ha, hb]
  · simp only [ha, hb, if_true, if_false]
    exact hcov b (lt_of_le_of_ne (ha ▸ hab) (fun h => hb h.symm))
  · simp only [ha, hb, if_true, if_false]; exact (hb ▸ hab).trans hx.le
  · simp only [ha, hb, if_false]; exact hab

theorem le_up (x xp : α) (hx : x < xp) (z : α) : z ≤ up x xp z := by
  classical
  unfold up; split_ifs with h
  · exact h ▸ hx.le
  · exact le_rfl

theorem dismantle_D {D : Set α} {F : α → α → α} (hD : ∀ a b, a ≤ b → b ∈ D → a ∈ D)
    {x xp : α} (hx : x < xp) (hcov : ∀ y, x < y → xp ≤ y) (hxpD : xp ∈ D) (h : Cx D F) :
    Cx {y : {y : α // y ≠ x} | y.1 ∈ D}
      (fun a b => ⟨up x xp (F a.1 b.1), by classical unfold up; split_ifs with h; exact hx.ne'; exact h⟩) := by
  obtain ⟨hF, nw⟩ := h
  refine ⟨fun a a' b b' ha hb => up_mono hx hcov (hF _ _ _ _ ha hb), fun a ha b hb => ⟨fun h1 => ?_, fun h2 => ?_⟩⟩
  · exact (nw a.1 ha b.1 hb).1 ((le_up x xp hx _).trans h1)
  · -- b ∉ D: if F a b = x then x ∈ D (x < xp ∈ D), so b ≤ up … = xp gives nothing; argue by cases
    have h2' : b.1 ≤ up x xp (F a.1 b.1) := h2
    classical
    unfold up at h2'
    split_ifs at h2' with hfx
    · -- F a b = x ∈ D and b ≤ xp ∈ D: then b ∈ D, contradiction
      exact hb (hD _ _ h2' hxpD)
    · exact (nw a.1 ha b.1 hb).2 h2'

/-- Push `y` to `y⁻`. -/
noncomputable def down (y ym : α) (z : α) : α := by classical exact if z = y then ym else z

theorem down_mono {y ym : α} (hy : ym < y) (hcov : ∀ z, z < y → z ≤ ym) : Monotone (down y ym) := by
  classical
  intro a b hab
  unfold down
  by_cases ha : a = y <;> by_cases hb : b = y
  · simp [ha, hb]
  · simp only [ha, hb, if_true, if_false]; exact hy.le.trans (ha ▸ hab)
  · simp only [ha, hb, if_true, if_false]
    exact hcov a (lt_of_le_of_ne (hb ▸ hab) ha)
  · simp only [ha, hb, if_false]; exact hab

theorem down_le (y ym : α) (hy : ym < y) (z : α) : down y ym z ≤ z := by
  classical
  unfold down; split_ifs with h
  · exact h ▸ hy.le
  · exact le_rfl

theorem dismantle_C {D : Set α} {F : α → α → α} (hD : ∀ a b, a ≤ b → b ∈ D → a ∈ D)
    {y ym : α} (hy : ym < y) (hcov : ∀ z, z < y → z ≤ ym) (hymD : ym ∉ D) (h : Cx D F) :
    Cx {z : {z : α // z ≠ y} | z.1 ∈ D}
      (fun a b => ⟨down y ym (F a.1 b.1), by classical unfold down; split_ifs with h; exact hy.ne; exact h⟩) := by
  obtain ⟨hF, nw⟩ := h
  refine ⟨fun a a' b b' ha hb => down_mono hy hcov (hF _ _ _ _ ha hb), fun a ha b hb => ⟨fun h1 => ?_, fun h2 => ?_⟩⟩
  · have h1' : down y ym (F a.1 b.1) ≤ a.1 := h1
    classical
    unfold down at h1'
    split_ifs at h1' with hfy
    · exact hymD (hD _ _ h1' ha)
    · exact (nw a.1 ha b.1 hb).1 h1'
  · have h2' : b.1 ≤ down y ym (F a.1 b.1) := h2
    exact (nw a.1 ha b.1 hb).2 (h2'.trans (down_le y ym hy _))

end Mordor.Dismantle
