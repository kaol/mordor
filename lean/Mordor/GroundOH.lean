import Mordor.GroundCut

/-!
# Ground clause lemmas for the orbit-height theory `OH_H` (log §34.3z¹⁵⁹)

An *orbit-height counterexample* (`OHCx F M H`) is a bounded poset with a monotone `F` and sets `M k` obeying the
sound Horn rules of the orbit `R_0 = ↓⊥`, `R_{k+1} = ↓(R_k ∪ a(R_k) ∪ b⁻¹(R_k))`, with `⊤ ∉ M H`:
`t ≤ ⊥ → t ∈ M 0`, `M k ⊆ M (k+1)`, down-closure, the b-rule `x ∈ M k → F x y ≤ x → y ∈ M (k+1)` and the a-rule
`x ∈ M k → y ≤ F x y → y ∈ M (k+1)`. Each lemma below is one clause family of `experiments/sat/oh_ground.py`; the
order and chain families are those of `GroundCut.lean`. A `bv_decide` refutation of finitely many such clauses
proves that no counterexample of the given height exists (`OHHeight4.lean`); `OrbitHeight.ohAt_four` transfers it
to the orbit of a complete lattice.
-/

namespace Mordor.Ground
open Classical
set_option linter.unusedSectionVars false

variable {α : Type*} [PartialOrder α] [OrderBot α] [OrderTop α]

/-- An orbit-height counterexample. -/
structure OHCx (F : α → α → α) (M : ℕ → Set α) (H : ℕ) : Prop where
  mono : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y'
  base : ∀ t, t ≤ ⊥ → t ∈ M 0
  incr : ∀ k t, t ∈ M k → t ∈ M (k + 1)
  down : ∀ k s t, s ≤ t → t ∈ M k → s ∈ M k
  brule : ∀ k x y, x ∈ M k → F x y ≤ x → y ∈ M (k + 1)
  arule : ∀ k x y, x ∈ M k → y ≤ F x y → y ∈ M (k + 1)
  top : ⊤ ∉ M H

variable {F : α → α → α} {M : ℕ → Set α} {H : ℕ}

theorem OHCx.mem_of_zero (O : OHCx F M H) {t : α} (h : t ∈ M 0) : ∀ k, t ∈ M k
  | 0 => h
  | k + 1 => O.incr k t (O.mem_of_zero h k)

theorem oh_topbot (O : OHCx F M H) {x y : α} (hx : x = ⊤) (hy : y = ⊥) : (!decide (x ≤ y)) = true := by
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, hx, hy]
  exact fun h => O.top (O.mem_of_zero (O.base ⊤ h) H)
theorem oh_top (O : OHCx F M H) {x : α} (hx : x = ⊤) : (!decide (x ∈ M H)) = true := by
  simpa [hx] using O.top
theorem oh_base (O : OHCx F M H) {z : α} (hz : z = ⊥) (t : α) : (!decide (t ≤ z) || decide (t ∈ M 0)) = true := by
  by_cases h : t ≤ z
  · simp [O.base t (hz ▸ h)]
  · simp [h]
theorem oh_incr (O : OHCx F M H) (k k' : ℕ) (hk : k' = k + 1) (t : α) :
    (!decide (t ∈ M k) || decide (t ∈ M k')) = true := by
  subst hk
  by_cases h : t ∈ M k
  · simp [O.incr k t h]
  · simp [h]
theorem oh_down (O : OHCx F M H) (k : ℕ) (s t : α) :
    (!decide (s ≤ t) || !decide (t ∈ M k) || decide (s ∈ M k)) = true := by
  by_cases h1 : s ≤ t
  · by_cases h2 : t ∈ M k
    · simp [O.down k s t h1 h2]
    · simp [h2]
  · simp [h1]
theorem oh_b (O : OHCx F M H) {a x y : α} (ha : a = F x y) (k k' : ℕ) (hk : k' = k + 1) :
    (!decide (x ∈ M k) || !decide (a ≤ x) || decide (y ∈ M k')) = true := by
  subst hk
  by_cases h1 : x ∈ M k
  · by_cases h2 : a ≤ x
    · simp [O.brule k x y h1 (ha ▸ h2)]
    · simp [h2]
  · simp [h1]
theorem oh_a (O : OHCx F M H) {a x y : α} (ha : a = F x y) (k k' : ℕ) (hk : k' = k + 1) :
    (!decide (x ∈ M k) || !decide (y ≤ a) || decide (y ∈ M k')) = true := by
  subst hk
  by_cases h1 : x ∈ M k
  · by_cases h2 : y ≤ a
    · simp [O.arule k x y h1 (ha ▸ h2)]
    · simp [h2]
  · simp [h1]
theorem oh_mono (O : OHCx F M H) {a b x1 y1 x2 y2 : α} (ha : a = F x1 y1) (hb : b = F x2 y2) :
    (!decide (x1 ≤ x2) || !decide (y1 ≤ y2) || decide (a ≤ b)) = true := by
  by_cases h1 : x1 ≤ x2
  · by_cases h2 : y1 ≤ y2
    · simp [ha, hb, O.mono _ _ _ _ h1 h2]
    · simp [h2]
  · simp [h1]

end Mordor.Ground
