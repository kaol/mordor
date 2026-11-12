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

/-! ### Rigid maps with the lower heights (§34.3z¹⁶⁰)

`OHCxR` adds the rigid hypotheses (`a ⊥ = ⊥`, `b ⊤ = ⊤`, no interior diagonal fixed point) and the two lower-height
consequences used by `oh_ground.py rigid ih`: `diag` (`OrbitHeight.diagGood_of_lower`) and `post`
(`OrbitHeight.top_mem_of_good_post`). Its fields are hypotheses here; `OHRigid.ohCxR_of_orbit` proves them for the true
orbit `M k := R_k` of a rigid map, given `OHAt` below `H`. -/

/-- A rigid orbit-height counterexample with the lower-height consequences. -/
structure OHCxR (F : α → α → α) (M : ℕ → Set α) (H : ℕ) : Prop extends OHCx F M H where
  rigA : ∀ y, y ≤ F ⊥ y → y ≤ ⊥
  rigB : ∀ x, F x ⊤ ≤ x → ⊤ ≤ x
  rigD : ∀ c, F c c ≤ c → c ≤ F c c → c ≤ ⊥ ∨ ⊤ ≤ c
  diag : ∀ k c, F c c ≤ c → ¬ ⊤ ≤ c → ¬ chainTo c (k + 1) → c ∈ M k
  post : ∀ j c, c ≤ F c c → ¬ c ≤ ⊥ → c ∈ M j → chainTo c j → ⊤ ∈ M H

theorem oh_rigA (R : OHCxR F M H) {z y a : α} (hz : z = ⊥) (ha : a = F z y) :
    (!decide (y ≤ a) || decide (y ≤ z)) = true := by
  by_cases h : y ≤ a
  · simp [hz ▸ R.rigA y (hz ▸ ha ▸ h)]
  · simp [h]
theorem oh_rigB (R : OHCxR F M H) {w x a : α} (hw : w = ⊤) (ha : a = F x w) :
    (!decide (a ≤ x) || decide (w ≤ x)) = true := by
  by_cases h : a ≤ x
  · simp [hw ▸ R.rigB x (hw ▸ ha ▸ h)]
  · simp [h]
theorem oh_rigD (R : OHCxR F M H) {z w c a : α} (hz : z = ⊥) (hw : w = ⊤) (ha : a = F c c) :
    (!decide (a ≤ c) || !decide (c ≤ a) || decide (c ≤ z) || decide (w ≤ c)) = true := by
  by_cases h1 : a ≤ c
  · by_cases h2 : c ≤ a
    · rcases R.rigD c (ha ▸ h1) (ha ▸ h2) with h | h
      · simp [hz, h]
      · simp [hw, h]
    · simp [h2]
  · simp [h1]
theorem oh_diag (R : OHCxR F M H) {w c a : α} (hw : w = ⊤) (ha : a = F c c) (k k' : ℕ) (hk : k' = k + 1) :
    (!decide (a ≤ c) || decide (w ≤ c) || decide (chainTo c k') || decide (c ∈ M k)) = true := by
  subst hk
  by_cases h1 : a ≤ c
  · by_cases h2 : w ≤ c
    · simp [h2]
    · by_cases h3 : chainTo c (k + 1)
      · simp [h3]
      · simp [R.diag k c (ha ▸ h1) (hw ▸ h2) h3]
  · simp [h1]
theorem oh_post (R : OHCxR F M H) {z w c a : α} (hz : z = ⊥) (hw : w = ⊤) (ha : a = F c c) (j : ℕ) :
    (!decide (c ≤ a) || decide (c ≤ z) || !decide (c ∈ M j) || !decide (chainTo c j) || decide (w ∈ M H)) = true := by
  by_cases h1 : c ≤ a
  · by_cases h2 : c ≤ z
    · simp [h2]
    · by_cases h3 : c ∈ M j
      · by_cases h4 : chainTo c j
        · simp [hw ▸ R.post j c (ha ▸ h1) (hz ▸ h2) h3 h4]
        · simp [h4]
      · simp [h3]
  · simp [h1]

end Mordor.Ground
