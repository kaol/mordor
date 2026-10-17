import Mordor.Cut
import Std.Tactic.BVDecide

/-!
# Ground clause lemmas for the cut theory `C_H^≤` (log §31.5, §34.3f)

A *cut counterexample* is a bounded poset with a monotone `F`, a down-set `D ∋ ⊥`, `⊤ ∉ D`, and no witness. Each
lemma below is one clause family of `experiments/sat/cut_ground.py`, stated as a Boolean identity in the atoms
`decide (x ≤ y)`, `decide (x ∈ D)`, `decide (chainTo x k)`. A machine refutation of finitely many such ground
clauses (checked by `bv_decide`, which replays a CaDiCaL LRAT proof in the kernel) is then a proof that no cut
counterexample of the given height exists. See `CutHeight4.lean`.
-/

namespace Mordor.Ground
open Classical
set_option linter.unusedSectionVars false

variable {α : Type*} [PartialOrder α] [OrderBot α] [OrderTop α]

/-- `chainTo x k`: a strict chain of `k + 1` elements ends at `x`. -/
def chainTo : α → ℕ → Prop
  | _, 0 => True
  | x, k + 1 => ∃ y, y < x ∧ chainTo y k

/-- No strict chain of `n + 1` elements (edge-height ≤ `n - 1`). -/
def NoChain (α : Type*) [PartialOrder α] (n : ℕ) : Prop := ∀ x : α, ¬ chainTo x n

/-- A cut counterexample: the negation of the Cut Lemma for one `F` and one down-set `D`. -/
structure CutCx (F : α → α → α) (D : Set α) : Prop where
  mono : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y'
  down : ∀ x y, x ≤ y → y ∈ D → x ∈ D
  bot : ⊥ ∈ D
  top : ⊤ ∉ D
  nowit : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y

variable {F : α → α → α} {D : Set α}

theorem cl_refl (x : α) : decide (x ≤ x) = true := by simp
theorem cl_bot {x : α} (h : x = ⊥) (y : α) : decide (x ≤ y) = true := by simp [h]
theorem cl_top {y : α} (h : y = ⊤) (x : α) : decide (x ≤ y) = true := by simp [h]
theorem cl_topbot (H : CutCx F D) {x y : α} (hx : x = ⊤) (hy : y = ⊥) : (!decide (x ≤ y)) = true := by
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, hx, hy]
  exact fun h => H.top (H.down _ _ h H.bot)
theorem cl_dbot (H : CutCx F D) {x : α} (hx : x = ⊥) : decide (x ∈ D) = true := by simpa [hx] using H.bot
theorem cl_dtop (H : CutCx F D) {x : α} (hx : x = ⊤) : (!decide (x ∈ D)) = true := by simpa [hx] using H.top
theorem cl_trans (x y z : α) : (!decide (x ≤ y) || !decide (y ≤ z) || decide (x ≤ z)) = true := by
  by_cases h1 : x ≤ y
  · by_cases h2 : y ≤ z
    · simp [le_trans h1 h2]
    · simp [h2]
  · simp [h1]
theorem cl_mono (H : CutCx F D) {a b x1 y1 x2 y2 : α} (ha : a = F x1 y1) (hb : b = F x2 y2) :
    (!decide (x1 ≤ x2) || !decide (y1 ≤ y2) || decide (a ≤ b)) = true := by
  by_cases h1 : x1 ≤ x2
  · by_cases h2 : y1 ≤ y2
    · simp [ha, hb, H.mono _ _ _ _ h1 h2]
    · simp [h2]
  · simp [h1]
theorem cl_down (H : CutCx F D) (p q : α) : (!decide (p ≤ q) || !decide (q ∈ D) || decide (p ∈ D)) = true := by
  by_cases h1 : p ≤ q
  · by_cases h2 : q ∈ D
    · simp [H.down _ _ h1 h2]
    · simp [h2]
  · simp [h1]
theorem cl_now1 (H : CutCx F D) {a s t : α} (ha : a = F s t) :
    (!decide (s ∈ D) || decide (t ∈ D) || !decide (a ≤ s)) = true := by
  by_cases h1 : s ∈ D
  · by_cases h2 : t ∈ D
    · simp [h2]
    · simp [ha, h1, h2, (H.nowit s h1 t h2).1]
  · simp [h1]
theorem cl_now2 (H : CutCx F D) {a s t : α} (ha : a = F s t) :
    (!decide (s ∈ D) || decide (t ∈ D) || !decide (t ≤ a)) = true := by
  by_cases h1 : s ∈ D
  · by_cases h2 : t ∈ D
    · simp [h2]
    · simp [ha, h1, h2, (H.nowit s h1 t h2).2]
  · simp [h1]
theorem cl_rank (p q : α) (k k' : ℕ) (hk : k' = k + 1) :
    (!decide (p ≤ q) || decide (q ≤ p) || !decide (chainTo p k) || decide (chainTo q k')) = true := by
  subst hk
  by_cases h1 : p ≤ q
  · by_cases h2 : q ≤ p
    · simp [h2]
    · by_cases h3 : chainTo p k
      · have : chainTo q (k + 1) := ⟨p, lt_of_le_of_ne h1 (fun h => h2 (h ▸ le_rfl)), h3⟩
        simp [this]
      · simp [h3]
  · simp [h1]
theorem cl_rank0 (p q : α) : (!decide (p ≤ q) || decide (q ≤ p) || decide (chainTo q 1)) = true := by
  by_cases h1 : p ≤ q
  · by_cases h2 : q ≤ p
    · simp [h2]
    · have : chainTo q 1 := ⟨p, lt_of_le_of_ne h1 (fun h => h2 (h ▸ le_rfl)), trivial⟩
      simp [this]
  · simp [h1]
theorem cl_rankmax {n : ℕ} (hn : NoChain α n) (x : α) : (!decide (chainTo x n)) = true := by
  simpa using hn x

/-! ## Self-duality of the cut theory (for `WLOG F(⊥,⊤) ∉ D` in certificates)

The order dual of a cut counterexample `(α, F, D)` is `(αᵒᵈ, Fᵈ, Dᵈ)` with `Fᵈ x y = F y x` and `Dᵈ` the complement
of `D`; the chain bound is preserved and `Fᵈ(⊥,⊤) = F(⊥,⊤)` changes side. So a refutation of the theory plus the
unit clause `F(⊥,⊤) ∉ D` refutes the theory (`cut_of_wlog`). -/

open OrderDual

/-- A strict chain of `k + 1` elements starts at `x` (going up). -/
def chainFrom : α → ℕ → Prop
  | _, 0 => True
  | x, k + 1 => ∃ y, x < y ∧ chainFrom y k

theorem chainTo_add : ∀ (k j : ℕ) (x : α), chainFrom x k → chainTo x j → ∃ z : α, chainTo z (j + k)
  | 0, _, x, _, h => ⟨x, h⟩
  | k + 1, j, x, ⟨y, hxy, hy⟩, h => by
      obtain ⟨z, hz⟩ := chainTo_add k (j + 1) y hy ⟨x, hxy, h⟩
      exact ⟨z, by rwa [Nat.add_right_comm, Nat.add_assoc] at hz⟩

theorem chainTo_dual : ∀ (k : ℕ) (x : αᵒᵈ), chainTo x k ↔ chainFrom (ofDual x) k
  | 0, _ => Iff.rfl
  | k + 1, x => by
      constructor
      · rintro ⟨y, hyx, hy⟩; exact ⟨ofDual y, hyx, (chainTo_dual k y).1 hy⟩
      · rintro ⟨y, hxy, hy⟩; exact ⟨toDual y, hxy, (chainTo_dual k (toDual y)).2 hy⟩

theorem NoChain.dual {n : ℕ} (hn : NoChain α n) : NoChain αᵒᵈ n := fun x hx => by
  obtain ⟨z, hz⟩ := chainTo_add n 0 (ofDual x) ((chainTo_dual n x).1 hx) trivial
  exact hn z (by simpa using hz)

/-- The dual bifunction `Fᵈ x y = F y x` on `αᵒᵈ`. -/
def dualF (F : α → α → α) : αᵒᵈ → αᵒᵈ → αᵒᵈ := fun x y => toDual (F (ofDual y) (ofDual x))
/-- The dual cut: the complement, read in `αᵒᵈ`. -/
def dualD (D : Set α) : Set αᵒᵈ := {x | ofDual x ∉ D}

theorem CutCx.dual (H : CutCx F D) : CutCx (dualF F) (dualD D) where
  mono _ _ _ _ hx hy := H.mono _ _ _ _ hy hx
  down _ _ hxy hy hx := hy (H.down _ _ hxy hx)
  bot := H.top
  top := fun h => h H.bot
  nowit x hx y hy := ⟨fun h => (H.nowit (ofDual y) (not_not.mp hy) (ofDual x) hx).2 h,
                      fun h => (H.nowit (ofDual y) (not_not.mp hy) (ofDual x) hx).1 h⟩

universe u in
/-- A refutation under `F(⊥,⊤) ∉ D`, uniform in the poset, refutes every cut counterexample. -/
theorem cut_of_wlog {n : ℕ}
    (core : ∀ {β : Type u} [PartialOrder β] [OrderBot β] [OrderTop β] {G : β → β → β} {E : Set β},
      CutCx G E → NoChain β n → G ⊥ ⊤ ∉ E → False)
    {α : Type u} [PartialOrder α] [OrderBot α] [OrderTop α] {F : α → α → α} {D : Set α}
    (H : CutCx F D) (hn : NoChain α n) : False := by
  by_cases hc : F ⊥ ⊤ ∈ D
  · exact core H.dual hn.dual (fun h => h hc)
  · exact core H hn hc

theorem cl_wlog {x : α} (hx : x ∉ D) : (!decide (x ∈ D)) = true := by simpa using hx

end Mordor.Ground
