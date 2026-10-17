import Mathlib.Order.FixedPoints

/-!
# Derived maps of a monotone bifunction (log §13–§14)

For monotone `F : α → α → α` on a complete lattice: `a x = νY. F x Y`, `b y = μX. F X y`, `m = μ a`, `n = ν b`.
Stability (L1, L2), lower commutation (I1), fixed-point fusion, L3/L4 and the I2 characterization, all
unconditional.

*Erratum to §13.1.* The log's proof of L2 justifies `a (b m) ≤ b m` by "the greatest fixed point is the infimum
of pre-fixed points". That is false (it holds for the least fixed point). The correct step, used below: with
`c = b m ≤ m`, `a c ≤ a m = m`, hence `a c = F c (a c) ≤ F c m = c`. The log's L1 proof likewise asserts
`a n ≤ n ⟺ m ≤ n` without proof; `a_n` below proves `a n = n` directly by the dual argument.
-/

namespace Mordor
variable {α : Type*} [CompleteLattice α] (F : α →o α →o α)

/-- The column map `x ↦ F x y`. -/
def col (y : α) : α →o α := ⟨fun x => F x y, fun _ _ h => F.mono h y⟩

/-- `a x = νY. F x Y`, the greatest fixed point of row `x`. -/
def a : α →o α := OrderHom.gfp.comp F

/-- `b y = μX. F X y`, the least fixed point of column `y`. -/
def b : α →o α := ⟨fun y => (col F y).lfp, fun _ _ h => OrderHom.lfp.mono fun x => (F x).mono h⟩

/-- `m = μX. νY. F X Y`. -/
def m : α := (a F).lfp
/-- `n = νY. μX. F X Y`. -/
def n : α := (b F).gfp

variable {F}

theorem row_a (x : α) : F x (a F x) = a F x := (F x).map_gfp
theorem col_b (y : α) : F (b F y) y = b F y := (col F y).map_lfp
theorem le_a {x y : α} (h : y ≤ F x y) : y ≤ a F x := (F x).le_gfp h
theorem b_le {x y : α} (h : F x y ≤ x) : b F y ≤ x := (col F y).lfp_le h
theorem a_m : a F (m F) = m F := (a F).map_lfp
theorem b_n : b F (n F) = n F := (b F).map_gfp

/-- **L2 (μ-stability).** `b m = m`. -/
theorem b_m : b F (m F) = m F := by
  have hmm : F (m F) (m F) = m F := by
    have h := row_a (F := F) (m F); rwa [a_m] at h
  have hc : b F (m F) ≤ m F := b_le hmm.le
  apply le_antisymm hc
  -- m = μ a ≤ c, because c is a-pre-fixed: a c ≤ a m = m, so a c = F c (a c) ≤ F c m = c
  apply (a F).lfp_le
  have h1 : a F (b F (m F)) ≤ m F := ((a F).mono hc).trans a_m.le
  calc a F (b F (m F)) = F (b F (m F)) (a F (b F (m F))) := (row_a _).symm
    _ ≤ F (b F (m F)) (m F) := (F _).mono h1
    _ = b F (m F) := col_b _

/-- **L1 (ν-stability).** `a n = n`. -/
theorem a_n : a F (n F) = n F := by
  have hnn : F (n F) (n F) = n F := by
    have h := col_b (F := F) (n F); rwa [b_n] at h
  have hc : n F ≤ a F (n F) := le_a hnn.ge
  apply le_antisymm _ hc
  -- a n ≤ ν b, because c = a n is b-post-fixed: b c ≥ b n = n, so b c = F (b c) c ≥ F n c = c
  apply (b F).le_gfp
  have h1 : n F ≤ b F (a F (n F)) := b_n.ge.trans ((b F).mono hc)
  calc a F (n F) = F (n F) (a F (n F)) := (row_a _).symm
    _ ≤ F (b F (a F (n F))) (a F (n F)) := F.mono h1 _
    _ = b F (a F (n F)) := col_b _

/-- **I1 (lower commutation).** `μX. νY. F ≤ νY. μX. F`, for every monotone `F`. -/
theorem m_le_n : m F ≤ n F := (a F).lfp_le a_n.le

/-- **Fixed-point fusion (§14.1).** `Fix (a ∘ b) = Fix a ∩ Fix b`. -/
theorem fusion (z : α) : a F (b F z) = z ↔ a F z = z ∧ b F z = z := by
  constructor
  · intro h
    have hz : z = b F z := by
      calc z = a F (b F z) := h.symm
        _ = F (b F z) (a F (b F z)) := (row_a _).symm
        _ = F (b F z) z := by rw [h]
        _ = b F z := col_b _
    exact ⟨(congrArg (a F) hz).trans h, hz.symm⟩
  · rintro ⟨ha, hb⟩; rw [hb, ha]

/-- `m` is the least and `n` the greatest common fixed point of `a` and `b`. -/
theorem m_le_common {z : α} (ha : a F z = z) : m F ≤ z := (a F).lfp_le_fixed ha
theorem common_le_n {z : α} (hb : b F z = z) : z ≤ n F := (b F).le_gfp hb.ge

/-- **L3.** `μ (a ∘ b) = μ a`. -/
theorem lfp_ab : ((a F).comp (b F)).lfp = m F := by
  apply le_antisymm
  · apply OrderHom.lfp_le_fixed; show a F (b F (m F)) = m F; rw [b_m, a_m]
  · have h := ((a F).comp (b F)).map_lfp
    exact m_le_common ((fusion _).1 h).1

/-- **L4.** `ν (a ∘ b) = ν b`. -/
theorem gfp_ab : ((a F).comp (b F)).gfp = n F := by
  apply le_antisymm
  · have h := ((a F).comp (b F)).map_gfp
    exact common_le_n ((fusion _).1 h).2
  · apply OrderHom.le_gfp; show n F ≤ a F (b F (n F)); rw [b_n, a_n]

/-- **I2 characterization (§14.1).** `m = n` iff `a` and `b` have exactly one common fixed point. -/
theorem m_eq_n_iff : m F = n F ↔ ∀ z, a F z = z → b F z = z → z = m F := by
  constructor
  · intro h z ha hb; exact le_antisymm (h ▸ common_le_n hb) (m_le_common ha)
  · intro h; exact (h _ a_n b_n).symm

/-- **Realizability Criterion, row half (§24.1).** `a' = a_F` iff the pins `F x (a' x) = a' x` hold and every
row fixed point lies below `a' x` (the greatest-fixed-point exclusion). No finiteness is needed. -/
theorem a_eq_iff (a' : α → α) :
    (∀ x, a F x = a' x) ↔ ∀ x, F x (a' x) = a' x ∧ ∀ y, F x y = y → y ≤ a' x := by
  constructor
  · intro h x; rw [← h x]; exact ⟨row_a x, fun y hy => le_a hy.ge⟩
  · intro h x
    exact le_antisymm ((h x).2 _ (row_a x)) (le_a (h x).1.ge)

/-- **Realizability Criterion, column half (§24.1).** -/
theorem b_eq_iff (b' : α → α) :
    (∀ y, b F y = b' y) ↔ ∀ y, F (b' y) y = b' y ∧ ∀ x, F x y = x → b' y ≤ x := by
  constructor
  · intro h y; rw [← h y]; exact ⟨col_b y, fun x hx => b_le hx.le⟩
  · intro h y
    exact le_antisymm (b_le (h y).1.le) ((h y).2 _ (col_b y))

end Mordor
