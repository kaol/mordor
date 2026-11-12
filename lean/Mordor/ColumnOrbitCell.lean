import Mordor.OrbitHeight

/-!
# The column orbit criterion for interval cells (round 26, §34.3z¹⁵³)

For `m` fix the column map `g y = m ⊔ F m y` and its descending orbit from the top,
`colOrb F m n = g^[n] ⊤`. It lies above `m`, decreases, and lies above every post-fixed point of `g`.

* `ic_of_colOrb_eq`: if the orbit reaches `m` (and `m ≠ ⊤`), the last value above `m` is a **lower cell**:
  `m < y ∧ F m y ≤ m`. No chain condition is needed.
* `colOrb_dichotomy` (`WellFoundedLT α`): the orbit stabilises at the greatest fixed point `y*` of `g`
  (`∀ z, z ≤ g z → z ≤ y*`), and either `m` has an interval cell, or `m < y*`, `m ⊔ F m y* = y*`, and
  `F m y*` is **incomparable** to `m`. In the case `m ≤ F m y*` one gets `F m y* = y*`, an upper cell.

So `GFP(m)` (`y* = m` or `F m y* = y*`) implies `IC(m)`; the converse fails per element (log §34.3z¹⁵³).
-/

namespace Mordor.OrbitHeight

set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

/-- The descending column orbit `⊤, m ⊔ F(m, ⊤), …`. -/
def colOrb (F : α →o α →o α) (m : α) (n : ℕ) : α := (fun y => m ⊔ F m y)^[n] ⊤

theorem colOrb_zero (m : α) : colOrb F m 0 = ⊤ := rfl

theorem colOrb_succ (m : α) (n : ℕ) : colOrb F m (n + 1) = m ⊔ F m (colOrb F m n) :=
  Function.iterate_succ_apply' _ _ _

theorem le_colOrb (m : α) : ∀ n, m ≤ colOrb F m n
  | 0 => le_top
  | n + 1 => by rw [colOrb_succ]; exact le_sup_left

theorem colOrb_succ_le (m : α) : ∀ n, colOrb F m (n + 1) ≤ colOrb F m n
  | 0 => le_top
  | n + 1 => calc
      colOrb F m (n + 2) = m ⊔ F m (colOrb F m (n + 1)) := colOrb_succ m (n + 1)
      _ ≤ m ⊔ F m (colOrb F m n) := sup_le_sup_left ((F m).mono (colOrb_succ_le m n)) _
      _ = colOrb F m (n + 1) := (colOrb_succ m n).symm

/-- Post-fixed points of the column map lie below the whole orbit. -/
theorem post_le_colOrb {m z : α} (hz : z ≤ m ⊔ F m z) : ∀ n, z ≤ colOrb F m n
  | 0 => le_top
  | n + 1 => by
    rw [colOrb_succ]
    exact hz.trans (sup_le_sup_left ((F m).mono (post_le_colOrb hz n)) _)

/-- **Lower cell.** If the column orbit reaches `m ≠ ⊤`, its last value above `m` is a lower cell. -/
theorem ic_of_colOrb_eq {m : α} (ht : m ≠ ⊤) {n : ℕ} (hn : colOrb F m n = m) :
    ∃ y, m < y ∧ F m y ≤ m := by
  classical
  have hex : ∃ n, colOrb F m n = m := ⟨n, hn⟩
  have h0 : Nat.find hex ≠ 0 := fun h => ht (by
    have := Nat.find_spec hex; rw [h, colOrb_zero] at this; exact this.symm)
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hjm : colOrb F m j ≠ m := Nat.find_min hex (by omega)
  have hj1 : colOrb F m (j + 1) = m := hj ▸ Nat.find_spec hex
  refine ⟨colOrb F m j, lt_of_le_of_ne (le_colOrb m j) (Ne.symm hjm), ?_⟩
  rw [colOrb_succ] at hj1
  exact le_sup_right.trans hj1.le

/-- The column orbit stabilises (no infinite descending chain). -/
theorem colOrb_stable [WellFoundedLT α] (m : α) : ∃ n, colOrb F m (n + 1) = colOrb F m n := by
  obtain ⟨y, ⟨n, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := α)).has_min (Set.range (colOrb F m)) ⟨_, 0, rfl⟩
  exact ⟨n, (colOrb_succ_le m n).eq_or_lt.resolve_right (hmin _ ⟨n + 1, rfl⟩)⟩

/-- **The column orbit dichotomy.** Either `m` has an interval cell, or the greatest fixed point `y*` of
`y ↦ m ⊔ F m y` is strictly above `m` with `F m y*` incomparable to `m`. -/
theorem colOrb_dichotomy [WellFoundedLT α] {m : α} (ht : m ≠ ⊤) :
    (∃ y, m < y ∧ (F m y ≤ m ∨ y ≤ F m y)) ∨
      ∃ n, m < colOrb F m n ∧ m ⊔ F m (colOrb F m n) = colOrb F m n ∧
        (∀ z, z ≤ m ⊔ F m z → z ≤ colOrb F m n) ∧
        ¬ m ≤ F m (colOrb F m n) ∧ ¬ F m (colOrb F m n) ≤ m := by
  obtain ⟨n, hn⟩ := colOrb_stable (F := F) m
  have hfix : m ⊔ F m (colOrb F m n) = colOrb F m n := (colOrb_succ m n).symm.trans hn
  by_cases hym : colOrb F m n = m
  · obtain ⟨y', h1, h2⟩ := ic_of_colOrb_eq (F := F) ht (n := n) hym
    exact Or.inl ⟨y', h1, Or.inl h2⟩
  have hlt : m < colOrb F m n := lt_of_le_of_ne (le_colOrb m n) (Ne.symm hym)
  by_cases hup : m ≤ F m (colOrb F m n)
  · exact Or.inl ⟨_, hlt, Or.inr (hfix.symm.trans (sup_eq_right.mpr hup)).le⟩
  by_cases hlo : F m (colOrb F m n) ≤ m
  · exact Or.inl ⟨_, hlt, Or.inl hlo⟩
  exact Or.inr ⟨n, hlt, hfix, fun z hz => post_le_colOrb hz n, hup, hlo⟩

end Mordor.OrbitHeight
