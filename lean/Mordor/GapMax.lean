import Mordor.GapPotential

/-!
# Maximum-gap descent (round 26, §34.3z¹²⁶)

ChatGPT brief "global gap descent and compatible monotone selection", Part A.

* `parent_iff_max_drop`: for nonempty finite sets `B`, `B'` and any `φ`, "every element of `B'` has some element of
  `B` with strictly larger `φ`" iff `max_{B'} φ < max_B φ`.
* `badSet T`: the bad pairs of a stage, as a `Finset`. `cut_of_max_gap_drop` (**max-gap drop ⇒ Cut**): if, for every
  stage `n + 1` that has bad pairs and is not stuck, stage `n` has bad pairs and the maximum gap
  `height y + (H − height x)` strictly drops, then `F` has a witness (via `cut_of_gap_parent`). The parent need not
  be causally related to the child.
-/

namespace Mordor.MaxGap
open Finset Mordor.SeparatorStages Mordor.GapPotential

set_option linter.unusedSectionVars false

/-- **Parent existence ⟺ maximum drop.** -/
theorem parent_iff_max_drop {ι : Type*} {B B' : Finset ι} (hB : B.Nonempty) (hB' : B'.Nonempty) (φ : ι → ℕ) :
    (∀ c ∈ B', ∃ p ∈ B, φ c < φ p) ↔ B'.sup' hB' φ < B.sup' hB φ := by
  constructor
  · intro h
    obtain ⟨c, hc, hce⟩ := Finset.exists_mem_eq_sup' hB' φ
    obtain ⟨p, hp, hlt⟩ := h c hc
    rw [hce]; exact hlt.trans_le (Finset.le_sup' φ hp)
  · intro h c hc
    obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_sup' hB φ
    exact ⟨p, hp, (Finset.le_sup' φ hc).trans_lt (hpe ▸ h)⟩

variable {β : Type*} [Lattice β] [BoundedOrder β] [DecidableEq β] [DecidableLE β] {F : β → β → β} {D : Set β}

/-- The bad pairs of a stage. -/
noncomputable def badSet (F : β → β → β) (D : Set β) (T : Finset β) : Finset (β × β) := by
  classical exact (T ×ˢ T).filter fun p => Bad F D T p.1 p.2

theorem mem_badSet {T : Finset β} {p : β × β} : p ∈ badSet F D T ↔ Bad F D T p.1 p.2 := by
  classical
  unfold badSet
  rw [Finset.mem_filter, Finset.mem_product]
  exact ⟨fun h => h.2, fun h => ⟨⟨h.1, h.2.2.1⟩, h⟩⟩

/-- The gap potential on pairs. -/
noncomputable def gap (H : ℕ) (p : β × β) : ℕ := height H p.2 + (H - height H p.1)

/-- **Maximum-gap drop ⇒ Cut.** -/
theorem cut_of_max_gap_drop (H : ℕ) (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) {T : ℕ → Finset β} (hr : Run F D T)
    (hdrop : ∀ n (h' : (badSet F D (T (n + 1))).Nonempty),
      (∃ a b, Bad F D (T (n + 1)) a b ∧ b ≤ F a b) ∨
      ∃ h : (badSet F D (T n)).Nonempty, (badSet F D (T (n + 1))).sup' h' (gap H) < (badSet F D (T n)).sup' h (gap H)) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  refine cut_of_gap_parent H hF hD hbot htop hr fun n x' y' hb => ?_
  have h' : (badSet F D (T (n + 1))).Nonempty := ⟨(x', y'), mem_badSet.2 hb⟩
  rcases hdrop n h' with hst | ⟨h, hlt⟩
  · exact Or.inl hst
  · right
    obtain ⟨p, hp, hlt'⟩ := (parent_iff_max_drop h h' (gap H)).2 hlt (x', y') (mem_badSet.2 hb)
    exact ⟨p.1, p.2, mem_badSet.1 hp, hlt'⟩

/-- **Nested separators shrink the gap** (§34.3z¹²⁷). A separator `s ≤ y` of a pair `(x, y)` (so `y ≰ s`) lies
strictly below `y`; at edge-height `≤ H` the child `(x, s)` has strictly smaller gap. This is the mechanism of the
descending runs along the `⊥` row; it is not a selection rule (the nested-first rule fails, §34.3z¹²⁷). -/
theorem nested_child_gap {H : ℕ} (hn : Mordor.Ground.NoChain β (H + 1)) {x y s : β} (hsy : s ≤ y) (hys : ¬ y ≤ s) :
    gap H (x, s) < gap H (x, y) := by
  have h := height_strictMono hn (lt_of_le_of_ne hsy fun h => hys (h ▸ le_rfl))
  simp only [gap]; omega

end Mordor.MaxGap
