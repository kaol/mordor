import Mordor.GapMax

/-!
# The finite state graph of the separator process (round 26, §34.3z¹³⁰)

ChatGPT brief "shortest-run descent", Report A.

* `Goal T`: no bad pair, or a stuck bad pair (`y ≤ F x y`) — the stops of the process.
* `step_exists_of_not_goal` (ACC): a non-goal stage has a `Step` (no witness is assumed: a non-stuck bad pair has
  `F x y` itself as a separator, and ACC gives a maximal one).
* `Reach k T`: a goal is reachable from `T` in at most `k` steps. `reach_finite`: on a finite lattice every `T`
  reaches a goal within `card α − |T|` steps (steps from non-goal stages grow `T` strictly, `step_strict`).
* `dist T`: the completion distance (least such `k`); `reach_dist`, `dist_le`.
* `optimal_successor`: a non-goal `T` has a step `T'` with `dist T' + 1 = dist T`, and `dist T ≤ dist T' + 1` for every
  step. (`dist` is defined only through `Reach`; on a witness-free infinite structure no goal is reachable, so the
  distance — and with it "shortest run" — exists only on lattices where `reach_finite`-type bounds hold.)
-/

namespace Mordor.ShortestRun
open Finset Mordor.SeparatorStages

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] [DecidableEq α] {F : α → α → α} {D : Set α}

variable (F D) in
/-- The stops of the process. -/
def Goal (T : Finset α) : Prop := (∀ x y, ¬ Bad F D T x y) ∨ ∃ x y, Bad F D T x y ∧ y ≤ F x y

/-- A non-goal stage has a refinement step (ACC). -/
theorem step_exists_of_not_goal [WellFoundedGT α] {T : Finset α} (hT : ¬ Goal F D T) : ∃ T', Step F D T T' := by
  classical
  have hns : ∀ x y, Bad F D T x y → ¬ y ≤ F x y := fun x y hb h => hT (Or.inr ⟨x, y, hb, h⟩)
  have hsep : ∀ p : α × α, ∃ s, Bad F D T p.1 p.2 → IsMaxSep F p.1 p.2 s := fun p => by
    by_cases hb : Bad F D T p.1 p.2
    · obtain ⟨s, ⟨h1, h2⟩, hmax⟩ := (wellFounded_gt (α := α)).has_min {s | F p.1 p.2 ≤ s ∧ ¬ p.2 ≤ s}
        ⟨F p.1 p.2, le_rfl, hns _ _ hb⟩
      exact ⟨s, fun _ => ⟨h1, h2, fun t hst => by
        by_contra hyt; exact hmax t ⟨h1.trans hst.le, hyt⟩ hst⟩⟩
    · exact ⟨⊤, fun h => absurd h hb⟩
  choose sep hsep using hsep
  let P := (T ×ˢ T).filter fun p => Bad F D T p.1 p.2
  refine ⟨meetClose (T ∪ P.image sep), P.image sep, rfl, fun s hs => ?_, fun x y hb => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hs
    have hb := (Finset.mem_filter.1 hp).2
    exact ⟨p.1, p.2, hb, hsep p hb⟩
  · exact ⟨sep (x, y), Finset.mem_image.2 ⟨(x, y), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hb.1, hb.2.2.1⟩, hb⟩,
      rfl⟩, hsep (x, y) hb⟩

variable (F D) in
/-- A goal is reachable within `k` steps. -/
def Reach : ℕ → Finset α → Prop
  | 0, T => Goal F D T
  | k + 1, T => Goal F D T ∨ ∃ T', Step F D T T' ∧ Reach k T'

theorem reach_mono : ∀ {k : ℕ} {T : Finset α}, Reach F D k T → Reach F D (k + 1) T
  | 0, _, h => Or.inl h
  | _ + 1, _, Or.inl h => Or.inl h
  | _ + 1, _, Or.inr ⟨T', hs, h⟩ => Or.inr ⟨T', hs, reach_mono h⟩

theorem goal_of_reach_zero {T : Finset α} (h : Reach F D 0 T) : Goal F D T := h

/-- **Finiteness.** On a finite lattice every stage reaches a goal within `card α − |T|` steps. -/
theorem reach_finite [Fintype α] [WellFoundedGT α] :
    ∀ n (T : Finset α), Fintype.card α - T.card ≤ n → Reach F D n T := by
  intro n
  induction n with
  | zero =>
    intro T hT
    by_contra hg
    obtain ⟨T', hs⟩ := step_exists_of_not_goal (F := F) (D := D) hg
    have hbad : ∃ x y, Bad F D T x y := by
      by_contra h; push_neg at h; exact hg (Or.inl h)
    obtain ⟨x, y, hb⟩ := hbad
    have hlt := Finset.card_lt_card (step_strict hs hb)
    have := Finset.card_le_univ T'
    omega
  | succ n ih =>
    intro T hT
    by_cases hg : Goal F D T
    · exact Or.inl hg
    · obtain ⟨T', hs⟩ := step_exists_of_not_goal (F := F) (D := D) hg
      have hbad : ∃ x y, Bad F D T x y := by
        by_contra h; push_neg at h; exact hg (Or.inl h)
      obtain ⟨x, y, hb⟩ := hbad
      have hlt := Finset.card_lt_card (step_strict hs hb)
      exact Or.inr ⟨T', hs, ih T' (by omega)⟩

theorem reach_exists [Fintype α] [WellFoundedGT α] (T : Finset α) : ∃ k, Reach F D k T :=
  ⟨_, reach_finite (F := F) (D := D) _ T le_rfl⟩

variable [Fintype α] [WellFoundedGT α]

variable (F D) in
/-- The completion distance. -/
noncomputable def dist (T : Finset α) : ℕ := by
  classical exact Nat.find (reach_exists (F := F) (D := D) T)

theorem reach_dist (T : Finset α) : Reach F D (dist F D T) T := by
  classical
  unfold dist; exact Nat.find_spec (reach_exists (F := F) (D := D) T)

theorem dist_le {T : Finset α} {k : ℕ} (h : Reach F D k T) : dist F D T ≤ k := by
  classical
  unfold dist; exact Nat.find_min' _ h

/-- **Optimal successor.** -/
theorem optimal_successor {T : Finset α} (hT : ¬ Goal F D T) :
    (∃ T', Step F D T T' ∧ dist F D T' + 1 = dist F D T) ∧
      ∀ T', Step F D T T' → dist F D T ≤ dist F D T' + 1 := by
  have hle : ∀ T', Step F D T T' → dist F D T ≤ dist F D T' + 1 := fun T' hs =>
    dist_le (Or.inr ⟨T', hs, reach_dist T'⟩)
  refine ⟨?_, hle⟩
  have hR := reach_dist (F := F) (D := D) T
  rcases hk : dist F D T with _ | k
  · rw [hk] at hR; exact absurd hR hT
  · rw [hk] at hR
    rcases hR with h | ⟨T', hs, hR'⟩
    · exact absurd h hT
    · refine ⟨T', hs, le_antisymm ?_ (hk ▸ hle T' hs)⟩
      have := dist_le hR'; omega

/-- **Downward absoluteness of maximal separators** (Report B). If `s` is a maximal separator of `(x, y)` in `α` and `P`
is any subset containing `s`, then `s` is maximal among the elements of `P` not above `y`. The converse fails: a
subset can have maximal separators that are not maximal in `α` (e.g. `{0, 1, 3}` in the chain `0 < 1 < 2 < 3`,
`y = 3`, response `1`: in the subset `1` is maximal, in the chain only `2` is). -/
theorem maxSep_restrict {G : α → α → α} {x y s : α} (hs : IsMaxSep G x y s) (P : Set α) :
    ∀ t ∈ P, s < t → y ≤ t := fun t _ h => hs.2.2 t h

end Mordor.ShortestRun
