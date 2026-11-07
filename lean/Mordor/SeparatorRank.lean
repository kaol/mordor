import Mordor.SeparatorStages
import Mordor.CutHeight5
import Mathlib.Order.LatticeIntervals

/-!
# Closure ranks and causal forks of the separator process (round 26, §34.3z¹²²)

ChatGPT brief "rank-decreasing causal chains in extremal-separator refinement".

`r : α → ℕ` is any strictly monotone rank (e.g. the height function of a lattice of finite edge-height).
* `cl_antitone_family`: `T ⊆ T' ⇒ cl_{T'} z ≤ cl_T z`.
* `bad_iff_le_cl`: for a meet-closed `T ∋ ⊤`, a cross pair is bad iff `y ≤ cl_T (F x y)`.
* `response_closure_strict_drop`, `response_closure_rank_strict_drop` (**Result 1**): if `(x, y)` is bad in `T` and
  `Step T T'`, then `cl_{T'} (F x y) < cl_T (F x y)`, hence `r` strictly drops.
* `next_bad_pair_carrier` (**Result 2**, causal fork): `s` a maximal separator of `(x, y)`, `(x', y')` any pair with
  `y' ∉ D`. Either both lie below `s` (then `s ∉ D`, `s ≠ ⊤`), or `v = s ⊔ x' ⊔ y' > s` is outside `D` and above
  `y`, `x'`, `y'`. The causal hypothesis `x' ≤ s ∨ y' ≤ s` of the brief is not needed: the fork is maximality of `s`
  alone.
* `contained_branch` / `contained_branch_height6`: if `s ∉ D` and Cut holds on `↓s` (in particular when `L` has
  edge-height ≤ 6, by `cut_height5`, since `↓s` then has edge-height ≤ 5), no witness forces `F s s ≰ s`; then
  `v = s ⊔ F s s > s` lies above `y` (and so outside `D`).
* `rank_parent_stage_bound` (**RP ⇒ ∃-SB**, stuck stages exempt): for families `T₀, T₁, …` (meet-closed, `⊤ ∈ Tₙ`),
  if every bad pair of a non-stuck `Tₙ₊₁` has a bad parent in `Tₙ` with strictly larger response closure rank, and
  `r ≤ H`, then some stage `≤ H` is stuck or `T_H` has no bad pair. (RP itself is refuted, §34.3z¹²².)
-/

namespace Mordor.SeparatorRank
open Finset Mordor.FiniteQuotient Mordor.SeparatorStages

set_option linter.unusedSectionVars false

section Closure

variable {α : Type*} [Lattice α] [BoundedOrder α] [DecidableEq α] [DecidableLE α]

theorem cl_antitone_family {T T' : Finset α} (h : T ⊆ T') (z : α) : cl T' z ≤ cl T z :=
  Finset.le_inf fun _ ht => cl_le (h (Finset.mem_filter.1 ht).1) (Finset.mem_filter.1 ht).2

variable {F : α → α → α} {D : Set α}

theorem bad_iff_le_cl {T : Finset α} (htT : ⊤ ∈ T) (hcl : ∀ a ∈ T, ∀ b ∈ T, a ⊓ b ∈ T) {x y : α} :
    Bad F D T x y ↔ x ∈ T ∧ x ∈ D ∧ y ∈ T ∧ y ∉ D ∧ y ≤ cl T (F x y) := by
  have key := Mordor.ExtremalSeparators.separated_iff_cl htT hcl (F x y) y
  unfold Bad Separated
  constructor
  · rintro ⟨a, b, c, d, e⟩; exact ⟨a, b, c, d, not_not.1 (fun h => e (key.2 h))⟩
  · rintro ⟨a, b, c, d, e⟩; exact ⟨a, b, c, d, fun h => key.1 h e⟩

/-- **Strict response-closure drop.** -/
theorem response_closure_strict_drop {T T' : Finset α} (htT : ⊤ ∈ T) (hcl : ∀ a ∈ T, ∀ b ∈ T, a ⊓ b ∈ T)
    (h : Step F D T T') {x y : α} (hb : Bad F D T x y) : cl T' (F x y) < cl T (F x y) := by
  refine lt_of_le_of_ne (cl_antitone_family (step_subset h) _) fun he => ?_
  obtain ⟨s, hs, hFs, hys⟩ := step_separates h hb
  have hy : y ≤ cl T (F x y) := ((bad_iff_le_cl htT hcl).1 hb).2.2.2.2
  exact hys (hy.trans (he ▸ cl_le hs hFs))

/-- **Result 1.** -/
theorem response_closure_rank_strict_drop {r : α → ℕ} (hr : StrictMono r) {T T' : Finset α} (htT : ⊤ ∈ T)
    (hcl : ∀ a ∈ T, ∀ b ∈ T, a ⊓ b ∈ T) (h : Step F D T T') {x y : α} (hb : Bad F D T x y) :
    r (cl T' (F x y)) < r (cl T (F x y)) :=
  hr (response_closure_strict_drop htT hcl h hb)

/-- **RP ⇒ ∃-SB** (stuck stages exempt). If, as long as no stage up to `H` is stuck, every bad pair of `Tₙ₊₁` has a
bad parent in `Tₙ` with strictly larger response closure rank (and `r ≤ H`), then some stage `≤ H` is stuck, or
`T_H` has no bad pair. -/
theorem rank_parent_stage_bound (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) {r : α → ℕ}
    (hr : StrictMono r) {H : ℕ} (hH : ∀ a, r a ≤ H) (T : ℕ → Finset α)
    (htT : ∀ n, ⊤ ∈ T n) (hcl : ∀ n, ∀ a ∈ T n, ∀ b ∈ T n, a ⊓ b ∈ T n)
    (hRP : ∀ n x' y', Bad F D (T (n + 1)) x' y' → (∃ a b, Bad F D (T (n + 1)) a b ∧ b ≤ F a b) ∨
      ∃ x y, Bad F D (T n) x y ∧ r (cl (T (n + 1)) (F x' y')) < r (cl (T n) (F x y))) :
    (∃ n ≤ H, ∃ a b, Bad F D (T n) a b ∧ b ≤ F a b) ∨ ∀ x y, ¬ Bad F D (T H) x y := by
  by_cases hstuck : ∃ n ≤ H, ∃ a b, Bad F D (T n) a b ∧ b ≤ F a b
  · exact Or.inl hstuck
  right
  push_neg at hstuck
  have hlow : ∀ n x y, Bad F D (T n) x y → r ⊥ < r (cl (T n) (F x y)) := fun n x y hb => by
    have hy := ((bad_iff_le_cl (htT n) (hcl n)).1 hb).2.2.2.2
    refine hr (lt_of_le_of_ne bot_le fun he => ?_)
    exact hb.2.2.2.1 (hD _ _ (he ▸ hy) hbot)
  have hup : ∀ n, n ≤ H → ∀ x y, Bad F D (T n) x y → r (cl (T n) (F x y)) + n ≤ H := by
    intro n
    induction n with
    | zero => intro _ x y _; simpa using hH _
    | succ n ih =>
      intro hn x' y' hb
      rcases hRP n x' y' hb with ⟨a, b, hab, hst⟩ | ⟨x, y, hb0, hlt⟩
      · exact absurd hst (hstuck (n + 1) hn a b hab)
      · have := ih (by omega) x y hb0; omega
  intro x y hb
  have h1 := hlow H x y hb; have h2 := hup H le_rfl x y hb; omega

end Closure

section Fork

variable {α : Type*} [Lattice α] [BoundedOrder α] {F : α → α → α} {D : Set α}

/-- **Result 2: the causal fork.** -/
theorem next_bad_pair_carrier (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) {x y s x' y' : α}
    (hs : IsMaxSep F x y s) (hy' : y' ∉ D) :
    (x' ≤ s ∧ y' ≤ s ∧ s ∉ D ∧ s ≠ ⊤) ∨ ∃ v, s < v ∧ v ∉ D ∧ y ≤ v ∧ x' ≤ v ∧ y' ≤ v := by
  obtain ⟨-, hys, hmax⟩ := hs
  by_cases hboth : x' ≤ s ∧ y' ≤ s
  · exact Or.inl ⟨hboth.1, hboth.2, fun h => hy' (hD _ _ hboth.2 h), fun h => hys (h ▸ le_top)⟩
  · right
    have hlt : s < s ⊔ x' ⊔ y' := lt_of_le_of_ne (le_sup_left.trans le_sup_left) fun he =>
      hboth ⟨(le_sup_right.trans le_sup_left).trans he.symm.le, le_sup_right.trans he.symm.le⟩
    exact ⟨s ⊔ x' ⊔ y', hlt, fun h => hy' (hD _ _ le_sup_right h), hmax _ hlt,
      le_sup_right.trans le_sup_left, le_sup_right⟩

/-- **Contained branch** (generic): Cut on `↓s`, `s ∉ D` and `F s s ≤ s` give a witness for `F`. -/
theorem contained_branch {s : α} (hsD : s ∉ D) (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D)
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hss : F s s ≤ s)
    (IH : ∀ (G : Set.Iic s → Set.Iic s → Set.Iic s), (∀ x x' y y', x ≤ x' → y ≤ y' → G x y ≤ G x' y') →
      ∀ D' : Set (Set.Iic s), (∀ x y, x ≤ y → y ∈ D' → x ∈ D') → ⊥ ∈ D' → ⊤ ∉ D' →
      ∃ x ∈ D', ∃ y, y ∉ D' ∧ (G x y ≤ x ∨ y ≤ G x y)) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  let G : Set.Iic s → Set.Iic s → Set.Iic s := fun a b =>
    ⟨F a.1 b.1, (hF _ _ _ _ a.2 b.2).trans hss⟩
  obtain ⟨a, ha, b, hb, hw⟩ := IH G (fun x x' y y' hx hy => hF _ _ _ _ hx hy) {a | a.1 ∈ D}
    (fun a b hab hb => hD _ _ hab hb) hbot hsD
  exact ⟨a.1, ha, b.1, hb, hw⟩

theorem chainTo_val {s : α} : ∀ (k : ℕ) (z : Set.Iic s), Mordor.Ground.chainTo z k → Mordor.Ground.chainTo z.1 k
  | 0, _, _ => trivial
  | k + 1, _, ⟨w, hw, hc⟩ => ⟨w.1, hw, chainTo_val k w hc⟩

/-- **Contained branch at edge-height ≤ 6** (via `cut_height5` on `↓s`). Under no witness, a maximal separator
`s ∉ D` has `F s s ≰ s`, and `v = s ⊔ F s s > s` lies above `y`. -/
theorem contained_branch_height6 (hn : Mordor.Ground.NoChain α 7)
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D)
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {x y s : α} (hs : IsMaxSep F x y s) (hsD : s ∉ D) :
    ¬ F s s ≤ s ∧ s < s ⊔ F s s ∧ y ≤ s ⊔ F s s := by
  have hstop : s ≠ ⊤ := fun h => hs.2.1 (h ▸ le_top)
  have hnoch : Mordor.Ground.NoChain (Set.Iic s) 6 := fun z hz =>
    hn ⊤ ⟨z.1, lt_of_le_of_lt z.2 (lt_top_iff_ne_top.2 hstop), chainTo_val 6 z hz⟩
  have hss : ¬ F s s ≤ s := fun hss => by
    obtain ⟨a, ha, b, hb, hw⟩ := contained_branch hsD hD hbot hF hss
      (fun G hG D' hD' hb' ht' => Mordor.Ground.cut_height5 hnoch G hG D' hD' hb' ht')
    rcases hw with h | h
    · exact (nw a ha b hb).1 h
    · exact (nw a ha b hb).2 h
  have hlt : s < s ⊔ F s s := lt_of_le_of_ne le_sup_left fun he => hss (le_sup_right.trans he.symm.le)
  exact ⟨hss, hlt, hs.2.2 _ hlt⟩

end Fork

end Mordor.SeparatorRank
