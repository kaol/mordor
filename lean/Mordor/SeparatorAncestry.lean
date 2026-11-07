import Mordor.SeparatorRank

/-!
# Separator ancestry, supports and fans (round 26, §34.3z¹²³)

ChatGPT brief "separator ancestry, coordinate age and column-conditioned coverage".

* `meetClose_meetClose_union`: `meetClose (meetClose X ∪ S) = meetClose (X ∪ S)`; hence `run_tokens`: every stage of a
  run is `meetClose ({⊥, ⊤} ∪ U)` for a finite set `U` of separators chosen at earlier stages (tokens).
* `fresh_token`: an element of `meetClose (T ∪ S) ∖ T` (`T` meet-closed, `⊤ ∈ T`) has, in **every** support
  `A ⊆ T ∪ S`, a token of `S ∖ T`.
* `minimal_meet_support_bound` (A2): a subset-minimal `A` with a given meet has `|A| ≤ H` at edge-height `≤ H`;
  `minimal_join_support_bound` (B2, B3): dually, a subset-minimal `A` with `P (A.sup v)` and `¬ P ⊥` has `|A| ≤ H`.
* `cone_separates` (B1): a separator of `(x_s, y)` separates `(x, y)` for every `x ≤ x_s`.
* `row_fan_collapse` (B2, case I): rows `X` with `⋁ X ∈ D` and a column `y ∉ D`: one maximal separator of
  `(⋁ X, y)` separates every `(x, y)`, `x ∈ X` (ACC, no witness).
* `potential_parent_stage_bound`: any stage-dependent potential bounded by `B` on bad pairs, decreasing from some
  bad parent to every bad child of a non-stuck stage, ends the run (stuck or terminal) by stage `B + 1`.
* `column_fan_collapse` (B3, case I): a row `x ∈ D` and columns `Y` with `⋀ Y ∉ D`: one minimal lower separator of
  `(x, ⋀ Y)` dually separates every `(x, y)`, `y ∈ Y` (DCC, no witness).
-/

namespace Mordor.SeparatorAncestry
open Finset Mordor.SeparatorStages Mordor.Ground

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] [DecidableEq α] [DecidableLE α]

theorem mem_meetClose_iff {X : Finset α} {e : α} : e ∈ meetClose X ↔ ∃ A ⊆ X, A.inf id = e := by
  unfold meetClose; simp [Finset.mem_image, Finset.mem_powerset]

theorem meetClose_meetClose_union (X S : Finset α) : meetClose (meetClose X ∪ S) = meetClose (X ∪ S) := by
  ext e
  constructor
  · intro he
    obtain ⟨A, hA, rfl⟩ := mem_meetClose_iff.1 he
    -- each a ∈ A ∩ meetClose X is a meet of a subset of X: replace it
    classical
    have : ∀ a ∈ A, ∃ B ⊆ X ∪ S, B.inf id = a := fun a ha => by
      rcases Finset.mem_union.1 (hA ha) with h | h
      · obtain ⟨B, hB, rfl⟩ := mem_meetClose_iff.1 h
        exact ⟨B, hB.trans Finset.subset_union_left, rfl⟩
      · exact ⟨{a}, Finset.singleton_subset_iff.2 (Finset.mem_union_right _ h), by simp⟩
    choose B hB hBa using this
    refine mem_meetClose_iff.2 ⟨A.attach.biUnion fun a => B a.1 a.2, ?_, ?_⟩
    · intro z hz
      obtain ⟨a, -, hz⟩ := Finset.mem_biUnion.1 hz
      exact hB a.1 a.2 hz
    · rw [Finset.inf_biUnion]
      conv_rhs => rw [← Finset.inf_attach]
      exact Finset.inf_congr rfl fun a _ => hBa a.1 a.2
  · intro he
    obtain ⟨A, hA, rfl⟩ := mem_meetClose_iff.1 he
    exact mem_meetClose_iff.2 ⟨A, hA.trans (Finset.union_subset_union (subset_meetClose X) (Finset.Subset.refl S)), rfl⟩

/-- **Fresh token** (A3): every support of a new element contains a token of the step. -/
theorem fresh_token {T S A : Finset α} (htT : ⊤ ∈ T) (hcl : ∀ a ∈ T, ∀ b ∈ T, a ⊓ b ∈ T) (hA : A ⊆ T ∪ S)
    (hnew : A.inf id ∉ T) : ∃ s ∈ A, s ∈ S ∧ s ∉ T := by
  by_contra h
  push_neg at h
  apply hnew
  refine Mordor.FiniteQuotient.inf_mem_of_closed htT hcl A fun a ha => ?_
  rcases Finset.mem_union.1 (hA ha) with h1 | h1
  · exact h1
  · exact h a ha h1

variable {F : α → α → α} {D : Set α}

/-- **Tokens** (A1): every stage of a run is the meet-closure of `{⊥, ⊤}` and earlier separators. -/
theorem run_tokens {T : ℕ → Finset α} (hr : Run F D T) :
    ∀ n, ∃ U : Finset α, T n = meetClose ({⊥, ⊤} ∪ U) ∧
      ∀ u ∈ U, ∃ k < n, ∃ x y, Bad F D (T k) x y ∧ IsMaxSep F x y u := by
  intro n
  induction n with
  | zero =>
    refine ⟨∅, ?_, by simp⟩
    rw [hr.1, Finset.union_empty]
    ext e
    constructor
    · intro he; exact subset_meetClose _ he
    · intro he
      obtain ⟨A, hA, rfl⟩ := mem_meetClose_iff.1 he
      have := (run_closed hr 0)
      rw [hr.1] at this
      exact Mordor.FiniteQuotient.inf_mem_of_closed this.2.1 this.2.2 A hA
  | succ n ih =>
    obtain ⟨U, hU, hUs⟩ := ih
    rcases hr.2 n with ⟨-, he⟩ | ⟨S, he, hS, -⟩
    · exact ⟨U, he.trans hU, fun u hu => by
        obtain ⟨k, hk, h⟩ := hUs u hu; exact ⟨k, by omega, h⟩⟩
    · refine ⟨U ∪ S, ?_, fun u hu => ?_⟩
      · rw [he, hU, meetClose_meetClose_union, Finset.union_assoc]
      · rcases Finset.mem_union.1 hu with h | h
        · obtain ⟨k, hk, h'⟩ := hUs u h; exact ⟨k, by omega, h'⟩
        · exact ⟨n, by omega, hS u h⟩

/-- No-`⊥` variant of `BoundedSupport.minimal_chain` for meets. -/
theorem minimal_meet_chain {P : α → Prop} {v : α → α} {S : Finset α} (hP : P (S.inf v))
    (hmin : ∀ S' ⊂ S, ¬ P (S'.inf v)) :
    ∀ n (A : Finset α), A ⊆ S → (S \ A).card = n → chainTo (A.inf v) n := by
  intro n
  induction n with
  | zero => intro _ _ _; trivial
  | succ n ih =>
    intro A hA hc
    obtain ⟨a, ha⟩ : (S \ A).Nonempty := Finset.card_pos.1 (by omega)
    have haS : a ∈ S := (Finset.mem_sdiff.1 ha).1
    have haA : a ∉ A := (Finset.mem_sdiff.1 ha).2
    have hsub : insert a A ⊆ S := Finset.insert_subset haS hA
    have hcard : (S \ insert a A).card = n := by
      have : S \ insert a A = (S \ A).erase a := by ext x; simp [Finset.mem_sdiff, Finset.mem_erase]; tauto
      rw [this, Finset.card_erase_of_mem ha, hc]; rfl
    exact ⟨_, Mordor.BoundedSupport.inf_strict_of_minimal hP hmin (Finset.ssubset_insert haA) hsub,
      ih _ hsub hcard⟩

/-- **Minimal meet support** (A2): `|A| ≤ H`. -/
theorem minimal_meet_support_bound {H : ℕ} (hH : NoChain α (H + 1)) {t : α} {A : Finset α}
    (hA : A.inf id = t) (hmin : ∀ A' ⊂ A, A'.inf id ≠ t) : A.card ≤ H := by
  have hc := minimal_meet_chain (P := (· = t)) (v := id) hA hmin A.card ∅ (Finset.empty_subset _) (by simp)
  by_contra hlt
  exact hH _ (Mordor.BoundedSupport.chainTo_mono _ _ _ hc (by omega))

/-- Strict increase of joins on subsets of a minimal set. -/
theorem sup_strict_of_minimal {P : α → Prop} {v : α → α} {S : Finset α} (hP : P (S.sup v))
    (hmin : ∀ S' ⊂ S, ¬ P (S'.sup v)) {A B : Finset α} (hAB : A ⊂ B) (hBS : B ⊆ S) : A.sup v < B.sup v := by
  refine lt_of_le_of_ne (Finset.sup_mono hAB.subset) fun heq => ?_
  have hS : S.sup v = (A ∪ (S \ B)).sup v := by
    conv_lhs => rw [← Finset.union_sdiff_of_subset hBS]
    rw [Finset.sup_union, Finset.sup_union, heq]
  obtain ⟨b, hbB, hbA⟩ := Finset.exists_of_ssubset hAB
  refine hmin _ ?_ (hS ▸ hP)
  refine Finset.ssubset_iff_of_subset (Finset.union_subset (hAB.subset.trans hBS) Finset.sdiff_subset) |>.2
    ⟨b, hBS hbB, ?_⟩
  simp [hbA, hbB]

theorem minimal_join_chain {P : α → Prop} {v : α → α} {S : Finset α} (hP : P (S.sup v))
    (hmin : ∀ S' ⊂ S, ¬ P (S'.sup v)) : ∀ A : Finset α, A ⊆ S → chainTo (A.sup v) A.card := by
  intro A
  induction A using Finset.induction_on with
  | empty => intro _; trivial
  | insert a A ha ih =>
    intro hsub
    rw [Finset.card_insert_of_notMem ha]
    exact ⟨A.sup v, sup_strict_of_minimal hP hmin (Finset.ssubset_insert ha) hsub,
      ih ((Finset.subset_insert a A).trans hsub)⟩

/-- **Minimal join support** (B2, B3): `|A| ≤ H`. -/
theorem minimal_join_support_bound {H : ℕ} (hH : NoChain α (H + 1)) {P : α → Prop} {v : α → α}
    {A : Finset α} (hP : P (A.sup v)) (hmin : ∀ A' ⊂ A, ¬ P (A'.sup v)) : A.card ≤ H := by
  have hc := minimal_join_chain hP hmin A (Finset.Subset.refl A)
  by_contra hlt
  exact hH _ (Mordor.BoundedSupport.chainTo_mono _ _ _ hc (by omega))

/-- **Coverage cone** (B1). -/
theorem cone_separates (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {xs y s x : α}
    (hs : F xs y ≤ s) (hys : ¬ y ≤ s) (hx : x ≤ xs) : F x y ≤ s ∧ ¬ y ≤ s :=
  ⟨(hF _ _ _ _ hx le_rfl).trans hs, hys⟩

/-- **Row-fan collapse** (B2, case I). -/
theorem row_fan_collapse [WellFoundedGT α] (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {X : Finset α} (hX : X.sup id ∈ D) {y : α} (hy : y ∉ D) :
    ∃ s, IsMaxSep F (X.sup id) y s ∧ ∀ x ∈ X, F x y ≤ s ∧ ¬ y ≤ s := by
  obtain ⟨s, h1, h2, h3⟩ := Mordor.ExtremalSeparators.exists_upper_separator nw hX hy
  exact ⟨s, ⟨h1, h2, h3⟩, fun x hx => cone_separates hF h1 h2 (Finset.le_sup (f := id) hx)⟩

/-- **Column-fan collapse** (B3, case I). -/
theorem column_fan_collapse [WellFoundedLT α] (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {x : α} (hx : x ∈ D) {Y : Finset α} (hY : Y.inf id ∉ D) :
    ∃ s, s ≤ F x (Y.inf id) ∧ ¬ s ≤ x ∧ (∀ t, t < s → t ≤ x) ∧ ∀ y ∈ Y, s ≤ F x y ∧ ¬ s ≤ x := by
  obtain ⟨s, h1, h2, h3⟩ := Mordor.ExtremalSeparators.exists_lower_separator nw hx hY
  exact ⟨s, h1, h2, h3, fun y hy => ⟨h1.trans (hF _ _ _ _ le_rfl (Finset.inf_le (f := id) hy)), h2⟩⟩

/-- **Potential-parent ⇒ stage bound** (generic; stuck stages exempt). `φ T x y ≤ B` on bad pairs, and, while no
stage up to `B + 1` is stuck, every bad pair of `Tₙ₊₁` has a bad parent in `Tₙ` with strictly larger `φ`. Then some
stage `≤ B + 1` is stuck or `T (B + 1)` has no bad pair. Instances: the gap potential `rank y + H - rank x`
(`B = 2H`) and the response gap `rank cl_T (F x y) + H - rank x` of §34.3z¹²³. -/
theorem potential_parent_stage_bound (φ : Finset α → α → α → ℕ) {B : ℕ} (T : ℕ → Finset α)
    (hB : ∀ n x y, Bad F D (T n) x y → φ (T n) x y ≤ B)
    (hRP : ∀ n x' y', Bad F D (T (n + 1)) x' y' → (∃ a b, Bad F D (T (n + 1)) a b ∧ b ≤ F a b) ∨
      ∃ x y, Bad F D (T n) x y ∧ φ (T (n + 1)) x' y' < φ (T n) x y) :
    (∃ n ≤ B + 1, ∃ a b, Bad F D (T n) a b ∧ b ≤ F a b) ∨ ∀ x y, ¬ Bad F D (T (B + 1)) x y := by
  by_cases hstuck : ∃ n ≤ B + 1, ∃ a b, Bad F D (T n) a b ∧ b ≤ F a b
  · exact Or.inl hstuck
  right
  push_neg at hstuck
  have hup : ∀ n, n ≤ B + 1 → ∀ x y, Bad F D (T n) x y → φ (T n) x y + n ≤ B := by
    intro n
    induction n with
    | zero => intro _ x y hb; simpa using hB 0 x y hb
    | succ n ih =>
      intro hn x' y' hb
      rcases hRP n x' y' hb with ⟨a, b, hab, hst⟩ | ⟨x, y, hb0, hlt⟩
      · exact absurd hst (hstuck (n + 1) hn a b hab)
      · have := ih (by omega) x y hb0; omega
  intro x y hb
  have := hup (B + 1) le_rfl x y hb; omega

end Mordor.SeparatorAncestry
