import Mordor.GroundCut
import Mordor.InfiniteCapture

/-!
# Bounded-support pivots (round 26, §34.3z¹¹⁷)

ChatGPT brief "axis-capture graphs, bounded support and the height-six obstruction", Program B1.

For a finite family `v : ι → α` and a predicate `P` (in the application: "in `D` and below no row"), call `S`
**minimal** if `P (S.inf v)` and no proper subset `S' ⊂ S` has `P (S'.inf v)`.

* `inf_strict_of_minimal`: on subsets of a minimal `S`, `A ⊂ B ⊆ S ⇒ B.inf v < A.inf v` (otherwise dropping `B \ A`
  from `S` keeps the meet).
* `minimal_chain`: hence `⊤ = ∅.inf v` carries a strict chain of `|S| + 1` steps when `⊥ < S.inf v`.
* `minimal_support_card` (**B1**): in a lattice with `NoChain α (H + 1)` (edge-height ≤ `H`), `|S| + 1 ≤ H`.
* `exists_minimal_support`: minimal subsets exist below any `S₀` with `P (S₀.inf v)`.
* `proper_partial_meet_outside` (application): for `P = Good` (in `D`, below no row), every proper partial meet lies
  outside `D`.
* `orbit_support_bound` (**strengthened B1**): for a mixed pivot of orbit points (`|S| ≥ 2`) and `i ∈ S`,
  `t i + |S| ≤ H`: the orbit descent of coordinate `i` prepends `t i` strict steps to the partial-meet chain.
-/

namespace Mordor.BoundedSupport
open Finset Mordor.Ground

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [DecidableEq ι]

theorem chainTo_mono : ∀ (n m : ℕ) (x : α), chainTo x n → m ≤ n → chainTo x m
  | _, 0, _, _, _ => trivial
  | 0, _ + 1, _, _, h => absurd h (by omega)
  | n + 1, m + 1, x, ⟨y, hy, hc⟩, h => ⟨y, hy, chainTo_mono n m y hc (by omega)⟩

/-- Strictness on subsets of a minimal set. -/
theorem inf_strict_of_minimal {P : α → Prop} {v : ι → α} {S : Finset ι} (hP : P (S.inf v))
    (hmin : ∀ S' ⊂ S, ¬ P (S'.inf v)) {A B : Finset ι} (hAB : A ⊂ B) (hBS : B ⊆ S) : B.inf v < A.inf v := by
  refine lt_of_le_of_ne (Finset.inf_mono hAB.subset) fun heq => ?_
  have hS : S.inf v = (A ∪ (S \ B)).inf v := by
    conv_lhs => rw [← Finset.union_sdiff_of_subset hBS]
    rw [Finset.inf_union, Finset.inf_union, heq]
  obtain ⟨b, hbB, hbA⟩ := Finset.exists_of_ssubset hAB
  refine hmin _ ?_ (hS ▸ hP)
  refine Finset.ssubset_iff_of_subset (Finset.union_subset (hAB.subset.trans hBS) Finset.sdiff_subset) |>.2
    ⟨b, hBS hbB, ?_⟩
  simp [hbA, hbB]

/-- The strict chain of partial meets of a minimal set. -/
theorem minimal_chain {P : α → Prop} {v : ι → α} {S : Finset ι} (hP : P (S.inf v))
    (hmin : ∀ S' ⊂ S, ¬ P (S'.inf v)) (hbot : ⊥ < S.inf v) :
    ∀ n (A : Finset ι), A ⊆ S → (S \ A).card = n → chainTo (A.inf v) (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro A hA hc
    have : A = S := le_antisymm hA (Finset.sdiff_eq_empty_iff_subset.1 (Finset.card_eq_zero.1 hc))
    subst this; exact ⟨⊥, hbot, trivial⟩
  | succ n ih =>
    intro A hA hc
    obtain ⟨a, ha⟩ : (S \ A).Nonempty := Finset.card_pos.1 (by omega)
    have haS : a ∈ S := (Finset.mem_sdiff.1 ha).1
    have haA : a ∉ A := (Finset.mem_sdiff.1 ha).2
    have hsub : insert a A ⊆ S := Finset.insert_subset haS hA
    have hcard : (S \ insert a A).card = n := by
      have : S \ insert a A = (S \ A).erase a := by ext x; simp [Finset.mem_sdiff, Finset.mem_erase]; tauto
      rw [this, Finset.card_erase_of_mem ha, hc]; rfl
    exact ⟨_, inf_strict_of_minimal hP hmin (Finset.ssubset_insert haA) hsub, ih _ hsub hcard⟩

/-- **B1.** A minimal set in a lattice of edge-height ≤ `H` has at most `H - 1` elements. -/
theorem minimal_support_card {H : ℕ} (hH : NoChain α (H + 1)) {P : α → Prop} {v : ι → α} {S : Finset ι}
    (hP : P (S.inf v)) (hmin : ∀ S' ⊂ S, ¬ P (S'.inf v)) (hbot : ¬ P ⊥) : S.card + 1 ≤ H := by
  have hb : ⊥ < S.inf v := bot_lt_iff_ne_bot.2 fun h => hbot (h ▸ hP)
  have hc := minimal_chain hP hmin hb S.card ∅ (Finset.empty_subset _) (by simp)
  by_contra hlt
  exact hH _ (chainTo_mono _ _ _ hc (by omega))

/-- Minimal sets exist. -/
theorem exists_minimal_support {P : α → Prop} {v : ι → α} {S₀ : Finset ι} (h0 : P (S₀.inf v)) :
    ∃ S ⊆ S₀, P (S.inf v) ∧ ∀ S' ⊂ S, ¬ P (S'.inf v) := by
  obtain ⟨S, ⟨hS0, hS⟩, hmin⟩ := (wellFounded_lt (α := Finset ι)).has_min
    {S | S ⊆ S₀ ∧ P (S.inf v)} ⟨S₀, Finset.Subset.refl _, h0⟩
  exact ⟨S, hS0, hS, fun S' hS' hP' => hmin S' ⟨hS'.subset.trans hS0, hP'⟩ hS'⟩

section Pivot

variable {k : ℕ} {D : Set α} (g : Fin k → α)

/-- In `D` and below no row. -/
def Good (x : α) : Prop := x ∈ D ∧ ∀ j, ¬ x ≤ g j

theorem not_good_bot (hk : 0 < k) : ¬ Good (D := D) g ⊥ :=
  fun h => h.2 ⟨0, hk⟩ bot_le

/-- Proper partial meets of a minimal pivot lie outside `D`. -/
theorem proper_partial_meet_outside {v : Fin k → α} {S : Finset (Fin k)}
    (hP : Good (D := D) g (S.inf v)) (hmin : ∀ S' ⊂ S, ¬ Good (D := D) g (S'.inf v)) {A : Finset (Fin k)}
    (hA : A ⊂ S) : A.inf v ∉ D := fun hAD => by
  by_cases hc : ∃ j, A.inf v ≤ g j
  · obtain ⟨j, hj⟩ := hc; exact hP.2 j ((Finset.inf_mono hA.subset).trans hj)
  · push_neg at hc; exact hmin A hA ⟨hAD, hc⟩

/-- **Strengthened B1.** For a mixed minimal pivot of orbit points and any coordinate `i` of its support, the orbit
descent to `uᵢ(tᵢ)` and the partial-meet chain together give `t i + |S| ≤ H`. -/
theorem orbit_support_bound {H : ℕ} (hH : NoChain α (H + 1)) (hk : 0 < k) {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (hg : ∀ i, g i ∈ D) (t : Fin k → ℕ)
    {S : Finset (Fin k)}
    (hP : Good (D := D) g (S.inf fun i => (F (g i))^[t i] ⊤))
    (hmin : ∀ S' ⊂ S, ¬ Good (D := D) g (S'.inf fun i => (F (g i))^[t i] ⊤))
    (h2 : 2 ≤ S.card) {i : Fin k} (hi : i ∈ S) : t i + S.card ≤ H := by
  set v : Fin k → α := fun i => (F (g i))^[t i] ⊤ with hv
  have hb : ⊥ < S.inf v := bot_lt_iff_ne_bot.2 fun h => not_good_bot g hk (h ▸ hP)
  have hsub : ({i} : Finset (Fin k)) ⊆ S := Finset.singleton_subset_iff.2 hi
  have hc0 := minimal_chain hP hmin hb (S \ {i}).card {i} hsub rfl
  have hcard : (S \ {i}).card + 1 = S.card := by
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_singleton]; omega
  rw [hcard, Finset.inf_singleton] at hc0
  have hssub : ({i} : Finset (Fin k)) ⊂ S :=
    Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h => by rw [← h, Finset.card_singleton] at h2; omega⟩
  have hout : (F (g i))^[t i] ⊤ ∉ D := by
    have := proper_partial_meet_outside g hP hmin hssub; rwa [Finset.inf_singleton] at this
  set u : ℕ → α := fun n => (F (g i))^[n] ⊤ with hu
  have hanti : Antitone u := Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) le_top
  have hstep : ∀ n, u n ∉ D → u (n + 1) < u n := fun n hn => by
    have he : u (n + 1) = F (g i) (u n) := Function.iterate_succ_apply' _ _ _
    refine lt_of_le_of_ne (hanti (Nat.le_succ n)) fun h => (nw _ (hg i) _ hn).2 ?_
    rw [← he, h]
  have key : ∀ m, m ≤ t i → chainTo (u (t i - m)) (S.card + m) := by
    intro m
    induction m with
    | zero => intro _; simpa using hc0
    | succ m ih =>
      intro hm
      have hn : u (t i - (m + 1)) ∉ D := fun h => hout (hD _ _ (hanti (Nat.sub_le _ _)) h)
      have hlt := hstep _ hn
      have he : t i - (m + 1) + 1 = t i - m := by omega
      rw [he] at hlt
      exact ⟨_, hlt, ih (by omega)⟩
  have htop := key (t i) le_rfl
  rw [Nat.sub_self] at htop
  by_contra hlt
  exact hH _ (chainTo_mono _ _ _ htop (by omega))

end Pivot

end Mordor.BoundedSupport
