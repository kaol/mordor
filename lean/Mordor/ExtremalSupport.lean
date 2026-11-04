import Mordor.SupportCofactors
import Mathlib.Data.DFinsupp.WellFounded

/-!
# Extremal support normalization and the three-petal incidence (round 26, §34.3z¹⁰³)

Response to the brief "extremal support normalization and the three-petal incidence problem". Row supports of `s`
indexed by a finite `ι` form the set `rowSupports F InD s` of tuples `p : ι → α` with entries in `D` and
`s = ⨆ᵢ F (pᵢ) s`, ordered pointwise. For generators `g : κ → α` and `σ : ι → κ`, `comeet g σ i = ⨅_{j≠i} g (σ j)`.

* `finite_product_wellFoundedGT`, `maximal_tuple_exists`, `maximal_row_support_exists`: ACC passes to finite products,
  so every support lies below a pointwise-maximal one.
* `comeet_stable`, `comeet_mem`: a co-meet tuple is itself stable (its cofactors stay under `g ∘ σ`).
* `maximal_stable_support_eq_comeets`, **`maximal_support_dichotomy`** (the brief's target): a maximal support has a
  crossing cofactor or equals a co-meet tuple with injective `σ`.
* **`stable_support_dominated`, `stable_support_iff_comeets`**: the extremal selection is not needed — every stable
  support lies pointwise below its own co-meet tuple, which is a stable support; so a stable support exists iff some
  injective co-meet tuple (for `|ι| = k = 3`: the three pairwise generator meets) is a row support.
* `generator_tuple_maximal`: the canonical generator tuple is maximal, and (antichain, `|ι| ≥ 3`) all its cofactors
  cross — the first branch of the dichotomy is always inhabited.
* **`not_all_but_one_in`, `two_outside_generator_responses`** (DCC): at a column contracting for every generator
  row, at least two generator responses lie outside `D` (found by z3 as an UNSAT orbit profile).
* **`not_all_but_one_anchor_in`, `two_outside_anchor_responses`** (DCC): the same for the join-anchor rows
  (strengthens `contracting_simultaneous`; proof: `anchor_sandwich` + `simultaneous_entry` at the end of one anchor
  orbit, the other anchors kept off their own petals because they already sit in another one).
* `common_missing_petal`: every response `F x s` with `x ≥ ⨅ g` avoids one common petal.
* `pairwise_meet_anchor_incidence`: the six edge/vertex inequalities, `aᵢ ≤ F gᵢ s`, and the three join equalities.
-/

namespace Mordor.Profile

set_option linter.unusedSectionVars false

section Extremal

variable {α : Type*} [CompleteLattice α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- ACC for finite products (pointwise order). -/
theorem finite_product_wellFoundedGT [WellFoundedGT α] : WellFoundedGT (ι → α) := by
  have : WellFoundedLT (ι → αᵒᵈ) := Pi.wellFoundedLT
  exact ⟨this.wf⟩

/-- A pointwise-maximal member of a set of tuples above any given member. -/
theorem maximal_tuple_exists [WellFoundedGT α] (S : Set (ι → α)) {p₀ : ι → α} (h₀ : p₀ ∈ S) :
    ∃ p ∈ S, p₀ ≤ p ∧ ∀ p' ∈ S, p ≤ p' → p' = p := by
  haveI := finite_product_wellFoundedGT (α := α) (ι := ι)
  obtain ⟨p, ⟨hpS, hp0⟩, hmax⟩ :=
    (wellFounded_gt (α := ι → α)).has_min {p | p ∈ S ∧ p₀ ≤ p} ⟨p₀, h₀, le_rfl⟩
  exact ⟨p, hpS, hp0, fun p' hp' hpp => by
    by_contra hne
    exact hmax p' ⟨hp', hp0.trans hpp⟩ (lt_of_le_of_ne hpp fun h => hne h.symm)⟩

/-- Row supports of `s` indexed by `ι`. -/
def rowSupports (F : α → α → α) (InD : α → Prop) (s : α) : Set (ι → α) :=
  {p | (∀ i, InD (p i)) ∧ s = Finset.univ.sup fun i => F (p i) s}

/-- Co-meet tuple `i ↦ ⨅_{j≠i} g (σ j)`. -/
def comeet {κ : Type*} (g : κ → α) (σ : ι → κ) (i : ι) : α := (Finset.univ.erase i).inf (g ∘ σ)

theorem maximal_row_support_exists [WellFoundedGT α] {F : α → α → α} {InD : α → Prop} {s : α} {p₀ : ι → α}
    (h₀ : p₀ ∈ rowSupports F InD s) :
    ∃ p ∈ rowSupports F InD s, p₀ ≤ p ∧ ∀ p' ∈ rowSupports F InD s, p ≤ p' → p' = p :=
  maximal_tuple_exists _ h₀

theorem comeet_stable {κ : Type*} (g : κ → α) (σ : ι → κ) (i : ι) : rowCof (comeet g σ) i ≤ g (σ i) :=
  Finset.sup_le fun _ hj =>
    Finset.inf_le (f := g ∘ σ) (Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hj).symm, Finset.mem_univ _⟩)

variable {F : α → α → α} {InD : α → Prop}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
  (hdown : ∀ x y, x ≤ y → InD y → InD x)
  (nw : ∀ x, InD x → ∀ y, ¬ InD y → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hdown in
theorem comeet_mem [Nontrivial ι] {κ : Type*} (g : κ → α) (hg : ∀ k, InD (g k)) (σ : ι → κ) (j : ι) :
    InD (comeet g σ j) := by
  obtain ⟨i, hi⟩ := exists_ne j
  exact hdown _ _ (Finset.inf_le (f := g ∘ σ) (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)) (hg (σ i))

include hF hdown in
/-- **Every stable support lies below its co-meet tuple, which is a stable support.** -/
theorem stable_support_dominated [Nontrivial ι] {κ : Type*} (g : κ → α) (hg : ∀ k, InD (g k)) {s : α}
    (hsc : ∀ x, InD x → F x s ≤ s) {p : ι → α} (hp : p ∈ rowSupports F InD s) (σ : ι → κ)
    (hσ : ∀ i, rowCof p i ≤ g (σ i)) :
    p ≤ comeet g σ ∧ comeet g σ ∈ rowSupports F InD s ∧ ∀ i, rowCof (comeet g σ) i ≤ g (σ i) := by
  obtain ⟨hle, hsup⟩ := cofactor_stable_comeets hF hdown g hg hsc hp.2 σ hσ
  exact ⟨hle, ⟨fun j => comeet_mem (ι := ι) hdown g hg σ j, hsup⟩, comeet_stable g σ⟩

include hF hdown in
/-- **A maximal stable support is a co-meet tuple.** -/
theorem maximal_stable_support_eq_comeets [Nontrivial ι] {κ : Type*} (g : κ → α) (hg : ∀ k, InD (g k)) {s : α}
    (hsc : ∀ x, InD x → F x s ≤ s) {p : ι → α} (hp : p ∈ rowSupports F InD s)
    (hmax : ∀ p' ∈ rowSupports F InD s, p ≤ p' → p' = p) (σ : ι → κ) (hσ : ∀ i, rowCof p i ≤ g (σ i)) :
    p = comeet g σ := by
  obtain ⟨hle, hmem, -⟩ := stable_support_dominated hF hdown g hg hsc hp σ hσ
  exact (hmax _ hmem hle).symm

include hF hdown nw in
/-- **Maximal support dichotomy.** In `D = ⋃ₖ ↓gₖ`, a pointwise-maximal row support has a cofactor outside `D`, or
it is the co-meet tuple of an injective `σ` (for `|ι| = k = 3`, the three pairwise generator meets). -/
theorem maximal_support_dichotomy [Nontrivial ι] {κ : Type*} (g : κ → α) (hg : ∀ k, InD (g k))
    (hgen : ∀ x, InD x → ∃ k, x ≤ g k) {s : α} (hs : ¬ InD s) (hsc : ∀ x, InD x → F x s ≤ s) {p : ι → α}
    (hp : p ∈ rowSupports F InD s) (hmax : ∀ p' ∈ rowSupports F InD s, p ≤ p' → p' = p) :
    (∃ i, ¬ InD (rowCof p i)) ∨ ∃ σ : ι → κ, Function.Injective σ ∧ p = comeet g σ := by
  by_cases h : ∀ i, InD (rowCof p i)
  · right
    choose σ hσ using fun i => hgen _ (h i)
    exact ⟨σ, cofactor_petal_injective hF hdown nw g hg hs hp.2 σ hσ,
      maximal_stable_support_eq_comeets hF hdown g hg hsc hp hmax σ hσ⟩
  · left
    push_neg at h
    exact h

include hF hdown nw in
/-- **Stable supports exist iff an injective co-meet tuple is a support.** -/
theorem stable_support_iff_comeets [Nontrivial ι] {κ : Type*} (g : κ → α) (hg : ∀ k, InD (g k))
    (hgen : ∀ x, InD x → ∃ k, x ≤ g k) {s : α} (hs : ¬ InD s) (hsc : ∀ x, InD x → F x s ≤ s) :
    (∃ p : ι → α, p ∈ rowSupports F InD s ∧ ∀ i, InD (rowCof p i)) ↔
      ∃ σ : ι → κ, Function.Injective σ ∧ comeet g σ ∈ rowSupports F InD s := by
  constructor
  · rintro ⟨p, hp, h⟩
    choose σ hσ using fun i => hgen _ (h i)
    exact ⟨σ, cofactor_petal_injective hF hdown nw g hg hs hp.2 σ hσ,
      (stable_support_dominated hF hdown g hg hsc hp σ hσ).2.1⟩
  · rintro ⟨σ, -, hm⟩
    exact ⟨_, hm, fun i => hdown _ _ (comeet_stable g σ i) (hg (σ i))⟩

include hdown in
/-- **The generator tuple is maximal**, and for an antichain of `≥ 3` generators every cofactor crosses. -/
theorem generator_tuple_maximal (g : ι → α) (hgen : ∀ x, InD x → ∃ k, x ≤ g k)
    (hanti : ∀ i j, g i ≤ g j → i = j) {s : α} :
    (∀ p' ∈ rowSupports F InD s, g ≤ p' → p' = g) ∧
      (3 ≤ Fintype.card ι → ∀ i, ¬ InD (rowCof g i)) := by
  refine ⟨fun p' hp' hle => funext fun i => ?_, fun h3 i hin => ?_⟩
  · obtain ⟨k, hk⟩ := hgen _ (hp'.1 i)
    have hik : i = k := hanti i k ((hle i).trans hk)
    subst hik
    exact le_antisymm hk (hle i)
  · obtain ⟨k, hk⟩ := hgen _ hin
    obtain ⟨j, hji, hjk⟩ := exists_third h3 i k
    exact hjk (hanti j k ((le_rowCof g hji).trans hk))

include hF hdown in
/-- **Pairwise-meet / join-anchor incidence** at a common contracting column `s`. -/
theorem pairwise_meet_anchor_incidence {g₁ g₂ g₃ s : α} (hsc : ∀ x, InD x → F x s ≤ s) (h₁ : InD g₁)
    (h₂ : InD g₂) (h₃ : InD g₃) (hm : s = F (g₁ ⊓ g₂) s ⊔ F (g₁ ⊓ g₃) s ⊔ F (g₂ ⊓ g₃) s) :
    F (g₁ ⊓ g₂) s ≤ F (g₁ ⊓ g₂ ⊔ g₁ ⊓ g₃) s ∧ F (g₁ ⊓ g₂) s ≤ F (g₁ ⊓ g₂ ⊔ g₂ ⊓ g₃) s ∧
    F (g₁ ⊓ g₃) s ≤ F (g₁ ⊓ g₂ ⊔ g₁ ⊓ g₃) s ∧ F (g₁ ⊓ g₃) s ≤ F (g₁ ⊓ g₃ ⊔ g₂ ⊓ g₃) s ∧
    F (g₂ ⊓ g₃) s ≤ F (g₁ ⊓ g₂ ⊔ g₂ ⊓ g₃) s ∧ F (g₂ ⊓ g₃) s ≤ F (g₁ ⊓ g₃ ⊔ g₂ ⊓ g₃) s ∧
    F (g₁ ⊓ g₂ ⊔ g₁ ⊓ g₃) s ≤ F g₁ s ∧ F (g₁ ⊓ g₂ ⊔ g₂ ⊓ g₃) s ≤ F g₂ s ∧ F (g₁ ⊓ g₃ ⊔ g₂ ⊓ g₃) s ≤ F g₃ s ∧
    s = F (g₁ ⊓ g₂ ⊔ g₁ ⊓ g₃) s ⊔ F (g₁ ⊓ g₂ ⊔ g₂ ⊓ g₃) s ⊔ F (g₁ ⊓ g₃ ⊔ g₂ ⊓ g₃) s ∧
    s = F g₁ s ⊔ F g₂ s ⊔ F g₃ s := by
  have hc₁ : g₁ ⊓ g₂ ⊔ g₁ ⊓ g₃ ≤ g₁ := sup_le inf_le_left inf_le_left
  have hc₂ : g₁ ⊓ g₂ ⊔ g₂ ⊓ g₃ ≤ g₂ := sup_le inf_le_right inf_le_left
  have hc₃ : g₁ ⊓ g₃ ⊔ g₂ ⊓ g₃ ≤ g₃ := sup_le inf_le_right inf_le_right
  have e1 := hF _ _ s s (le_sup_left : g₁ ⊓ g₂ ≤ g₁ ⊓ g₂ ⊔ g₁ ⊓ g₃) le_rfl
  have e2 := hF _ _ s s (le_sup_left : g₁ ⊓ g₂ ≤ g₁ ⊓ g₂ ⊔ g₂ ⊓ g₃) le_rfl
  have e3 := hF _ _ s s (le_sup_right : g₁ ⊓ g₃ ≤ g₁ ⊓ g₂ ⊔ g₁ ⊓ g₃) le_rfl
  have e4 := hF _ _ s s (le_sup_left : g₁ ⊓ g₃ ≤ g₁ ⊓ g₃ ⊔ g₂ ⊓ g₃) le_rfl
  have e5 := hF _ _ s s (le_sup_right : g₂ ⊓ g₃ ≤ g₁ ⊓ g₂ ⊔ g₂ ⊓ g₃) le_rfl
  have e6 := hF _ _ s s (le_sup_right : g₂ ⊓ g₃ ≤ g₁ ⊓ g₃ ⊔ g₂ ⊓ g₃) le_rfl
  have v1 := hF _ _ s s hc₁ le_rfl
  have v2 := hF _ _ s s hc₂ le_rfl
  have v3 := hF _ _ s s hc₃ le_rfl
  have hu : F g₁ s ⊔ F g₂ s ⊔ F g₃ s ≤ s := sup_le (sup_le (hsc _ h₁) (hsc _ h₂)) (hsc _ h₃)
  have ha : F (g₁ ⊓ g₂ ⊔ g₁ ⊓ g₃) s ⊔ F (g₁ ⊓ g₂ ⊔ g₂ ⊓ g₃) s ⊔ F (g₁ ⊓ g₃ ⊔ g₂ ⊓ g₃) s ≤
      F g₁ s ⊔ F g₂ s ⊔ F g₃ s := sup_le_sup (sup_le_sup v1 v2) v3
  have hsa : s ≤ F (g₁ ⊓ g₂ ⊔ g₁ ⊓ g₃) s ⊔ F (g₁ ⊓ g₂ ⊔ g₂ ⊓ g₃) s ⊔ F (g₁ ⊓ g₃ ⊔ g₂ ⊓ g₃) s := by
    exact hm.le.trans (sup_le (sup_le (e1.trans (le_sup_left.trans le_sup_left))
      (e3.trans (le_sup_left.trans le_sup_left))) (e5.trans (le_sup_right.trans le_sup_left)))
  exact ⟨e1, e2, e3, e4, e5, e6, v1, v2, v3, le_antisymm hsa (ha.trans hu), le_antisymm (hsa.trans ha) hu⟩

include hF nw in
/-- **A common missing petal.** For finitely many generators with `⨅ g ∈ D`, some petal `g k` contains no response
`F x s` with `x ≥ ⨅ g` — in particular none of the meet, join-anchor or generator responses (no witness at the row
`⨅ g`, then monotonicity). The z3 label enumeration of the incidence (§34.3z¹⁰³) shows exactly this regularity. -/
theorem common_missing_petal {κ : Type*} (G : Finset κ) (g : κ → α) (hm : InD (G.inf g)) {s : α} (hs : ¬ InD s) :
    ∃ k ∈ G, ∀ x, G.inf g ≤ x → ¬ F x s ≤ g k := by
  by_contra h
  push_neg at h
  exact (nw _ hm s hs).1 (Finset.le_inf fun k hk => (h k hk).elim fun x ⟨hx, hle⟩ =>
    (hF _ _ _ _ hx le_rfl).trans hle)

/-- **Not all but one generator response can enter `D`** (DCC). At a column `s ∉ D` contracting for every generator
row, if `F pⱼ s ∈ D` for all `j ≠ i₀`, follow the `p_{i₀}` row orbit from `s` to its last outside point `v ≤ s`: every
generator takes `v` into `D` (`j ≠ i₀` by monotonicity in the column, `i₀` by the entry), against `column_lemma`. -/
theorem not_all_but_one_in [WellFoundedLT α] {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (hF' : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : κ → α)
    (nw' : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {s : α} (hs : ¬ ∃ i, s ≤ p i) (hgs : ∀ i, F (p i) s ≤ s) (i₀ : κ)
    (hin : ∀ j, j ≠ i₀ → ∃ k, F (p j) s ≤ p k) : False := by
  obtain ⟨n, hn, hend⟩ :=
    Mordor.FGTwo.orbit_end (InD := fun x => ∃ i, x ≤ p i) hF' ⟨i₀, le_rfl⟩ nw' s hs (hgs i₀)
  have hvs : (F (p i₀))^[n] s ≤ s :=
    Monotone.antitone_iterate_of_map_le (fun _ _ h => hF' _ _ _ _ le_rfl h) (hgs i₀) (Nat.zero_le n)
  obtain ⟨j, hj⟩ := Mordor.Crossing.column_lemma hF' p (hn n le_rfl) nw'
  by_cases hji : j = i₀
  · subst hji; exact hj hend
  · obtain ⟨k, hk⟩ := hin j hji
    exact hj ⟨k, (hF' _ _ _ _ le_rfl hvs).trans hk⟩

/-- **Two outside generator responses.** At a column contracting for every generator row, at least two distinct
generator responses lie outside `D` (strengthens `column_lemma`, which gives one; z3 found it as the UNSAT of the
generator-orbit length profile `(2, 1, 1)` in §34.3z¹⁰³). -/
theorem two_outside_generator_responses [WellFoundedLT α] {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (hF' : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : κ → α)
    (nw' : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {s : α} (hs : ¬ ∃ i, s ≤ p i) (hgs : ∀ i, F (p i) s ≤ s) :
    ∃ i j, i ≠ j ∧ (¬ ∃ k, F (p i) s ≤ p k) ∧ ¬ ∃ k, F (p j) s ≤ p k := by
  obtain ⟨i, hi⟩ := Mordor.Crossing.column_lemma hF' p hs nw'
  by_contra h
  push_neg at h
  refine not_all_but_one_in hF' p nw' hs hgs i fun j hji => ?_
  by_contra hj
  push_neg at hi
  exact hj (h i j (Ne.symm hji) hi)

open Mordor.Crossing in
/-- **Not all but one anchor response can enter `D`** (DCC). At a column `s ∉ D` contracting for every generator row,
suppose `F cⱼ s ∈ D` for every join anchor `cⱼ` with `j ≠ i₀`. Follow the `c_{i₀}`-orbit of `s` to its last outside
point `v ≤ s`. There every anchor takes `v` into `D` away from its own petal: `c_{i₀}` by `anchor_sandwich`; `cⱼ`
because `F cⱼ v ≤ F cⱼ s ≤ p_k` with `k ≠ j` (`anchor_sandwich` at `s`), so `F cⱼ v ≤ pⱼ` would give
`F cⱼ v ≤ pⱼ ⊓ p_k ≤ cⱼ`, a witness. This contradicts `simultaneous_entry`. -/
theorem not_all_but_one_anchor_in [WellFoundedLT α] {κ : Type*} [Fintype κ] [DecidableEq κ]
    (hF' : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : κ → α)
    (nw' : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {s : α} (hs : ¬ ∃ i, s ≤ p i) (hgs : ∀ i, F (p i) s ≤ s) (i₀ : κ)
    (hin : ∀ j, j ≠ i₀ → ∃ k, F (anchor p j) s ≤ p k) : False := by
  haveI : Nonempty κ := ⟨i₀⟩
  have hc0 : F (anchor p i₀) s ≤ s := (hF' _ _ _ _ (anchor_le p i₀) le_rfl).trans (hgs i₀)
  obtain ⟨n, hn, hend⟩ :=
    Mordor.FGTwo.orbit_end (InD := fun x => ∃ i, x ≤ p i) hF' ⟨i₀, anchor_le p i₀⟩ nw' s hs hc0
  have hv : ¬ ∃ j, (F (anchor p i₀))^[n] s ≤ p j := hn n le_rfl
  have hvs : (F (anchor p i₀))^[n] s ≤ s :=
    Monotone.antitone_iterate_of_map_le (fun _ _ h => hF' _ _ _ _ le_rfl h) hc0 (Nat.zero_le n)
  refine Mordor.Profile.simultaneous_entry hF' p nw' hv (fun i => ?_) (fun i => ?_)
  · by_cases hi : i = i₀
    · subst hi; exact hend
    · obtain ⟨k, hk⟩ := hin i hi
      exact ⟨k, (hF' _ _ _ _ le_rfl hvs).trans hk⟩
  · by_cases hi : i = i₀
    · subst hi; exact anchor_sandwich hF' p i nw' hs (hgs i) n hn
    · intro hle
      obtain ⟨k, hk⟩ := hin i hi
      have hks : ¬ F (anchor p i) s ≤ p i := anchor_sandwich hF' p i nw' hs (hgs i) 0
        (fun m hm => by rw [show m = 0 by omega]; simpa using hs)
      have hki : k ≠ i := fun h => hks (h ▸ hk)
      have hmeet : F (anchor p i) ((F (anchor p i₀))^[n] s) ≤ anchor p i :=
        (le_inf hle ((hF' _ _ _ _ le_rfl hvs).trans hk)).trans
          (Finset.le_sup (f := fun l => p i ⊓ p l) (Finset.mem_erase.2 ⟨hki, Finset.mem_univ _⟩))
      exact (nw' _ ⟨i, anchor_le p i⟩ _ hv).1 hmeet

open Mordor.Crossing in
/-- **Two outside anchor responses** (DCC): at a column contracting for every generator row, at least two distinct
join-anchor responses lie outside `D` (strengthens `contracting_simultaneous`, which gives one). Found by z3 as the
UNSAT anchor/generator orbit profiles of §34.3z¹⁰³. -/
theorem two_outside_anchor_responses [WellFoundedLT α] {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (hF' : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : κ → α)
    (nw' : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {s : α} (hs : ¬ ∃ i, s ≤ p i) (hgs : ∀ i, F (p i) s ≤ s) :
    ∃ i j, i ≠ j ∧ (¬ ∃ k, F (anchor p i) s ≤ p k) ∧ ¬ ∃ k, F (anchor p j) s ≤ p k := by
  obtain ⟨i, hi⟩ := Mordor.Profile.contracting_simultaneous hF' p nw' hs hgs
  by_contra h
  push_neg at h
  refine not_all_but_one_anchor_in hF' p nw' hs hgs i fun j hji => ?_
  by_contra hj
  push_neg at hi
  exact hj (h i j (Ne.symm hji) hi)

end Extremal

end Mordor.Profile
