import Mordor.GlobalReciprocal

/-!
# Irredundant reciprocal supports and response exchange (round 26, §34.3z¹⁰¹)

Response to the brief "irredundant reciprocal supports and response exchange". Setting of `GlobalReciprocal.lean`:
`s ∉ D` with `F x s ≤ s` for all `x ∈ D` and `s = ⨆_{p∈P} F p s`; `r ∈ D` with `r ≤ F r y` for all `y ∉ D` and
`r = ⨅_{q∈Q} F r q`.

* `minimal_finset_support`: from any finite support, an inclusion-minimal one (pure finset fact).
* `row_support_essential`, `column_support_essential`: in a minimal support every element is essential:
  `s ≰ ⨆_{P \ {p}} F p' s`, `⨅_{Q \ {q}} F r q' ≰ r`.
* `row_input_join_out`, `column_input_meet_in`: for **any** support (minimal or not), `⨆ P ∉ D` and `⨅ Q ∈ D`;
  only the support equation and no witness are used (not the uniform inequalities).
* `response_trichotomy`: all row responses `F p s` in `D`, or all column responses `F r q` outside `D`, or a mixed
  pair `F r q ∈ D`, `F p s ∉ D` — a new cross pair (`mixed_response_cross`).
* `exchange_regular`: the row exchange `P ↦ {F p s}` preserves the support equation when each `F p s ≥ p`; then it is
  the column orbit along `s` from `p`, which leaves `D` (`column_orbit_exits`): no new termination principle.
* `generator_row_support`: for a finitely generated cut the generators themselves are a row support, so every
  row support reduces to a generator subset and its responses are the first row-orbit steps `g_i(s)` (in particular
  a size-3 irredundant row support cannot contain both generators when `k = 2`).
* `generator_response_other_petal`: an inside generator response lies in another petal, so the regular exchange
  never applies to the generator support; `generator_not_caseA` (= `column_lemma`): Case A never holds there.
* `exchange_regular_column`: the dual exchange; iterating it is the row orbit along `r`, which enters `D`
  (`regular_column_iterate_enters`, the argument of `row_orbit_enters` from `q`) and so ends in Case C.
-/

namespace Mordor.Profile

set_option linter.unusedSectionVars false

/-- An inclusion-minimal finite subset with a property, below any given one. -/
theorem minimal_finset_support {β : Type*} [DecidableEq β] (Pr : Finset β → Prop) {P₀ : Finset β} (h₀ : Pr P₀) :
    ∃ P ⊆ P₀, Pr P ∧ ∀ P' ⊂ P, ¬ Pr P' := by
  obtain ⟨P, ⟨hP0, hP⟩, hmin⟩ := (wellFounded_lt (α := Finset β)).has_min {P | P ⊆ P₀ ∧ Pr P} ⟨P₀, Finset.Subset.refl _, h₀⟩
  exact ⟨P, hP0, hP, fun P' hP' hPr => hmin P' ⟨hP'.subset.trans hP0, hPr⟩ hP'⟩

variable {α : Type*} [CompleteLattice α] {F : α → α → α} {InD : α → Prop}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
  (hdown : ∀ x y, x ≤ y → InD y → InD x)
  (nw : ∀ x, InD x → ∀ y, ¬ InD y → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

/-- **Row irredundancy.** -/
theorem row_support_essential {β : Type*} [DecidableEq β] (f : β → α) {s : α} {P : Finset β}
    (hP : s = P.sup f) (hmin : ∀ P' ⊂ P, ¬ s = P'.sup f) {p : β} (hp : p ∈ P) : ¬ s ≤ (P.erase p).sup f := by
  intro h
  refine hmin _ (Finset.erase_ssubset hp) (le_antisymm h ?_)
  rw [hP]; exact Finset.sup_mono (Finset.erase_subset p P)

/-- **Column irredundancy.** -/
theorem column_support_essential {β : Type*} [DecidableEq β] (f : β → α) {r : α} {Q : Finset β}
    (hQ : r = Q.inf f) (hmin : ∀ Q' ⊂ Q, ¬ r = Q'.inf f) {q : β} (hq : q ∈ Q) : ¬ (Q.erase q).inf f ≤ r := by
  intro h
  refine hmin _ (Finset.erase_ssubset hq) (le_antisymm ?_ h)
  rw [hQ]; exact Finset.inf_mono (Finset.erase_subset q Q)

include hF nw in
/-- **The input join of a row support is outside `D`.** -/
theorem row_input_join_out {s : α} (hs : ¬ InD s) {P : Finset α}
    (hP : s = P.sup fun p => F p s) : ¬ InD (P.sup id) := by
  intro hin
  have hle : s ≤ F (P.sup id) s :=
    hP.le.trans (Finset.sup_le fun p hp => hF _ _ _ _ (Finset.le_sup (f := id) hp) le_rfl)
  exact (nw _ hin s hs).2 hle

include hF nw in
/-- **The input meet of a column support is in `D`.** -/
theorem column_input_meet_in {r : α} (hr : InD r) {Q : Finset α} (hQ : r = Q.inf fun q => F r q) :
    InD (Q.inf id) := by
  by_contra hout
  have hle : F r (Q.inf id) ≤ r :=
    (Finset.le_inf fun q hq => hF _ _ _ _ le_rfl (Finset.inf_le (f := id) hq)).trans hQ.ge
  exact (nw r hr _ hout).1 hle

/-- **Response trichotomy.** -/
theorem response_trichotomy {β γ : Type*} (u : β → α) (v : γ → α) :
    (∀ p, InD (u p)) ∨ (∀ q, ¬ InD (v q)) ∨ ∃ p q, ¬ InD (u p) ∧ InD (v q) := by
  by_cases h1 : ∀ p, InD (u p)
  · exact Or.inl h1
  · by_cases h2 : ∀ q, ¬ InD (v q)
    · exact Or.inr (Or.inl h2)
    · push_neg at h1 h2
      obtain ⟨p, hp⟩ := h1; obtain ⟨q, hq⟩ := h2
      exact Or.inr (Or.inr ⟨p, q, hp, hq⟩)

include nw in
/-- **The mixed response pair is a cross pair.** -/
theorem mixed_response_cross {u v : α} (hu : ¬ InD u) (hv : InD v) : ¬ F v u ≤ v ∧ ¬ u ≤ F v u :=
  nw v hv u hu

include hF in
/-- **Regular row exchange** preserves the support equation (and is a column-orbit step along `s`). -/
theorem exchange_regular [DecidableEq α] {s : α} (hsc : ∀ x, InD x → F x s ≤ s) {P : Finset α}
    (hP : s = P.sup fun p => F p s) (hexp : ∀ p ∈ P, p ≤ F p s) (hin : ∀ p ∈ P, InD (F p s)) :
    s = (P.image fun p => F p s).sup fun u => F u s := by
  apply le_antisymm
  · rw [Finset.sup_image]
    calc s = P.sup (fun p => F p s) := hP
      _ ≤ P.sup ((fun u => F u s) ∘ fun p => F p s) :=
          Finset.sup_mono_fun fun p hp => hF _ _ _ _ (hexp p hp) le_rfl
  · exact Finset.sup_le fun u hu => by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hu; show F (F p s) s ≤ s; exact hsc _ (hin p hp)

include hF in
/-- **The generators are a row support.** If `D = ⋃_{g∈G} ↓g` and `s` satisfies the aggregate row equation, then
`s = ⨆_{g∈G} F g s`: every row response is dominated by a generator response, so row supports reduce to subsets of
the generators, and the row responses of the canonical support are the first row-orbit steps `g_i(s)`. -/
theorem generator_row_support {s : α} (G : Finset α) (hG : ∀ g ∈ G, InD g)
    (hgen : ∀ x, InD x → ∃ g ∈ G, x ≤ g) (hsc : ∀ x, InD x → F x s ≤ s) (hΦ : s ≤ Φagg F InD s) :
    s = G.sup fun g => F g s := by
  apply le_antisymm
  · refine hΦ.trans (iSup_le fun x => ?_)
    obtain ⟨g, hg, hxg⟩ := hgen x.1 x.2
    exact (hF _ _ _ _ hxg le_rfl).trans (Finset.le_sup (f := fun g => F g s) hg)
  · exact Finset.sup_le fun g hg => hsc g (hG g hg)

include nw in
/-- **Inside generator responses change petal.** For an antichain of generators, an inside response `F g s ∈ D`
lies below a *different* generator, and `g ≰ F g s`: the regular-exchange hypothesis of `exchange_regular` never
holds on the generator support. -/
theorem generator_response_other_petal {s : α} (hs : ¬ InD s) (G : Finset α) (hG : ∀ g ∈ G, InD g)
    (hgen : ∀ x, InD x → ∃ g ∈ G, x ≤ g) (hanti : ∀ g ∈ G, ∀ g' ∈ G, g ≤ g' → g = g') {g : α} (hg : g ∈ G)
    (hin : InD (F g s)) : (∃ g' ∈ G, g' ≠ g ∧ F g s ≤ g') ∧ ¬ g ≤ F g s := by
  obtain ⟨g', hg', hle⟩ := hgen _ hin
  have hne : g' ≠ g := fun h => (nw g (hG g hg) s hs).1 (h ▸ hle)
  exact ⟨⟨g', hg', hne, hle⟩, fun h => hne (hanti g hg g' hg' (h.trans hle)).symm⟩

/-- **Case A never holds on the generator support** (it is the old `column_lemma`): at a column `s ∉ D` some generator
response `F pᵢ s` is outside `D`. With `generator_row_support`, the response trichotomy on the canonical row support
reduces to Case B (all column responses outside) or Case C (a mixed pair). -/
theorem generator_not_caseA {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] (hF' : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : ι → α) {s : α} (hs : ¬ ∃ i, s ≤ p i)
    (nw' : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) :
    ¬ ∀ i, ∃ j, F (p i) s ≤ p j := by
  obtain ⟨i, hi⟩ := Mordor.Crossing.column_lemma hF' p hs nw'
  exact fun h => hi (h i)

include hF in
/-- **Regular column exchange** (dual of `exchange_regular`): `Q ↦ {F r q}` preserves `r = ⨅ F r ·` when each
`F r q ≤ q` and `F r q ∉ D`. Iterating it is the row orbit of `F r` from each `q`, a descending chain that
enters `D` under DCC (`regular_column_iterate_enters`), i.e. produces an inside column response: Case C. -/
theorem exchange_regular_column [DecidableEq α] {r : α} (hrc : ∀ y, ¬ InD y → r ≤ F r y) {Q : Finset α}
    (hQ : r = Q.inf fun q => F r q) (hcon : ∀ q ∈ Q, F r q ≤ q) (hout : ∀ q ∈ Q, ¬ InD (F r q)) :
    r = (Q.image fun q => F r q).inf fun v => F r v := by
  apply le_antisymm
  · exact Finset.le_inf fun v hv => by
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hv; show r ≤ F r (F r q); exact hrc _ (hout q hq)
  · rw [Finset.inf_image]
    calc Q.inf ((fun v => F r v) ∘ fun q => F r q) ≤ Q.inf (fun q => F r q) :=
          Finset.inf_mono_fun fun q hq => hF _ _ _ _ le_rfl (hcon q hq)
      _ = r := hQ.symm

include hF nw in
/-- **Regular column exchange terminates in `D`.** If `F r q ≤ q` with `r ∈ D`, `q ∉ D`, the descending iterates
`(F r)^[n] q` reach `D` (DCC; the argument of `row_orbit_enters` started at `q` instead of `⊤`). -/
theorem regular_column_iterate_enters [WellFoundedLT α] {r q : α} (hr : InD r) (hcon : F r q ≤ q) :
    ∃ n, InD ((F r)^[n] q) := by
  by_contra hall
  push_neg at hall
  have anti : Antitone fun n => (F r)^[n] q :=
    Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) hcon
  obtain ⟨_, ⟨M, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := α)).has_min (Set.range fun n => (F r)^[n] q) ⟨_, 0, rfl⟩
  have e := eq_of_le_of_not_lt (anti (Nat.le_succ M)) (hmin _ ⟨M + 1, rfl⟩)
  have hfix : F r ((F r)^[M] q) = (F r)^[M] q := by rw [← Function.iterate_succ_apply' (F r) M q]; exact e
  exact (nw r hr _ (hall M)).2 hfix.ge

end Mordor.Profile
