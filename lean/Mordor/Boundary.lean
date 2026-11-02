import Mordor.TransferSets
import Mordor.Feedback
import Mathlib.Order.CompactlyGenerated.Basic

/-!
# Sink rows and the minimal boundary (round 26, §34.3z⁷⁹)

Response to the brief "sink-row preservation and minimal-boundary descent". `D = ⋃ᵢ ↓pᵢ` finite, `F` monotone, no
witness, `Transfer`/`SelfEntry` as in `TransferSets.lean`.

* `sink_row_out`, `sink_row_incomparable`: at a column `v ∉ D` where `j` does not transfer, `F pⱼ v ∉ D`; if moreover
  `F pⱼ v ≰ v` (the sink cone), then `F pⱼ v` and `v` are incomparable. Only `¬ Transfer j v` at `v` itself is used.
* `meet_proj_lt`, `meet_iterate_enters`: `v ⊓ F x v < v` for **every** row `x ∈ D` and every column `v ∉ D` (no
  witness), so every meet-projected iteration enters `D` (DCC). This carries no sink information.
* `minimal_sink_boundary`: a minimal outside column `v` below a sink cone, with `q = F pⱼ v ∉ D`, `q ∥ v`,
  `v ⊓ q ∈ D`, `v ⊓ q < v`. (`v ⊓ q ∈ D` holds for every `q ≱ v` by minimality alone.)
* `lower_boundary_cases` (ACC): `v` is a finite join of strict predecessors, or has a greatest strict predecessor.
* `cover_labels_empty`, `cover_labels_three`: a finite cover of `v ∉ D` by elements of `D` has empty total label
  intersection; for three generators it contains two elements with disjoint labels, or the triangle
  `{0,1}, {1,2}, {0,2}` (`Feedback.blockers_three`).
* `minimal_row_fixedpoint` (ACC): at a minimal outside column `v`, the row map `x ↦ v ⊓ F x v` has a fixed point
  `r < v`; then `r ≤ F r v`, `v ⊓ F r v = r` and `F r v ∥ v`. No case split on the lower boundary is needed.
* `jump_fixedpoint` (DCC): if every strict predecessor of `v ∉ D` lies below `B ∈ D`, the map `x ↦ B ⊓ F x v` has a
  fixed point `r ≤ B` with `r ≤ F r v`, `F r v ∥ v`, `F r v ≰ B`. (`F r v ≤ B` would make `r = F r v` a witness.)
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

section
variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF nw in
/-- **The row of a non-transferring generator leaves `D`.** -/
theorem sink_row_out {j : ι} {v : α} (hv : ¬ ∃ i, v ≤ p i) (hj : ¬ Transfer F p j v) :
    ¬ ∃ k, F (p j) v ≤ p k := by
  rintro ⟨k, hk⟩
  by_cases hkj : k = j
  · subst hkj; exact (nw _ ⟨k, le_rfl⟩ v hv).1 hk
  · exact hj ⟨hv, k, hkj, (hF _ _ _ _ (anchor_le p j) le_rfl).trans hk⟩

include nw in
theorem sink_row_incomparable {j : ι} {v : α} (hv : ¬ ∃ i, v ≤ p i) (hnc : ¬ F (p j) v ≤ v) :
    ¬ F (p j) v ≤ v ∧ ¬ v ≤ F (p j) v :=
  ⟨hnc, (nw _ ⟨j, le_rfl⟩ v hv).2⟩

include nw in
/-- **Meet-projected descent holds everywhere**: for every row in `D` and column outside `D`. -/
theorem meet_proj_lt {x v : α} (hx : ∃ i, x ≤ p i) (hv : ¬ ∃ i, v ≤ p i) : v ⊓ F x v < v :=
  lt_of_le_of_ne inf_le_left fun h => (nw x hx v hv).2 (inf_eq_left.1 h)

include nw in
theorem meet_iterate_enters [WellFoundedLT α] {x : α} (hx : ∃ i, x ≤ p i) :
    ∀ v, ∃ n, ∃ i, (fun w => w ⊓ F x w)^[n] v ≤ p i := by
  intro v
  induction v using WellFoundedLT.induction with
  | _ v ih =>
    by_cases hv : ∃ i, v ≤ p i
    · exact ⟨0, hv⟩
    · obtain ⟨n, hn⟩ := ih _ (meet_proj_lt p nw hx hv)
      exact ⟨n + 1, by rwa [Function.iterate_succ_apply]⟩

include hF nw in
/-- **The minimal boundary configuration of a sink.** -/
theorem minimal_sink_boundary [WellFoundedLT α] {u : α} {j : ι} (hu : ¬ ∃ i, u ≤ p i)
    (hsink : ∀ v, v ≤ u → ¬ Transfer F p j v) (hnc : ∀ v, v ≤ u → (¬ ∃ i, v ≤ p i) → ¬ F (p j) v ≤ v) :
    ∃ v, v ≤ u ∧ (¬ ∃ i, v ≤ p i) ∧ (∀ w, w < v → ∃ i, w ≤ p i) ∧ (¬ ∃ k, F (p j) v ≤ p k) ∧
      ¬ F (p j) v ≤ v ∧ ¬ v ≤ F (p j) v ∧ (∃ i, v ⊓ F (p j) v ≤ p i) ∧ v ⊓ F (p j) v < v := by
  obtain ⟨v, ⟨hvu, hv⟩, hmin⟩ := (wellFounded_lt (α := α)).has_min {v | v ≤ u ∧ ¬ ∃ i, v ≤ p i} ⟨u, le_rfl, hu⟩
  have hbelow : ∀ w, w < v → ∃ i, w ≤ p i := fun w hw => by
    by_contra h; exact hmin w ⟨hw.le.trans hvu, h⟩ hw
  have hlt := meet_proj_lt p nw ⟨j, le_rfl⟩ hv
  exact ⟨v, hvu, hv, hbelow, sink_row_out hF p nw hv (hsink v hvu), hnc v hvu hv, (nw _ ⟨j, le_rfl⟩ v hv).2,
    hbelow _ hlt, hlt⟩

include hF nw in
/-- **Row-projected fixed point at a minimal outside column** (ACC). If every strict predecessor of `v ∉ D` lies in
`D`, the row map `G x = v ⊓ F x v` sends `{x | x < v}` into itself (no witness), so a maximal post-fixed point `r < v`
of `G` above `⊥` is a fixed point. Then `r ≤ F r v`, `v ⊓ F r v = r`, and `F r v ∥ v`: `F r v ≤ v` would give
`F r v = r`, a witness. Maximality: no `y` with `r < y < v` has `y ≤ F y v`. No lower-boundary case split is needed; `jump_fixedpoint` is the variant where the strict
predecessors have a largest element `B` (and then DCC suffices). -/
theorem minimal_row_fixedpoint [WellFoundedGT α] [Nonempty ι] {v : α} (hv : ¬ ∃ i, v ≤ p i)
    (hbelow : ∀ w, w < v → ∃ i, w ≤ p i) :
    ∃ r, r < v ∧ v ⊓ F r v = r ∧ r ≤ F r v ∧ ¬ F r v ≤ v ∧ ¬ v ≤ F r v ∧
      ∀ y, r < y → y < v → ¬ y ≤ F y v := by
  have hG : ∀ x, x < v → v ⊓ F x v < v := fun x hx => meet_proj_lt p nw (hbelow x hx) hv
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hbot : (⊥ : α) < v := lt_of_le_of_ne bot_le fun e => hv ⟨i₀, e ▸ bot_le⟩
  obtain ⟨r, ⟨hrv, hGr⟩, hmax⟩ :=
    (wellFounded_gt (α := α)).has_min {x | x < v ∧ x ≤ v ⊓ F x v} ⟨⊥, hbot, bot_le⟩
  have hfix : v ⊓ F r v = r := by
    refine (eq_of_le_of_not_lt hGr fun hlt => hmax _ ⟨hG r hrv, ?_⟩ hlt).symm
    exact le_inf inf_le_left ((hF _ _ _ _ hGr le_rfl).trans' inf_le_right)
  obtain ⟨hn1, hn2⟩ := nw r (hbelow r hrv) v hv
  refine ⟨r, hrv, hfix, hfix.symm.le.trans inf_le_right, fun h => hn1 ?_, hn2,
    fun y hry hyv hy => hmax y ⟨hyv, le_inf hyv.le hy⟩ hry⟩
  have e := hfix; rw [inf_eq_right.2 h] at e; exact e.le

include hF nw in
/-- **The jump case.** If every strict predecessor of `v ∉ D` lies below `B ∈ D`, then `x ↦ B ⊓ F x v` has a fixed point
`r ≤ B` whose value `F r v` is above `r`, incomparable with `v`, and not below `B`. -/
theorem jump_fixedpoint [WellFoundedLT α] {B v : α} (hB : ∃ i, B ≤ p i) (hv : ¬ ∃ i, v ≤ p i)
    (hBv : ∀ x, x < v → x ≤ B) :
    ∃ r, r ≤ B ∧ r = B ⊓ F r v ∧ r ≤ F r v ∧ ¬ F r v ≤ v ∧ ¬ v ≤ F r v ∧ ¬ F r v ≤ B := by
  obtain ⟨r, ⟨hrB, hHr⟩, hmin⟩ :=
    (wellFounded_lt (α := α)).has_min {x | x ≤ B ∧ B ⊓ F x v ≤ x} ⟨B, le_rfl, inf_le_left⟩
  have hfix : B ⊓ F r v = r := by
    refine eq_of_le_of_not_lt hHr fun hlt => hmin _ ⟨inf_le_left, ?_⟩ hlt
    exact le_inf inf_le_left (inf_le_right.trans (hF _ _ _ _ hHr le_rfl))
  have hrD : ∃ i, r ≤ p i := hB.elim fun i hi => ⟨i, hrB.trans hi⟩
  obtain ⟨hn1, hn2⟩ := nw r hrD v hv
  have hrF : r ≤ F r v := hfix.symm.le.trans inf_le_right
  have hnB : ¬ F r v ≤ B := fun h => hn1 (by have e := hfix; rw [inf_eq_right.2 h] at e; exact e.le)
  refine ⟨r, hrB, hfix.symm, hrF, fun h => hnB (hBv _ (lt_of_le_of_ne h fun e => hn2 e.ge)), hn2, hnB⟩

end

section
variable {α : Type*} [CompleteLattice α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lower boundary of a column** (ACC): a finite join of strict predecessors, or a greatest strict predecessor. -/
theorem lower_boundary_cases [WellFoundedGT α] (v : α) :
    (∃ t : Finset α, (∀ x ∈ t, x < v) ∧ t.sup id = v) ∨
      (sSup {x | x < v} < v ∧ ∀ x, x < v → x ≤ sSup {x | x < v}) := by
  have hle : sSup {x | x < v} ≤ v := sSup_le fun _ hx => le_of_lt hx
  rcases eq_or_lt_of_le hle with heq | hlt
  · obtain ⟨t, ht, hsup⟩ := CompleteLattice.WellFoundedGT.isSupFiniteCompact α {x | x < v}
    exact Or.inl ⟨t, fun x hx => ht hx, hsup ▸ heq⟩
  · exact Or.inr ⟨hlt, fun x hx => le_sSup hx⟩

/-- A finite cover of a column outside `D` by elements of `D` has empty total label intersection. -/
theorem cover_labels_empty (p : ι → α) {v : α} (hv : ¬ ∃ i, v ≤ p i) {t : Finset α} (hsup : t.sup id = v) :
    ∀ k, ∃ x ∈ t, ¬ x ≤ p k := by
  intro k
  by_contra h
  push_neg at h
  exact hv ⟨k, hsup ▸ Finset.sup_le fun x hx => h x hx⟩

open Classical in
/-- The label of an element: the generators above it. -/
noncomputable def lab (p : ι → α) (x : α) : Finset ι := Finset.univ.filter (fun k => x ≤ p k)

/-- **Three generators**: a finite cover of `v ∉ D` by elements of `D` contains two elements with disjoint labels, or
elements with the three pairwise labels `{0,1}`, `{1,2}`, `{0,2}` (the triangle). -/
theorem cover_labels_three (p : Fin 3 → α) {v : α} (hv : ¬ ∃ i, v ≤ p i) {t : Finset α}
    (hD : ∀ x ∈ t, ∃ i, x ≤ p i) (hsup : t.sup id = v) :
    (∃ x ∈ t, ∃ y ∈ t, Disjoint (lab p x) (lab p y)) ∨
      ((∃ x ∈ t, lab p x = {0, 1}) ∧ (∃ x ∈ t, lab p x = {1, 2}) ∧ (∃ x ∈ t, lab p x = {0, 2})) := by
  classical
  have hmem : ∀ x k, k ∈ lab p x ↔ x ≤ p k := fun x k => by simp [lab]
  rcases Feedback.blockers_three (t.image (lab p))
      (fun A hA => by
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hA
        obtain ⟨i, hi⟩ := hD x hx; exact ⟨i, (hmem x i).2 hi⟩)
      (fun k => by
        obtain ⟨x, hx, hk⟩ := cover_labels_empty p hv hsup k
        exact ⟨lab p x, Finset.mem_image.2 ⟨x, hx, rfl⟩, fun h => hk ((hmem x k).1 h)⟩) with
    ⟨A, hA, B, hB, hAB⟩ | ⟨h1, h2, h3⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hA
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hB
    exact Or.inl ⟨x, hx, y, hy, hAB⟩
  · obtain ⟨x, hx, ex⟩ := Finset.mem_image.1 h1
    obtain ⟨y, hy, ey⟩ := Finset.mem_image.1 h2
    obtain ⟨z, hz, ez⟩ := Finset.mem_image.1 h3
    exact Or.inr ⟨⟨x, hx, ex⟩, ⟨y, hy, ey⟩, ⟨z, hz, ez⟩⟩

end
end Mordor.Profile
