import Mordor.Boundary
import Mordor.Transport

/-!
# The row orbit's greatest fixed point is invisible to the cut problem (round 26, §34.3z⁸⁰)

Response to the brief "the global orbit below a clipped row fixed point". For a row `r ∈ D` the `F r`-orbit of `⊤`
descends to the greatest fixed point `z` of `F r` (`row_orbit_gfp`), and `z ∈ D`. The brief's conjecture is
`z ≰ r` for the row fixed point `r` of `Boundary.minimal_row_fixedpoint`.

* `row_orbit_gfp` (DCC): the orbit is eventually constant at `z = F r z ∈ D`, and every post-fixed point of `F r` is
  below `z`.
* `normalLow_postfixed_bot`, `normalLow_gfp_le`: **the conjecture fails in the normal form of every `F`.** With
  `G = normalizeLow F D` (`⊥` on `L × D`, `F` on `D × Dᶜ`, `⊤` on `Dᶜ × Dᶜ`; monotone, `Transport.normalizeLow_mono`,
  equal to `F` on cross cells, `normalizeLow_cross`, hence witness-free with the same minimal columns and the same row
  fixed points), the only post-fixed point of `G r` is `⊥`, so `ν(G r) = ⊥ ≤ r`.
* `clipped_squeeze`: for the brief's weakened sandwich, the squeeze survives with the clipped step `s ⊓ F a s` under the
  weaker hypothesis `F r s ≤ s`; what fails is the base case, since `s ⊓ F a s` may lie in `D`.
* `sink_no_anchor_contracting`: the weakened anchor sandwich reduces to its base case "no `cⱼ`-contracting column
  self-enters", and that base case would exclude every `cⱼ`-contracting column from a sink cone of `j`.
* Consequently a proof of `ν(F r) ≰ r` from monotonicity and no witness would refute every counterexample at once: it
  is as strong as Cut, and the iterates after the first entry into `D` (values of `F` on `D × D`) carry no
  information about the cut problem.
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The row orbit of `⊤` ends at the greatest fixed point**, which lies in `D`. -/
theorem row_orbit_gfp [WellFoundedLT α] {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : ι → α) (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {r : α} (hr : ∃ i, r ≤ p i) :
    ∃ z, (∃ N, ∀ n, N ≤ n → (F r)^[n] ⊤ = z) ∧ F r z = z ∧ (∃ i, z ≤ p i) ∧ ∀ w, w ≤ F r w → w ≤ z := by
  have hmono : Monotone (F r) := fun _ _ h => hF _ _ _ _ le_rfl h
  have hanti : Antitone fun n => (F r)^[n] ⊤ := Monotone.antitone_iterate_of_map_le hmono le_top
  obtain ⟨_, ⟨N, rfl⟩, hmin⟩ := (wellFounded_lt (α := α)).has_min (Set.range fun n => (F r)^[n] ⊤) ⟨⊤, 0, rfl⟩
  have hconst : ∀ n, N ≤ n → (F r)^[n] ⊤ = (F r)^[N] ⊤ := fun n hn =>
    eq_of_le_of_not_lt (hanti hn) (hmin _ ⟨n, rfl⟩)
  have hfix : F r ((F r)^[N] ⊤) = (F r)^[N] ⊤ := by
    rw [← Function.iterate_succ_apply' (F r) N ⊤]; exact hconst _ (Nat.le_succ N)
  refine ⟨_, ⟨N, hconst⟩, hfix, ?_, fun w hw => ?_⟩
  · by_contra hz; exact (nw r hr _ hz).2 hfix.ge
  · have : ∀ n, w ≤ (F r)^[n] ⊤ := fun n => by
      induction n with
      | zero => exact le_top
      | succ n ih => rw [Function.iterate_succ_apply']; exact hw.trans (hmono ih)
    exact this N

/-- **In normal form the row orbit collapses**: the only post-fixed point of `G r` (`r ∈ D`) is `⊥`. -/
theorem normalLow_postfixed_bot {F : α → α → α} (p : ι → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {r : α} (hr : ∃ i, r ≤ p i) {w : α} (hw : w ≤ normalizeLow F {x | ∃ i, x ≤ p i} r w) : w = ⊥ := by
  by_cases hwD : ∃ i, w ≤ p i
  · have : normalizeLow F {x | ∃ i, x ≤ p i} r w = ⊥ := by simp [normalizeLow, hwD]
    exact le_bot_iff.1 (this ▸ hw)
  · rw [normalizeLow_cross (D := {x | ∃ i, x ≤ p i}) hr hwD] at hw
    exact absurd hw (nw r hr w hwD).2

/-- The normal form is monotone, agrees with `F` on cross cells (so it is witness-free, with the same minimal columns
and row fixed points), and its row orbits have greatest fixed point `⊥ ≤ r`. -/
theorem normalLow_gfp_le {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) :
    let G := normalizeLow F {x | ∃ i, x ≤ p i}
    (∀ x x' y y', x ≤ x' → y ≤ y' → G x y ≤ G x' y') ∧
    (∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → G x y = F x y) ∧
    (∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ G x y ≤ x ∧ ¬ y ≤ G x y) ∧
    ∀ r, (∃ i, r ≤ p i) → ∀ w, w ≤ G r w → w ≤ r := by
  intro G
  have hcross : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → G x y = F x y := fun x hx y hy =>
    normalizeLow_cross (D := {x | ∃ i, x ≤ p i}) hx hy
  refine ⟨normalizeLow_mono (fun _ _ hxy ⟨i, hi⟩ => ⟨i, hxy.trans hi⟩) hF, hcross,
    fun x hx y hy => hcross x hx y hy ▸ nw x hx y hy, fun r hr w hw => ?_⟩
  rw [normalLow_postfixed_bot p nw hr hw]; exact bot_le

/-- **The clipped squeeze.** With `r ≤ a`, `h = F r` and the clipped step `g' s = s ⊓ F a s`, the hypothesis `F r s ≤ s`
(weaker than `F a s ≤ s`) already gives the squeeze `h^[k+1] s ≤ h^[k] (g' s) ≤ h^[k] s` of `FGTwo.sandwich`, and it is
inherited: `F r (g' s) ≤ g' s`. -/
theorem clipped_squeeze {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {r a s : α}
    (hra : r ≤ a) (hs : F r s ≤ s) :
    (∀ k, (F r)^[k + 1] s ≤ (F r)^[k] (s ⊓ F a s) ∧ (F r)^[k] (s ⊓ F a s) ≤ (F r)^[k] s) ∧
      F r (s ⊓ F a s) ≤ s ⊓ F a s := by
  have hmono : Monotone (F r) := fun _ _ h => hF _ _ _ _ le_rfl h
  have h1 : F r s ≤ s ⊓ F a s := le_inf hs (hF _ _ _ _ hra le_rfl)
  refine ⟨fun k => ⟨?_, (hmono.iterate k) inf_le_left⟩, le_inf ((hmono inf_le_left).trans hs)
    (hF _ _ _ _ hra inf_le_left)⟩
  rw [Function.iterate_succ_apply]; exact (hmono.iterate k) h1

/-- **The weakened anchor sandwich is its own base case.** If no anchor-contracting column self-enters
(`F cⱼ u ≤ u → ¬ F cⱼ u ≤ pⱼ`, the would-be base case of a sandwich with hypothesis `F cⱼ s ≤ s`), then on a sink cone
of `j` no column is `cⱼ`-contracting: its `F cⱼ`-orbit descends inside the cone, enters `D` (`orbit_end`) at a value
that cannot transfer, hence below `pⱼ`, from a last point that is itself `cⱼ`-contracting. -/
theorem sink_no_anchor_contracting [WellFoundedLT α] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {j : ι}
    (hweak : ∀ u, (¬ ∃ i, u ≤ p i) → F (anchor p j) u ≤ u → ¬ F (anchor p j) u ≤ p j)
    {u₀ : α} (hsink : ∀ v, v ≤ u₀ → ¬ Transfer F p j v) {u : α} (huu : u ≤ u₀) (hu : ¬ ∃ i, u ≤ p i) :
    ¬ F (anchor p j) u ≤ u := by
  intro hcu
  have hmono : Monotone (F (anchor p j)) := fun _ _ h => hF _ _ _ _ le_rfl h
  obtain ⟨n, hU, k, hk⟩ := FGTwo.orbit_end (InD := fun x => ∃ i, x ≤ p i) hF ⟨j, anchor_le p j⟩ nw u hu hcu
  have hanti := Monotone.antitone_iterate_of_map_le hmono hcu
  have hwu : (F (anchor p j))^[n] u ≤ u := hanti (Nat.zero_le n)
  have hwc : F (anchor p j) ((F (anchor p j))^[n] u) ≤ (F (anchor p j))^[n] u := by
    rw [← Function.iterate_succ_apply' (F (anchor p j)) n u]; exact hanti (Nat.le_succ n)
  have hkj : k = j := by
    by_contra hne; exact hsink _ (hwu.trans huu) ⟨hU n le_rfl, k, hne, hk⟩
  exact hweak _ (hU n le_rfl) hwc (hkj ▸ hk)

end Mordor.Profile
