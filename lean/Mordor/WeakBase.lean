import Mordor.OrbitGfp

/-!
# The weak base case: anchor-contracting self-entries (round 26, §34.3z⁸¹)

The cross-cell target left by §34.3z⁸⁰: **weak base for `j`**: no column `u ∉ D` with `F cⱼ u ≤ u` has
`F cⱼ u ≤ pⱼ`. (`l4` is the case `F pⱼ u ≤ u`.)

* `weak_base_descent` (DCC): a failure of the weak base descends along the clipped step `u ↦ u ⊓ F pⱼ u` to a failure
  at a column where the clipped value `d = u ⊓ F pⱼ u` lies in `D`.
* `weak_base_reduced`: at such a column, `e = F cⱼ u ≤ d`, the label of `d` is exactly `{j}`, `q = F pⱼ u ∉ D` and
  `q ∥ u`. This is the smallest configuration a counterexample to the weak base must contain.
* `weak_base_two` (DCC): for two generators the weak base for both generators is already contradictory (the single
  anchor orbit of `⊤` enters `D` from a contracting last point). So the weak base is not a lemma on the way to `cut_two`
  but a restatement of it; for three generators it is at least as strong as the open case wherever a sink cone has an
  anchor-contracting column (`sink_no_anchor_contracting`).
* `anchor_join_dichotomy` (DCC): with `Ψ u = ⨆ᵢ F cᵢ u`, either the weak base fails somewhere, or the `Ψ`-orbit of
  `⊤` never enters `D`, so `ν Ψ ∉ D` and `ν Ψ = ⨆ᵢ F cᵢ (ν Ψ)` with every term strictly below it.
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF nw in
/-- **Descent of a weak-base failure** along the clipped generator step. -/
theorem weak_base_descent [WellFoundedLT α] {j : ι} :
    ∀ u, (¬ ∃ i, u ≤ p i) → F (anchor p j) u ≤ u → F (anchor p j) u ≤ p j →
      ∃ w, w ≤ u ∧ (¬ ∃ i, w ≤ p i) ∧ F (anchor p j) w ≤ w ∧ F (anchor p j) w ≤ p j ∧
        ∃ i, w ⊓ F (p j) w ≤ p i := by
  intro u
  induction u using WellFoundedLT.induction with
  | _ u ih =>
    intro hu hcu hself
    by_cases hd : ∃ i, u ⊓ F (p j) u ≤ p i
    · exact ⟨u, le_rfl, hu, hcu, hself, hd⟩
    · have hle : u ⊓ F (p j) u ≤ u := inf_le_left
      have hc' : F (anchor p j) (u ⊓ F (p j) u) ≤ u ⊓ F (p j) u :=
        le_inf ((hF _ _ _ _ le_rfl hle).trans hcu)
          (hF _ _ _ _ (anchor_le p j) inf_le_left)
      obtain ⟨w, hwu, hw⟩ := ih _ (meet_proj_lt p nw ⟨j, le_rfl⟩ hu) hd hc'
        ((hF _ _ _ _ le_rfl hle).trans hself)
      exact ⟨w, hwu.trans hle, hw⟩

include hF nw in
/-- **The reduced configuration.** -/
theorem weak_base_reduced {j : ι} {u : α} (hu : ¬ ∃ i, u ≤ p i) (hcu : F (anchor p j) u ≤ u)
    (hself : F (anchor p j) u ≤ p j) (hd : ∃ i, u ⊓ F (p j) u ≤ p i) :
    F (anchor p j) u ≤ u ⊓ F (p j) u ∧ u ⊓ F (p j) u ≤ p j ∧ (∀ k, k ≠ j → ¬ u ⊓ F (p j) u ≤ p k) ∧
      (¬ ∃ k, F (p j) u ≤ p k) ∧ ¬ F (p j) u ≤ u ∧ ¬ u ≤ F (p j) u := by
  have hcp : F (anchor p j) u ≤ F (p j) u := hF _ _ _ _ (anchor_le p j) le_rfl
  have he : F (anchor p j) u ≤ u ⊓ F (p j) u := le_inf hcu hcp
  have hnot : ∀ k, k ≠ j → ¬ F (anchor p j) u ≤ p k := fun k hk h =>
    (nw _ ⟨j, anchor_le p j⟩ u hu).1 ((le_inf hself h).trans (meet_le_anchor p hk))
  have hlab : ∀ k, k ≠ j → ¬ u ⊓ F (p j) u ≤ p k := fun k hk h => hnot k hk (he.trans h)
  have hq : ¬ ∃ k, F (p j) u ≤ p k := by
    rintro ⟨k, hk⟩
    by_cases hkj : k = j
    · subst hkj; exact (nw _ ⟨k, le_rfl⟩ u hu).1 hk
    · exact hnot k hkj (hcp.trans hk)
  obtain ⟨i, hi⟩ := hd
  have hij : i = j := by by_contra h; exact hlab i h hi
  refine ⟨he, hij ▸ hi, hlab, hq, fun h => hq ?_, (nw _ ⟨j, le_rfl⟩ u hu).2⟩
  exact ⟨i, by rwa [inf_eq_right.2 h] at hi⟩

end Mordor.Profile

namespace Mordor.Profile
open Mordor.Crossing
variable {α : Type*} [Lattice α] [BoundedOrder α]

/-- **For two generators the weak base is `cut_two` restated.** -/
theorem weak_base_two [WellFoundedLT α] {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : Fin 2 → α) (htop : ¬ ∃ i, ⊤ ≤ p i)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (hweak : ∀ j u, (¬ ∃ i, u ≤ p i) → F (anchor p j) u ≤ u → ¬ F (anchor p j) u ≤ p j) : False := by
  have hanc : ∀ j, anchor p j = p 0 ⊓ p 1 := by
    intro j
    fin_cases j
    · show (Finset.univ.erase (0 : Fin 2)).sup (fun k => p 0 ⊓ p k) = _
      rw [show Finset.univ.erase (0 : Fin 2) = {1} by decide, Finset.sup_singleton]
    · show (Finset.univ.erase (1 : Fin 2)).sup (fun k => p 1 ⊓ p k) = _
      rw [show Finset.univ.erase (1 : Fin 2) = {0} by decide, Finset.sup_singleton, inf_comm]
  have hcD : ∃ i, anchor p 0 ≤ p i := ⟨0, anchor_le p 0⟩
  obtain ⟨n, hU, k, hk⟩ :=
    FGTwo.orbit_end (InD := fun x => ∃ i, x ≤ p i) hF hcD nw ⊤ htop le_top
  have hmono : Monotone (F (anchor p 0)) := fun _ _ h => hF _ _ _ _ le_rfl h
  have hanti := Monotone.antitone_iterate_of_map_le hmono (le_top : F (anchor p 0) ⊤ ≤ ⊤)
  have hwc : F (anchor p 0) ((F (anchor p 0))^[n] ⊤) ≤ (F (anchor p 0))^[n] ⊤ := by
    rw [← Function.iterate_succ_apply' (F (anchor p 0)) n ⊤]; exact hanti (Nat.le_succ n)
  rw [hanc 0] at hwc hk
  exact hweak k _ (by simpa [hanc] using hU n le_rfl) (by rw [hanc k]; exact hwc) (by rw [hanc k]; exact hk)

end Mordor.Profile

namespace Mordor.Profile
open Mordor.Crossing
variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Anchor-join dichotomy** (DCC, any number of generators). Let `Ψ u = ⨆ᵢ F cᵢ u`. Either the weak base fails for
some generator, or the `Ψ`-orbit of `⊤` never enters `D` (so its limit `ν Ψ` lies outside `D`): if it first enters at
step `n + 1`, every anchor value at the column `uₙ` is in `D` and below `uₙ`, so all transfer (`no_common_transfer`). -/
theorem anchor_join_dichotomy [WellFoundedLT α] [Nonempty ι] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α) (htop : ¬ ∃ i, ⊤ ≤ p i)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (hweak : ∀ j u, (¬ ∃ i, u ≤ p i) → F (anchor p j) u ≤ u → ¬ F (anchor p j) u ≤ p j) :
    ∀ n, ¬ ∃ i, (fun u => Finset.univ.sup fun k => F (anchor p k) u)^[n] ⊤ ≤ p i := by
  set Ψ : α → α := fun u => Finset.univ.sup fun k => F (anchor p k) u with hΨ
  have hmono : Monotone Ψ := fun _ _ h => Finset.sup_mono_fun fun k _ => hF _ _ _ _ le_rfl h
  have hanti := Monotone.antitone_iterate_of_map_le hmono (le_top : Ψ ⊤ ≤ ⊤)
  intro n
  induction n with
  | zero => simpa using htop
  | succ n ih =>
    intro hin
    set u := Ψ^[n] ⊤
    have hstep : Ψ^[n + 1] ⊤ = Ψ u := Function.iterate_succ_apply' Ψ n ⊤
    have hle : ∀ k, F (anchor p k) u ≤ Ψ u := fun k => Finset.le_sup (f := fun k => F (anchor p k) u) (Finset.mem_univ k)
    have hΨu : Ψ u ≤ u := by rw [← hstep]; exact hanti (Nat.le_succ n)
    obtain ⟨i, hi⟩ := hin
    rw [hstep] at hi
    refine no_common_transfer hF p nw fun k => ⟨ih, ?_⟩
    have hkD : F (anchor p k) u ≤ p i := (hle k).trans hi
    by_cases hki : i = k
    · exact absurd (hki ▸ hkD) (hweak k u ih ((hle k).trans hΨu))
    · exact ⟨i, hki, hkD⟩

end Mordor.Profile
