import Mordor.SinkCone

/-!
# Mixed row/column frontier induction and the least anchor-contracting hull (round 26, §34.3z⁸⁴)

Response to the brief "find a second cross-column induction".

**Priority A (frontier transitions).** For a cross pair `x ∈ D`, `y ∉ D`: `x⁺ = x ⊔ F x y`, `y⁻ = y ⊓ F x y`.
* `cross_frontier_step`: `x < x⁺`, `y⁻ < y`, `y⁻ ≤ F x y ≤ x⁺` (no witness only).
* `cross_pattern`: `x⁺ ∈ D → y⁻ ∈ D` (three patterns).
* `seed_join_out`: for an antichain of generators and `q ∉ D`, `pⱼ ⊔ q ∉ D`.
* `frontier_pair` (ACC + DCC): the transitions "column down while `y⁻ ∉ D`, row up while `x⁺ ∈ D`" are well founded in
  the product order, so from every cross pair `(x₀, y₀)` one reaches a **frontier pair** `x ≥ x₀`, `y ≤ y₀` with
  `y ⊓ F x y ∈ D` and `x ⊔ F x y ∉ D` (pattern 3). This is the whole content of the mixed induction: pattern 3 is its
  terminal state, and it is not contradictory (the log records a one-generator partial model).

**Priority B (anchor hull).** `Aⱼ = {z | F cⱼ z ≤ z}` is closed under meets and contains `⊤`.
* `anchor_hull` (DCC): the least `λ ≥ v` in `Aⱼ`; `F cⱼ λ ∈ Aⱼ`; for `v ∉ D`, `v ≰ F cⱼ λ`, so `v ⊓ F cⱼ λ < v`.
* `anchor_hull_entry`: the `F cⱼ`-orbit of `λ` enters `D` from a last point `w ≤ λ`, either transferring (then on a
  sink cone `↓w` meets the cone only inside `D`) or self-entering (a weak-base failure at `w`).
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

section Frontier
variable {α : Type*} [Lattice α] {F : α → α → α} {InD : α → Prop}
  (hdown : ∀ x y, x ≤ y → InD y → InD x)
  (nw : ∀ x, InD x → ∀ y, ¬ InD y → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include nw in
theorem cross_frontier_step {x y : α} (hx : InD x) (hy : ¬ InD y) :
    x < x ⊔ F x y ∧ y ⊓ F x y < y ∧ y ⊓ F x y ≤ F x y ∧ F x y ≤ x ⊔ F x y :=
  ⟨lt_of_le_of_ne le_sup_left fun h => (nw x hx y hy).1 (sup_eq_left.1 h.symm),
   lt_of_le_of_ne inf_le_left fun h => (nw x hx y hy).2 (inf_eq_left.1 h), inf_le_right, le_sup_right⟩

include hdown in
theorem cross_pattern {x y : α} (h : InD (x ⊔ F x y)) : InD (y ⊓ F x y) :=
  hdown _ _ (inf_le_right.trans le_sup_right) h

include hdown nw in
/-- **The frontier pair.** -/
theorem frontier_pair [WellFoundedLT α] [WellFoundedGT α] :
    ∀ y₀, ¬ InD y₀ → ∀ x₀, InD x₀ →
      ∃ x y, x₀ ≤ x ∧ y ≤ y₀ ∧ InD x ∧ ¬ InD y ∧ InD (y ⊓ F x y) ∧ ¬ InD (x ⊔ F x y) := by
  intro y₀
  induction y₀ using WellFoundedLT.induction with
  | _ y ihy =>
    intro hy x₀
    induction x₀ using WellFoundedGT.induction with
    | _ x ihx =>
      intro hx
      obtain ⟨hxlt, hylt, -, -⟩ := cross_frontier_step nw hx hy
      by_cases hym : InD (y ⊓ F x y)
      · by_cases hxp : InD (x ⊔ F x y)
        · obtain ⟨x', y', h1, h2, h3⟩ := ihx _ hxlt hxp
          exact ⟨x', y', hxlt.le.trans h1, h2, h3⟩
        · exact ⟨x, y, le_rfl, le_rfl, hx, hy, hym, hxp⟩
      · obtain ⟨x', y', h1, h2, h3⟩ := ihy _ hylt hym x hx
        exact ⟨x', y', h1, h2.trans hylt.le, h3⟩

end Frontier

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For an antichain of generators, `pⱼ ⊔ q` is outside `D` whenever `q` is. -/
theorem seed_join_out (p : ι → α) (hanti : ∀ i k, p i ≤ p k → i = k) {j : ι} {q : α} (hq : ¬ ∃ i, q ≤ p i) :
    ¬ ∃ i, p j ⊔ q ≤ p i := by
  rintro ⟨i, hi⟩
  have hji := hanti j i (le_sup_left.trans hi)
  exact hq ⟨i, le_sup_right.trans hi⟩

variable {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF nw in
/-- **The least anchor-contracting hull.** -/
theorem anchor_hull [WellFoundedLT α] (j : ι) {v : α} (hv : ¬ ∃ i, v ≤ p i) :
    ∃ l, v ≤ l ∧ F (anchor p j) l ≤ l ∧ (∀ z, v ≤ z → F (anchor p j) z ≤ z → l ≤ z) ∧
      F (anchor p j) (F (anchor p j) l) ≤ F (anchor p j) l ∧ ¬ v ≤ F (anchor p j) l ∧
      v ⊓ F (anchor p j) l < v := by
  set h := F (anchor p j)
  have hmono : Monotone h := fun _ _ hh => hF _ _ _ _ le_rfl hh
  obtain ⟨l, ⟨hvl, hl⟩, hmin⟩ := (wellFounded_lt (α := α)).has_min {z | v ≤ z ∧ h z ≤ z} ⟨⊤, le_top, le_top⟩
  have hleast : ∀ z, v ≤ z → h z ≤ z → l ≤ z := fun z hvz hz => by
    have hm : l ⊓ z ∈ {z | v ≤ z ∧ h z ≤ z} :=
      ⟨le_inf hvl hvz, le_inf ((hmono inf_le_left).trans hl) ((hmono inf_le_right).trans hz)⟩
    have : l ⊓ z = l := eq_of_le_of_not_lt inf_le_left (hmin _ hm)
    exact this ▸ inf_le_right
  have hlD : ¬ ∃ i, l ≤ p i := fun ⟨i, hi⟩ => hv ⟨i, hvl.trans hi⟩
  have hnv : ¬ v ≤ h l := fun hvh => by
    have := hleast _ hvh (hmono hl)
    exact (nw _ ⟨j, anchor_le p j⟩ l hlD).2 this
  exact ⟨l, hvl, hl, hleast, hmono hl, hnv, lt_of_le_of_ne inf_le_left fun e => hnv (inf_eq_left.1 e)⟩

include hF nw in
/-- **First entry from an anchor-contracting column**: transfer or self-entry at a last point below it. -/
theorem anchor_hull_entry [WellFoundedLT α] {j : ι} {l : α} (hl : ¬ ∃ i, l ≤ p i)
    (hcl : F (anchor p j) l ≤ l) :
    ∃ w, w ≤ l ∧ (¬ ∃ i, w ≤ p i) ∧ F (anchor p j) w ≤ w ∧
      (Transfer F p j w ∨ F (anchor p j) w ≤ p j) := by
  have hmono : Monotone (F (anchor p j)) := fun _ _ h => hF _ _ _ _ le_rfl h
  obtain ⟨n, hU, k, hk⟩ := FGTwo.orbit_end (InD := fun x => ∃ i, x ≤ p i) hF ⟨j, anchor_le p j⟩ nw l hl hcl
  have hanti := Monotone.antitone_iterate_of_map_le hmono hcl
  have hwc : F (anchor p j) ((F (anchor p j))^[n] l) ≤ (F (anchor p j))^[n] l := by
    rw [← Function.iterate_succ_apply' (F (anchor p j)) n l]; exact hanti (Nat.le_succ n)
  refine ⟨_, hanti (Nat.zero_le n), hU n le_rfl, hwc, ?_⟩
  by_cases hkj : k = j
  · exact Or.inr (hkj ▸ hk)
  · exact Or.inl ⟨hU n le_rfl, k, hkj, hk⟩

end Mordor.Profile
