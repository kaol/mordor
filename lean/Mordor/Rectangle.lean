import Mordor.Skeleton

/-!
# The critical rectangle and boundary capturers (round 26, §34.3z⁵⁹)

For a cut `D`, a row `m ∈ D` (e.g. a meet of maximal elements of `D`), a column `v ∉ D` (a join of minimal elements of
`Dᶜ`) and boundary elements `p`, `u`, the four cells
`z₀₀ = F(m, v)`, `z₁₀ = F(m ⊓ p, v)`, `z₀₁ = F(m, v ⊔ u)`, `z₁₁ = F(m ⊓ p, v ⊔ u)`.

* `rect_mono`: `z₁₀ ≤ z₀₀ ≤ z₀₁` and `z₁₀ ≤ z₁₁ ≤ z₀₁` (and `z₀₀`, `z₁₁` are not compared).
* `rect_cross`, `rect_nowit`: all four cells are cross cells, and no-witness gives **both** `z ≰ row` and
  `col ≰ z` at each of them, whatever side `z` is on.
* `rect_side`: the side pattern is antitone along the rectangle order: `z₀₁ ∈ D` forces all four into `D`, and
  `z₁₀ ∉ D` forces all four out.
* `fresh_capturer`, `capturer_exists`, `capturer_exists_dual`, `max_incomparable`, `min_incomparable`: an uncaptured
  `D`-value has a maximal capturer (ACC), necessarily new; dually under DCC; distinct maximal (minimal) boundary
  elements are incomparable.
-/

namespace Mordor.Rectangle
open Skeleton

section
variable {L : Type*} [Lattice L] {F : L → L → L}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
include hF

theorem rect_mono (m p v u : L) :
    F (m ⊓ p) v ≤ F m v ∧ F m v ≤ F m (v ⊔ u) ∧ F (m ⊓ p) v ≤ F (m ⊓ p) (v ⊔ u) ∧
      F (m ⊓ p) (v ⊔ u) ≤ F m (v ⊔ u) :=
  ⟨hF _ _ _ _ inf_le_left le_rfl, hF _ _ _ _ le_rfl le_sup_left, hF _ _ _ _ le_rfl le_sup_left,
    hF _ _ _ _ inf_le_left le_rfl⟩

/-- The side pattern is antitone: `z₀₁ ∈ D` puts every cell in `D`; `z₁₀ ∉ D` puts every cell outside. -/
theorem rect_side {D : Set L} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (m p v u : L) :
    (F m (v ⊔ u) ∈ D → F (m ⊓ p) v ∈ D ∧ F m v ∈ D ∧ F (m ⊓ p) (v ⊔ u) ∈ D) ∧
    (F (m ⊓ p) v ∉ D → F m v ∉ D ∧ F (m ⊓ p) (v ⊔ u) ∉ D ∧ F m (v ⊔ u) ∉ D) := by
  obtain ⟨h1, h2, h3, h4⟩ := rect_mono hF m p v u
  refine ⟨fun h => ⟨hD _ _ (h1.trans h2) h, hD _ _ h2 h, hD _ _ h4 h⟩, fun h => ⟨?_, ?_, ?_⟩⟩
  · exact fun h' => h (hD _ _ h1 h')
  · exact fun h' => h (hD _ _ h3 h')
  · exact fun h' => h (hD _ _ (h1.trans h2) h')

end

section
variable {L : Type*} [Lattice L] {F : L → L → L} {D : Set L}

theorem rect_cross (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) {m v : L} (hm : m ∈ D) (hv : v ∉ D) (p u : L) :
    m ⊓ p ∈ D ∧ v ⊔ u ∉ D :=
  ⟨hD _ _ inf_le_left hm, fun h => hv (hD _ _ le_sup_left h)⟩

/-- No-witness at the four cells: each value is neither below its row nor above its column. -/
theorem rect_nowit (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (h : NoWit F D) {m v : L} (hm : m ∈ D) (hv : v ∉ D)
    (p u : L) :
    (¬ F m v ≤ m ∧ ¬ v ≤ F m v) ∧ (¬ F (m ⊓ p) v ≤ m ⊓ p ∧ ¬ v ≤ F (m ⊓ p) v) ∧
    (¬ F m (v ⊔ u) ≤ m ∧ ¬ v ⊔ u ≤ F m (v ⊔ u)) ∧
    (¬ F (m ⊓ p) (v ⊔ u) ≤ m ⊓ p ∧ ¬ v ⊔ u ≤ F (m ⊓ p) (v ⊔ u)) := by
  obtain ⟨hmp, hvu⟩ := rect_cross hD hm hv p u
  exact ⟨h m hm v hv, h _ hmp v hv, h m hm _ hvu, h _ hmp _ hvu⟩

end

section Capture
variable {L : Type*} [CompleteLattice L] {D : Set L}

/-- A capturer chosen above a value that no selected generator captures is not a selected generator. -/
theorem fresh_capturer {Sel : Set L} {z p : L} (hz : ∀ q ∈ Sel, ¬ z ≤ q) (hzp : z ≤ p) : p ∉ Sel :=
  fun hp => hz p hp hzp

/-- Under ACC every element of a down-set lies below a maximal element of it. -/
theorem capturer_exists [WellFoundedGT L] {z : L} (hz : z ∈ D) :
    ∃ p, p ∈ D ∧ (∀ q ∈ D, ¬ p < q) ∧ z ≤ p := by
  obtain ⟨p, ⟨hpD, hzp⟩, hmax⟩ := (wellFounded_gt (α := L)).has_min {p | p ∈ D ∧ z ≤ p} ⟨z, hz, le_rfl⟩
  exact ⟨p, hpD, fun q hq hpq => hmax q ⟨hq, hzp.trans hpq.le⟩ hpq, hzp⟩

/-- Under DCC every element outside a down-set lies above a minimal element outside it. -/
theorem capturer_exists_dual [WellFoundedLT L] {z : L} (hz : z ∉ D) :
    ∃ u, u ∉ D ∧ (∀ v, v ∉ D → ¬ v < u) ∧ u ≤ z := by
  obtain ⟨u, ⟨huD, huz⟩, hmin⟩ := (wellFounded_lt (α := L)).has_min {u | u ∉ D ∧ u ≤ z} ⟨z, hz, le_rfl⟩
  exact ⟨u, huD, fun v hv hvu => hmin v ⟨hv, hvu.le.trans huz⟩ hvu, huz⟩

theorem max_incomparable {p q : L} (hq : q ∈ D) (hp : ∀ r ∈ D, ¬ p < r) (hpq : p ≤ q) : p = q :=
  by_contra fun h => hp q hq (lt_of_le_of_ne hpq h)

theorem min_incomparable {u v : L} (hv : v ∉ D) (hu : ∀ w, w ∉ D → ¬ w < u) (hvu : v ≤ u) : v = u :=
  by_contra fun h => hu v hv (lt_of_le_of_ne hvu h)

end Capture

section Exchange
variable {L : Type*} [Lattice L] {F : L → L → L} {D : Set L}

/-- **The surviving exchange property.** If `p` captures `z₀₀ = F(m, v)` and `q` captures `z₁₁ = F(m ⊓ p, v ⊔ u)`,
then `p ⊓ q ≰ m`: both lie above `z₁₀ = F(m ⊓ p, v)`, which is not below its row `m ⊓ p`. So successive capturers
cannot meet below the base meet, and in particular `p ⊓ q ≠ ⊥`. -/
theorem capturer_meet_escapes (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (h : NoWit F D) {m v p q : L} (u : L) (hm : m ∈ D) (hv : v ∉ D)
    (hp : F m v ≤ p) (hq : F (m ⊓ p) (v ⊔ u) ≤ q) : ¬ p ⊓ q ≤ m := by
  intro hpq
  obtain ⟨h1, -, h3, -⟩ := rect_mono hF m p v u
  have hz : F (m ⊓ p) v ≤ p ⊓ q := le_inf (h1.trans hp) (h3.trans hq)
  exact (h _ (hD _ _ inf_le_left hm) v hv).1 (le_inf (hz.trans hpq) (hz.trans inf_le_left))

/-- **Dual.** If `u` captures `z₀₁ = F(m, v ⊔ u)` from below and `w ≤ z₁₁ = F(m ⊓ p, v ⊔ u)`, then `v ≰ u ⊔ w`. -/
theorem capturer_join_escapes (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (h : NoWit F D) {m v u w : L} (p : L) (hm : m ∈ D) (hv : v ∉ D)
    (hu : u ≤ F m (v ⊔ u)) (hw : w ≤ F (m ⊓ p) (v ⊔ u)) : ¬ v ≤ u ⊔ w := by
  intro hvw
  obtain ⟨-, -, -, h4⟩ := rect_mono hF m p v u
  have hz : u ⊔ w ≤ F m (v ⊔ u) := sup_le hu (hw.trans h4)
  have hvu : v ⊔ u ∉ D := fun h' => hv (hD _ _ le_sup_left h')
  exact (h m hm _ hvu).2 (sup_le (hvw.trans hz) (le_sup_left.trans hz))

end Exchange
end Mordor.Rectangle
