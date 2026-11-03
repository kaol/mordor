import Mordor.CrossCellInduction

/-!
# Response re-entry at a frontier pair (round 26, §34.3z⁹⁴)

Response to the brief "response re-entry and nested frontiers". A *frontier pair* (`frontier_pair`): `x ∈ D`,
`y ∉ D`, `z = F x y`, `a = y ⊓ z ∈ D`, `b = x ⊔ z ∉ D`.

* `response_reentry`: case A (`z ∈ D`) gives the cross pair `(z, b)`, case B (`z ∉ D`) gives `(a, z)`; both are
  comparable cross pairs (row ≤ column).
* `response_interval_nested`: the new **pair interval** (`[z, b]` resp. `[a, z]`) lies inside the response interval
  `[a, b]`.
* `response_interval_strict`: it is strictly inside iff `a ≠ z` (case A) resp. `z ≠ b` (case B); i.e. the degenerate
  cases are `z ≤ y` (A) and `x ≤ z` (B).
* `response_degenerate_join`: in degenerate case A, `x, z ∈ D` are incomparable with `x ⊔ z ∉ D` (so `D` is not
  join-closed: impossible for one generator, `principal_join_closed`).
* `response_degenerate_meet`: in degenerate case B, `y, z ∉ D` are incomparable with `y ⊓ z ∈ D`.
* The brief's progress lemma compares *response* intervals across a terminalization; nothing above relates the next
  response interval `[y' ⊓ F x' y', x' ⊔ F x' y']` to `[a, b]` (terminalization moves the row up and the column down
  freely). This is tested, not proved (§34.3z⁹⁴).
-/

namespace Mordor.Profile

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] {F : α → α → α} {InD : α → Prop}
  (hdown : ∀ x y, x ≤ y → InD y → InD x)
  (nw : ∀ x, InD x → ∀ y, ¬ InD y → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

/-- **Response re-entry.** -/
theorem response_reentry {x y : α} (ha : InD (y ⊓ F x y)) (hb : ¬ InD (x ⊔ F x y)) :
    (InD (F x y) → InD (F x y) ∧ ¬ InD (x ⊔ F x y) ∧ F x y ≤ x ⊔ F x y) ∧
    (¬ InD (F x y) → InD (y ⊓ F x y) ∧ ¬ InD (F x y) ∧ y ⊓ F x y ≤ F x y) :=
  ⟨fun hz => ⟨hz, hb, le_sup_right⟩, fun hz => ⟨ha, hz, inf_le_right⟩⟩

/-- **The new pair interval lies in the response interval.** -/
theorem response_interval_nested (x y : α) :
    (y ⊓ F x y ≤ F x y ∧ x ⊔ F x y ≤ x ⊔ F x y) ∧ (y ⊓ F x y ≤ y ⊓ F x y ∧ F x y ≤ x ⊔ F x y) :=
  ⟨⟨inf_le_right, le_rfl⟩, ⟨le_rfl, le_sup_right⟩⟩

/-- **Strictness**: the degenerate cases are exactly `z ≤ y` (case A) and `x ≤ z` (case B). -/
theorem response_interval_strict (x y : α) :
    (y ⊓ F x y = F x y ↔ F x y ≤ y) ∧ (x ⊔ F x y = F x y ↔ x ≤ F x y) :=
  ⟨inf_eq_right, sup_eq_right⟩

include nw in
/-- **Degenerate join escape.** -/
theorem response_degenerate_join {x y : α} (hx : InD x) (hy : ¬ InD y) (hb : ¬ InD (x ⊔ F x y))
    (hz : InD (F x y)) : ¬ F x y ≤ x ∧ ¬ x ≤ F x y :=
  ⟨(nw x hx y hy).1, fun h => hb (by rw [sup_eq_right.2 h]; exact hz)⟩

include nw in
/-- **Degenerate meet capture.** -/
theorem response_degenerate_meet {x y : α} (hx : InD x) (hy : ¬ InD y) (ha : InD (y ⊓ F x y))
    (hz : ¬ InD (F x y)) : ¬ y ≤ F x y ∧ ¬ F x y ≤ y :=
  ⟨(nw x hx y hy).2, fun h => hz (by rw [inf_eq_right.2 h] at ha; exact ha)⟩

/-- For a principal cut `D = ↓p` the degenerate join case cannot occur: `↓p` is join-closed. -/
theorem principal_join_closed {p x z : α} (hx : x ≤ p) (hz : z ≤ p) : x ⊔ z ≤ p := sup_le hx hz

end Mordor.Profile
