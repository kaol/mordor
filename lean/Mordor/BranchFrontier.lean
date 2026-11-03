import Mordor.ResponseFrontier

/-!
# Branch-complete frontier splits (round 26, §34.3z⁹⁵)

Response to the brief "branch-complete frontiers and certificate extraction". At a frontier pair (`a = y ⊓ z ∈ D`,
`b = x ⊔ z ∉ D`, `z = F x y`):

* `frontier_split_A`: if `z ∈ D`, both `(x, b)` and `(z, b)` are cross pairs, `x ∥ z`, and `x ⊔ z = b ∉ D` (join split).
* `frontier_split_B`: if `z ∉ D`, both `(a, y)` and `(a, z)` are cross pairs, `y ∥ z`, and `y ⊓ z = a ∈ D` (meet split).
* `branch_children_cross`: in either case each child has its row below its column.
* `branch_provenance`: the children carry the parent row `x` (A) resp. the parent column `y` (B) unchanged, so the
  source coordinate survives one split on one side; the other child replaces it by the response `z`.
* The conjectural branch-alignment lemma is **not** stated as a theorem: for one generator the anchor is `⊥` and no
  transfer exists, so the lemma would say "no infinite branch", i.e. Cut for `↓p` restricted to the tree. Finite
  trees cannot test it; z3 shows depth-2 trees with no anchor transfer at any named column (§34.3z⁹⁵).
-/

namespace Mordor.Profile

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] {F : α → α → α} {InD : α → Prop}
  (hdown : ∀ x y, x ≤ y → InD y → InD x)
  (nw : ∀ x, InD x → ∀ y, ¬ InD y → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include nw in
theorem frontier_split_A {x y : α} (hx : InD x) (hy : ¬ InD y) (hb : ¬ InD (x ⊔ F x y)) (hz : InD (F x y)) :
    (InD x ∧ ¬ InD (x ⊔ F x y)) ∧ (InD (F x y) ∧ ¬ InD (x ⊔ F x y)) ∧ ¬ F x y ≤ x ∧ ¬ x ≤ F x y :=
  ⟨⟨hx, hb⟩, ⟨hz, hb⟩, response_degenerate_join nw hx hy hb hz⟩

include nw in
theorem frontier_split_B {x y : α} (hx : InD x) (hy : ¬ InD y) (ha : InD (y ⊓ F x y)) (hz : ¬ InD (F x y)) :
    (InD (y ⊓ F x y) ∧ ¬ InD y) ∧ (InD (y ⊓ F x y) ∧ ¬ InD (F x y)) ∧ ¬ y ≤ F x y ∧ ¬ F x y ≤ y :=
  ⟨⟨ha, hy⟩, ⟨ha, hz⟩, response_degenerate_meet nw hx hy ha hz⟩

/-- Each child has its row below its column. -/
theorem branch_children_cross (x y : α) :
    (x ≤ x ⊔ F x y ∧ F x y ≤ x ⊔ F x y) ∧ (y ⊓ F x y ≤ y ∧ y ⊓ F x y ≤ F x y) :=
  ⟨⟨le_sup_left, le_sup_right⟩, ⟨inf_le_left, inf_le_right⟩⟩

/-- **Provenance.** One child keeps the parent row (A) resp. the parent column (B); the other uses the response. -/
theorem branch_provenance (x y : α) :
    ((x, x ⊔ F x y).1 = x ∧ (F x y, x ⊔ F x y).1 = F x y) ∧
    ((y ⊓ F x y, y).2 = y ∧ (y ⊓ F x y, F x y).2 = F x y) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end Mordor.Profile
