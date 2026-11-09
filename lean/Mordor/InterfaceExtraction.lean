import Mordor.InterfaceTrace

/-!
# Separator cycles force a lower witness (round 26, §34.3z¹⁴⁰)

The line-cycle family (§34.3z¹³⁶) refutes maximal-separator descent on finite lattices: coatoms `cᵢ` above a common
meet `x`, with `F(cᵢ, y) = c_{σ i}` for a fixed-point-free `σ`. `atom_family_block` (§34.3z¹²⁶) shows that this
configuration cannot occur without a *lower witness* at `(x, y)`:

* `cycle_lower_witness`: if `x ≤ cᵢ` for all `i`, `cᵢ ⊓ cⱼ ≤ x` for `i ≠ j`, and every `F(cᵢ, y)` equals some `cⱼ`
  with `j ≠ i`, then `F(x, y) ≤ x` (monotonicity gives `F(x, y) ≤ F(cᵢ, y)`; two successive responses meet below `x`).
* `cycle_impossible`: hence such a cycle is impossible in a witness-free instance with `x ∈ D`, `y ∉ D`.

So the finite counterexamples to maximal-separator descent are blocked, in the witness-free setting, by exactly the
infinite-antichain obstruction; any infinite interface that defeats descent must avoid this shift structure.
-/

namespace Mordor.InterfaceExtraction
open Mordor.InterfaceTrace

variable {α : Type*} [CompleteLattice α]

theorem cycle_lower_witness {ι : Type*} [Nonempty ι] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (c : ι → α) {x y : α}
    (hxc : ∀ i, x ≤ c i) (hmeet : ∀ i j, i ≠ j → c i ⊓ c j ≤ x) (hcyc : ∀ i, ∃ j, j ≠ i ∧ F (c i) y = c j) :
    F x y ≤ x := by
  by_contra hsafe
  exact atom_family_block c (fun i => F (c i) y) hmeet hcyc (fun i => hF _ _ _ _ (hxc i) le_rfl) hsafe
    (Classical.arbitrary ι)

theorem cycle_impossible {ι : Type*} [Nonempty ι] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set α}
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (c : ι → α) {x y : α} (hx : x ∈ D) (hy : y ∉ D)
    (hxc : ∀ i, x ≤ c i) (hmeet : ∀ i j, i ≠ j → c i ⊓ c j ≤ x) (hcyc : ∀ i, ∃ j, j ≠ i ∧ F (c i) y = c j) :
    False :=
  (nw x hx y hy).1 (cycle_lower_witness hF c hxc hmeet hcyc)

end Mordor.InterfaceExtraction
