import Mordor.RelayDescent

/-!
# Terminal relays on the centre's orbit: predecessor inequalities (round 26, §34.3z¹⁴⁸)

ChatGPT brief "Terminal relay orbit theorem and the multi-row sandwich" (effective HEAD b266a38).

The bottom orbit `c₀ = ⊤`, `c_{j+1} = F ⊥ c_j` descends (`bot_orbit_anti`). If `u = F ⊥ c` with `c` the predecessor
(`u ≤ c`), then for every row `r`: `u ≤ F r c ≤ F r ⊤` (`pred_row_bounds`), and for the block row `a`:
`F a u ≤ F a c`, so `u ⊔ F a u ≤ F a c ≤ F a ⊤` (`pred_join_bound`). These are the brief's predecessor inequalities;
the K ≥ 2 contradiction itself is not proved (see the log).
-/

namespace Mordor.Relay
open Mordor

set_option linter.unusedSectionVars false

variable {β : Type*} [Lattice β] [BoundedOrder β] {F : β → β → β}

/-- The orbit of `⊤` under any monotone map descends. -/
theorem orbit_anti {g : β → β} (hg : Monotone g) : ∀ k, g^[k + 1] ⊤ ≤ g^[k] ⊤
  | 0 => le_top
  | k + 1 =>
      calc g^[k + 1 + 1] ⊤ = g (g^[k + 1] ⊤) := Function.iterate_succ_apply' g (k + 1) ⊤
        _ ≤ g (g^[k] ⊤) := hg (orbit_anti hg k)
        _ = g^[k + 1] ⊤ := (Function.iterate_succ_apply' g k ⊤).symm

theorem bot_orbit_anti (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (k : ℕ) :
    (F ⊥)^[k + 1] ⊤ ≤ (F ⊥)^[k] ⊤ :=
  orbit_anti (fun _ _ h => hF _ _ _ _ le_rfl h) k

/-- **Predecessor row bounds.** -/
theorem pred_row_bounds (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (r c : β) :
    F ⊥ c ≤ F r c ∧ F r c ≤ F r ⊤ :=
  ⟨hF _ _ _ _ bot_le le_rfl, hF _ _ _ _ le_rfl le_top⟩

/-- **The join bound.** With `u = F ⊥ c ≤ c`: `u ⊔ F a u ≤ F a c ≤ F a ⊤`. -/
theorem pred_join_bound (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (a c : β) (huc : F ⊥ c ≤ c) :
    F ⊥ c ⊔ F a (F ⊥ c) ≤ F a c ∧ F a c ≤ F a ⊤ :=
  ⟨sup_le (pred_row_bounds hF a c).1 (hF _ _ _ _ le_rfl huc), (pred_row_bounds hF a c).2⟩

/-- On the bottom orbit: `u = c_{K+1}` and `c = c_K`. -/
theorem orbit_join_bound (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (a : β) (K : ℕ) :
    (F ⊥)^[K + 1] ⊤ ⊔ F a ((F ⊥)^[K + 1] ⊤) ≤ F a ((F ⊥)^[K] ⊤) ∧ F a ((F ⊥)^[K] ⊤) ≤ F a ⊤ := by
  have h := pred_join_bound hF a ((F ⊥)^[K] ⊤) (by
    have := bot_orbit_anti hF K; rwa [Function.iterate_succ_apply'] at this)
  rwa [Function.iterate_succ_apply']

end Mordor.Relay
