import Mordor.TerminalRelayOrbit
import Mordor.CutHeight5

/-!
# Clipped and lifted interval cuts at edge-height six (round 26, §34.3z¹⁵⁰)

ChatGPT brief "The relative Cut theorem below a terminal join" (HEAD 0f83f88). Trust: `Ground.cut_height5`
(`bv_decide`: `Lean.ofReduceBool`, `Lean.trustCompiler`, as documented in §34.3g).

In a bounded lattice of edge-height `≤ 6` (`NoChain β 7`) with a witness-free proper cut `D`:

* `clipped_escape`: for **every** `c ∉ D`, `c < ⊤`, some `x ∈ D`, `y ∉ D` below `c` have `F x y ⊓ c ≤ x` and
  `F x y ≰ c` (height-five Cut on `↓c` for `F ⊓ c`; the upper alternative would be a global cell).
* `lifted_escape`: for **every** `p ∈ D`, `p ≠ ⊥`, some `x ∈ D`, `y ∉ D` above `p` have `y ≤ F x y ⊔ p` and
  `y ≰ F x y` (height-five Cut on `↑p` for `F ⊔ p`). These generalize `BottomMaxCell.dual_near_cell` and
  `near_cell_of_atomic_over` from atomic intervals to all intervals.
* `top_escape`: if `c` is maximal among the proper non-members, every clipped escape at `c` has `c ⊔ F x y = ⊤`.
* `terminal_join_lt_top`: on the bottom orbit, `u ⊔ F a u < ⊤` for `u = F ⊥ c`, `c ∉ D`, `a ∈ D` (otherwise
  `(a, c)` is an upper cell).

None of these uses a relay: escapes exist below every proper non-member of a witness-free cut. Hence "no escape"
statements are equivalent to Cut for the cut in question, not intermediate lemmas (see the log).
-/

namespace Mordor.Clipped
open Mordor Mordor.Ground

set_option linter.unusedSectionVars false

variable {β : Type*} [Lattice β] [BoundedOrder β]

theorem chainTo_val_Iic {t : β} : ∀ (k : ℕ) (x : Set.Iic t), chainTo x k → chainTo x.1 k
  | 0, _, _ => trivial
  | k + 1, _, ⟨y, hy, hc⟩ => ⟨y.1, Subtype.coe_lt_coe.2 hy, chainTo_val_Iic k y hc⟩

theorem chainTo_val_Ici {p : β} (hp : ⊥ < p) : ∀ (k : ℕ) (x : Set.Ici p), chainTo x k → chainTo x.1 (k + 1)
  | 0, x, _ => ⟨⊥, lt_of_lt_of_le hp x.2, trivial⟩
  | k + 1, _, ⟨y, hy, hc⟩ => ⟨y.1, Subtype.coe_lt_coe.2 hy, chainTo_val_Ici hp k y hc⟩

theorem noChain_Iic {t : β} (ht : t < ⊤) (hn : NoChain β 7) : NoChain (Set.Iic t) 6 := fun x hx =>
  hn ⊤ ⟨x.1, lt_of_le_of_lt x.2 ht, chainTo_val_Iic 6 x hx⟩

theorem noChain_Ici {p : β} (hp : ⊥ < p) (hn : NoChain β 7) : NoChain (Set.Ici p) 6 := fun x hx =>
  hn x.1 (chainTo_val_Ici hp 6 x hx)

variable {F : β → β → β} {D : Set β}

/-- **Clipped escape.** -/
theorem clipped_escape (hn : NoChain β 7) (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ ⦃x y⦄, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D)
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {c : β} (hc : c ∉ D) (hct : c < ⊤) :
    ∃ x ∈ D, ∃ y ∉ D, x ≤ c ∧ y ≤ c ∧ F x y ⊓ c ≤ x ∧ ¬ F x y ≤ c := by
  let G : Set.Iic c → Set.Iic c → Set.Iic c := fun x y => ⟨F x.1 y.1 ⊓ c, inf_le_right⟩
  have hG : ∀ x x' y y' : Set.Iic c, x ≤ x' → y ≤ y' → G x y ≤ G x' y' := fun x x' y y' hx hy =>
    show F x.1 y.1 ⊓ c ≤ F x'.1 y'.1 ⊓ c from inf_le_inf_right c (hF _ _ _ _ hx hy)
  obtain ⟨x, hx, y, hy, hw⟩ := cut_height5 (noChain_Iic hct hn) G hG {z | z.1 ∈ D}
    (fun x y hxy hyD => hD (show x.1 ≤ y.1 from hxy) hyD) (show (⊥ : β) ∈ D from hbot) (show c ∉ D from hc)
  have hxD : x.1 ∈ D := hx
  have hyD : y.1 ∉ D := hy
  rcases hw with h | h
  · have h' : F x.1 y.1 ⊓ c ≤ x.1 := h
    refine ⟨x.1, hxD, y.1, hyD, x.2, y.2, h', fun hle => (nw _ hxD _ hyD).1 ?_⟩
    calc F x.1 y.1 = F x.1 y.1 ⊓ c := (inf_eq_left.2 hle).symm
      _ ≤ x.1 := h'
  · exact absurd ((show y.1 ≤ F x.1 y.1 ⊓ c from h).trans inf_le_left) (nw _ hxD _ hyD).2

/-- **Lifted escape.** -/
theorem lifted_escape (hn : NoChain β 7) (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ ⦃x y⦄, x ≤ y → y ∈ D → x ∈ D) (htop : ⊤ ∉ D)
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {p : β} (hp : p ∈ D) (hp0 : ⊥ < p) :
    ∃ x ∈ D, ∃ y ∉ D, p ≤ x ∧ p ≤ y ∧ y ≤ F x y ⊔ p ∧ ¬ y ≤ F x y := by
  let G : Set.Ici p → Set.Ici p → Set.Ici p := fun x y => ⟨F x.1 y.1 ⊔ p, le_sup_right⟩
  have hG : ∀ x x' y y' : Set.Ici p, x ≤ x' → y ≤ y' → G x y ≤ G x' y' := fun x x' y y' hx hy =>
    show F x.1 y.1 ⊔ p ≤ F x'.1 y'.1 ⊔ p from sup_le_sup_right (hF _ _ _ _ hx hy) p
  obtain ⟨x, hx, y, hy, hw⟩ := cut_height5 (noChain_Ici hp0 hn) G hG {z | z.1 ∈ D}
    (fun x y hxy hyD => hD (show x.1 ≤ y.1 from hxy) hyD) (show p ∈ D from hp) (show (⊤ : β) ∉ D from htop)
  have hxD : x.1 ∈ D := hx
  have hyD : y.1 ∉ D := hy
  rcases hw with h | h
  · exact absurd (le_sup_left.trans (show F x.1 y.1 ⊔ p ≤ x.1 from h)) (nw _ hxD _ hyD).1
  · exact ⟨x.1, hxD, y.1, hyD, x.2, y.2, h, (nw _ hxD _ hyD).2⟩

/-- **Top escape.** At a maximal proper non-member every clipped escape reaches `⊤`. -/
theorem top_escape (hD : ∀ ⦃x y⦄, x ≤ y → y ∈ D → x ∈ D) {c x y : β} (hc : c ∉ D)
    (hmax : ∀ z, c < z → z ∉ D → z = ⊤) (hesc : ¬ F x y ≤ c) : c ⊔ F x y = ⊤ := by
  have hlt : c < c ⊔ F x y := lt_of_le_of_ne le_sup_left (fun e => hesc (e ▸ le_sup_right))
  exact hmax _ hlt (fun h => hc (hD le_sup_left h))

/-- **The terminal join is proper.** -/
theorem terminal_join_lt_top (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {a c : β} (ha : a ∈ D) (hc : c ∉ D)
    (huc : F ⊥ c ≤ c) : F ⊥ c ⊔ F a (F ⊥ c) < ⊤ := by
  refine lt_top_iff_ne_top.2 fun e => (nw a ha c hc).2 ?_
  have h := (Mordor.Relay.pred_join_bound hF a c huc).1
  rw [e] at h; exact le_top.trans h

end Mordor.Clipped
