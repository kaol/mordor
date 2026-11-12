import Mordor.GroundOH
import Mordor.HeightInduction
import Mordor.OHHeight4

/-!
# The rigid orbit-height counterexample of a true orbit (round 26, §34.3z¹⁶⁰)

`top_mem_or_ohCxR`: for a complete lattice of edge-height `≤ H`, given `OHAt` at every smaller height, either
`⊤ ∈ R_H`, or the true orbit `M k := R_k` is a rigid orbit-height counterexample `OHCxR` — the map is rigid
(`top_mem_reduction` handles the other cases) and the lower-height consequences `diag`, `post` hold. Ground
certificates for the rigid theory (`oh_ground.py … rigid ih`, `oh_lean.py`) close the second alternative.
The `post` field is proved from the true orbit (`top_mem_of_good_post`), not from an arbitrary over-approximation.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

variable {β : Type u} [CompleteLattice β]

theorem height_le_of_not_chainTo {H : ℕ} {c : β} {k : ℕ} (h : ¬ chainTo c (k + 1)) : height H c ≤ k := by
  by_contra hk
  exact h (chainTo_mono' (height H c) (k + 1) c (chainTo_height c) (by omega))

theorem top_mem_or_ohCxR {H : ℕ} (IH : ∀ H' < H, OHAt.{u} H') (hn : NoChain β (H + 1)) (G : β →o β →o β) :
    (⊤ : β) ∈ Rk G H ∨ OHCxR (fun x y => G x y) (fun k => Rk G k) H := by
  by_cases htop : (⊤ : β) ∈ Rk G H
  · exact Or.inl htop
  right
  have ha : a G ⊥ = ⊥ := by by_contra h; exact htop (top_mem_of_a_bot IH hn h)
  have hb : b G ⊤ = ⊤ := by by_contra h; exact htop (top_mem_of_b_top IH hn h)
  have hd : ∀ c, G c c = c → c = ⊥ ∨ c = ⊤ := fun c hc => by
    by_contra h; push_neg at h; exact htop (top_mem_of_diag_fixed IH hn hc h.1 h.2)
  exact
    { mono := fun x x' y y' hx hy => (G.mono hx y).trans ((G x').mono hy)
      base := fun t h => (show t ∈ Set.Iic (⊥ : β) from h)
      incr := fun k t h => Rk_mono (Nat.le_succ k) h
      down := fun k s t hst h => Rk_down k hst h
      brule := fun k x y hx h => mem_succ_of_cell hx le_rfl (Or.inl h)
      arule := fun k x y hx h => mem_succ_of_cell hx le_rfl (Or.inr h)
      top := htop
      rigA := fun y h => ha ▸ le_a h
      rigB := fun x h => hb ▸ b_le h
      rigD := fun c h1 h2 => by
        rcases hd c (le_antisymm h1 h2) with e | e
        · exact Or.inl e.le
        · exact Or.inr e.ge
      diag := fun k c h1 h2 h3 =>
        Rk_mono (height_le_of_not_chainTo h3) (diagGood_of_lower IH hn h1 (fun e => h2 (e ▸ le_rfl)))
      post := fun j c h1 h2 h3 h4 => by
        have hjH : j ≤ H := by
          by_contra hj; exact hn c (chainTo_mono' j (H + 1) c h4 (by omega))
        exact top_mem_of_good_post IH hn h1 (fun e => h2 (e ▸ le_rfl)) h3 (le_height hjH h4) }

/-- The lower heights `< 5`, all proved (`≤ 3` by ordinary proofs, `4` by the certificate `ohAt_4'`). -/
theorem ohAt_lt_five : ∀ H' < 5, OHAt.{u} H' := fun H' h => by
  rcases Nat.lt_or_ge H' 4 with h4 | h4
  · exact ohAt_of_riseAt fun H'' hH'' => riseAt_le_three (by omega)
  · rw [show H' = 4 by omega]; exact ohAt_4'

end Mordor.OrbitHeight
