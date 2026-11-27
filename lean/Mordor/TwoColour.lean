import Mordor.PairTrap

/-!
# Two colours: the colour shadow and the colour trap (§34.3z²⁹⁷, brief run 20)

Setting: W0, no μ-fixed atom of `R_1` (the `hno` of `colourGain`), and exactly two colour atoms `ca ≠ cb`
(atoms of `Z` that are values of row `⊥`) with no element of `Z` above both.

* `desc_ge_of_postfixed`: if `c` lies below every element `(F x)^[j+1] ⊤` (`j < i`) and `Q ≤ F(x, Q) ⊔ c`, then `Q`
  lies below `(F x)^[j] ⊤` for every `j ≤ i`.
* `desc_ge_of_phi_last`: if `c ≤ F(⊥, (F x)^[k] ⊤)`, then `c ≤ (F x)^[j+1] ⊤` for every `j ≤ k`.
* `twoColour_gain`: `cb ≤ λ(ca)` (ColourGain).
* `twoColour_shadow`: `cb ≤ F(⊥, r)` for the last high element `r` of row `ca`.
* `twoColour_not_above`: `¬ ca ≤ λ(ca)`.
* `twoColour_noTrap`: no `Q ≥ ca` has `Q ≤ F(ca, Q) ⊔ cb`.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} [CompleteLattice α] {F : α →o α →o α}

theorem desc_ge_of_postfixed {x c Q : α} {i : ℕ}
    (hc : ∀ j, j < i → c ≤ (F x)^[j+1] (⊤ : α)) (hQ : Q ≤ F x Q ⊔ c) :
    ∀ j, j ≤ i → Q ≤ (F x)^[j] (⊤ : α) := by
  intro j
  induction j with
  | zero => intro _; exact le_top
  | succ j ih =>
    intro hj
    have h1 := ih (by omega)
    have h2 : F x Q ≤ (F x)^[j+1] (⊤ : α) := by
      rw [Function.iterate_succ_apply']; exact (F x).mono h1
    exact hQ.trans (sup_le h2 (hc j (by omega)))

theorem desc_ge_of_phi_last {x c : α} {k : ℕ} (hc : c ≤ F ⊥ ((F x)^[k] (⊤ : α))) :
    ∀ j, j ≤ k → c ≤ (F x)^[j+1] (⊤ : α) := by
  intro j hj
  rw [Function.iterate_succ_apply']
  have hanti : (F x)^[k] (⊤ : α) ≤ (F x)^[j] (⊤ : α) :=
    iter_antitone_of_le (F x).monotone (le_top : F x ⊤ ≤ ⊤) hj
  exact hc.trans (((F ⊥).mono hanti).trans ((F.mono bot_le) _))

/-- ColourGain with two colours: the landing of row `ca` carries `cb`. -/
theorem twoColour_gain {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    (hno : ¬ ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q)
    {ca cb : α} (hA2 : ∀ w, height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → F ⊥ w = ca ∨ F ⊥ w = cb)
    {i : ℕ} (hi : height H ((F ca)^[i] (⊤ : α)) ≤ 2) (hmin : ∀ j < i, 2 < height H ((F ca)^[j] (⊤ : α))) :
    cb ≤ (F ca)^[i] (⊤ : α) := by
  obtain ⟨w, hw1, hw0, hwp, hwx⟩ := colourGain hn ha hk2 htop hno hi hmin
  rcases hA2 w hw1 hw0 with e | e
  · exact absurd (le_of_eq e) hwx
  · exact e ▸ hwp

/-- **Colour shadow.** The last high element `r` of row `ca` has `cb ≤ F(⊥, r)`. -/
theorem twoColour_shadow {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    (hno : ¬ ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q)
    {ca cb : α} (hca1 : height H ca = 1) (hca0 : F ⊥ ca = ⊥)
    (hA2 : ∀ w, height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → F ⊥ w = ca ∨ F ⊥ w = cb)
    (hU : ∀ z, F ⊥ z = ⊥ → ca ≤ z → cb ≤ z → False)
    {k : ℕ} (hi : height H ((F ca)^[k+1] (⊤ : α)) ≤ 2)
    (hmin : ∀ j < k + 1, 2 < height H ((F ca)^[j] (⊤ : α))) :
    cb ≤ F ⊥ ((F ca)^[k] (⊤ : α)) := by
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hk2 z (hR12 ((mem_one_iff ha).2 hz))
  have hpos : ∀ {z : α}, z ≠ ⊥ → 1 ≤ height H z := fun hz => by
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hz); rw [height_bot_eq_zero] at this; omega
  have hR : ca ∈ Rk F 1 := (mem_one_iff ha).2 hca0
  set p := (F ca)^[k+1] (⊤ : α) with hpdef
  set r := (F ca)^[k] (⊤ : α) with hrdef
  have hpr : p = F ca r := by rw [hpdef, hrdef, Function.iterate_succ_apply']
  have hple : p ≤ r := by
    have := iter_antitone_of_le (F ca).monotone (le_top : F ca ⊤ ≤ ⊤) (Nat.le_succ k)
    rw [hpdef, hrdef]; exact this
  have hsp : F ⊥ r ≤ p := hpr ▸ (F.mono bot_le) r
  have hrh : 2 < height H r := hmin k (by omega)
  have hs0 : F ⊥ r ≠ ⊥ := fun h => by have := hZT r h; omega
  have hbp : cb ≤ p := twoColour_gain hn ha hk2 htop hno hA2 hi hmin
  by_cases hpZ : F ⊥ p = ⊥
  · have hsZ : F ⊥ (F ⊥ r) = ⊥ := le_bot_iff.1 (((F ⊥).mono hsp).trans (le_of_eq hpZ))
    have hs2 : height H (F ⊥ r) ≤ 2 := le_trans ((height_strictMono hn).monotone hsp) hi
    rcases (show height H (F ⊥ r) = 1 ∨ height H (F ⊥ r) = 2 by have := hpos hs0; omega) with h1 | h2
    · rcases hA2 r h1 hsZ with e | e
      · exact (hU p hpZ (e ▸ hsp) hbp).elim
      · exact le_of_eq e.symm
    · have e : F ⊥ r = p := eq_of_le_of_height_ge hn hsp (by omega)
      exact e ▸ hbp
  · obtain ⟨hp2, hc1, hc0⟩ := exit_atom hn hk2 ha hR htop hi hmin hpZ
    rcases hA2 p hc1 hc0 with e | e
    · exfalso
      obtain ⟨k', hk', hmin', hfix⟩ :=
        exitFixed_of_dom hn hk2 (rfl : (F ca)^[k+1] (⊤ : α) = p) hp2 hca1 hR (le_refl ca) e
      exact hno ⟨ca, hR, hca1, k', by rw [hk']; omega, hmin', hfix⟩
    · exact e ▸ ((F ⊥).mono hple)

/-- **Colour trap.** Row `ca` does not land above `ca`. -/
theorem twoColour_not_above {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    (hno : ¬ ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q)
    {ca cb : α} (hca1 : height H ca = 1) (hca0 : F ⊥ ca = ⊥) (hcb1 : height H cb = 1) (hcb0 : F ⊥ cb = ⊥)
    (hab : ca ≠ cb)
    (hA2 : ∀ w, height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → F ⊥ w = ca ∨ F ⊥ w = cb)
    (hU : ∀ z, F ⊥ z = ⊥ → ca ≤ z → cb ≤ z → False)
    {i : ℕ} (hi : height H ((F ca)^[i] (⊤ : α)) ≤ 2) (hmin : ∀ j < i, 2 < height H ((F ca)^[j] (⊤ : α))) :
    ¬ ca ≤ (F ca)^[i] (⊤ : α) := by
  intro hle
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hRa : ca ∈ Rk F 1 := (mem_one_iff ha).2 hca0
  have hRb : cb ∈ Rk F 1 := (mem_one_iff ha).2 hcb0
  set p := (F ca)^[i] (⊤ : α) with hpdef
  have hbp : cb ≤ p := twoColour_gain hn ha hk2 htop hno hA2 hi hmin
  by_cases hpZ : F ⊥ p = ⊥
  · exact hU p hpZ hle hbp
  obtain ⟨hp2, hc1, hc0⟩ := exit_atom hn hk2 ha hRa htop hi hmin hpZ
  -- the exit atom of row `ca` is `cb` (it is not `ca`: no fixed atom)
  have hφp : F ⊥ p = cb := by
    rcases hA2 p hc1 hc0 with e | e
    · exfalso
      obtain ⟨k', hk', hmin', hfix⟩ :=
        exitFixed_of_dom hn hk2 (rfl : (F ca)^[i] (⊤ : α) = p) hp2 hca1 hRa (le_refl ca) e
      exact hno ⟨ca, hRa, hca1, k', by rw [hk']; omega, hmin', hfix⟩
    · exact e
  -- `p = ca ⊔ cb`
  have hjp : ca ⊔ cb ≤ p := sup_le hle hbp
  have hlt : ca < ca ⊔ cb := by
    refine lt_of_le_of_ne le_sup_left (fun e => hab ?_)
    have hba : cb ≤ ca := e ▸ le_sup_right
    have hb0 : cb ≠ ⊥ := fun h => by rw [h, height_bot_eq_zero] at hcb1; omega
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hb0)
    exact (eq_of_le_of_height_ge hn hba (by omega)).symm
  have hj2 : 2 ≤ height H (ca ⊔ cb) := by have := height_strictMono hn hlt; omega
  have hPeq : ca ⊔ cb = p := eq_of_le_of_height_ge hn hjp (by omega)
  -- row `cb` lands; its descent stays above `ca` (shadow), so above `p` (trap), so it lands at `p`
  obtain ⟨i', hi', hmin'⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hRb))
  have hi0 : i' ≠ 0 := land_index_pos htop hi'
  obtain ⟨k', hk'⟩ : ∃ k', i' = k' + 1 := ⟨i' - 1, by omega⟩
  subst hk'
  have hA2' : ∀ w, height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → F ⊥ w = cb ∨ F ⊥ w = ca :=
    fun w h1 h0 => (hA2 w h1 h0).symm
  have hU' : ∀ z, F ⊥ z = ⊥ → cb ≤ z → ca ≤ z → False := fun z hz h1 h2 => hU z hz h2 h1
  have hsh : ca ≤ F ⊥ ((F cb)^[k'] (⊤ : α)) :=
    twoColour_shadow hn ha hk2 htop hno hcb1 hcb0 hA2' hU' hi' hmin'
  have hstep := desc_ge_of_phi_last hsh
  have hQ : p ≤ F cb p ⊔ ca := by
    have hb : cb ≤ F cb p := by rw [← hφp]; exact (F.mono bot_le) p
    calc p = ca ⊔ cb := hPeq.symm
      _ = cb ⊔ ca := sup_comm _ _
      _ ≤ F cb p ⊔ ca := sup_le_sup_right hb ca
  have hpl : p ≤ (F cb)^[k'+1] (⊤ : α) :=
    desc_ge_of_postfixed (fun j hj => hstep j (by omega)) hQ (k' + 1) le_rfl
  have hp2' : height H p = 2 := hp2
  have hlam : (F cb)^[k'+1] (⊤ : α) = p := (eq_of_le_of_height_ge hn hpl (by omega)).symm
  exact hno ⟨cb, hRb, hcb1, k' + 1, hi', hmin', by rw [hlam]; exact hφp⟩

/-- **No colour trap.** No `Q ≥ ca` has `Q ≤ F(ca, Q) ⊔ cb`. -/
theorem twoColour_noTrap {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    (hno : ¬ ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q)
    {ca cb : α} (hca1 : height H ca = 1) (hca0 : F ⊥ ca = ⊥) (hcb1 : height H cb = 1) (hcb0 : F ⊥ cb = ⊥)
    (hab : ca ≠ cb)
    (hA2 : ∀ w, height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → F ⊥ w = ca ∨ F ⊥ w = cb)
    (hU : ∀ z, F ⊥ z = ⊥ → ca ≤ z → cb ≤ z → False)
    {Q : α} (hQa : ca ≤ Q) (hQ : Q ≤ F ca Q ⊔ cb) : False := by
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hRa : ca ∈ Rk F 1 := (mem_one_iff ha).2 hca0
  obtain ⟨i, hi, hmin⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hRa))
  have hi0 : i ≠ 0 := land_index_pos htop hi
  obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  subst hk
  have hsh := twoColour_shadow hn ha hk2 htop hno hca1 hca0 hA2 hU hi hmin
  have hstep := desc_ge_of_phi_last hsh
  have hQl : Q ≤ (F ca)^[k+1] (⊤ : α) :=
    desc_ge_of_postfixed (fun j hj => hstep j (by omega)) hQ (k + 1) le_rfl
  exact twoColour_not_above hn ha hk2 htop hno hca1 hca0 hcb1 hcb0 hab hA2 hU hi hmin (hQa.trans hQl)

end Mordor.OrbitHeight
