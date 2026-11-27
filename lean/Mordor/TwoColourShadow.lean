import Mordor.TwoColour

/-!
# The self-shadow; CertAtom with two colour atoms (§34.3z²⁹⁸)

Setting of `TwoColour.lean`: W0, no μ-fixed atom, exactly two colour atoms `ca ≠ cb`, no element of `Z` above both.

* `twoColour_selfShadow` (ShadowLemma): the last high element `r` of row `ca` has `ca ≤ F(⊥, r)`. The proof walks the
  staircase of rows `ca` and `cb` with value row `⊥` (as in `pairStair`) from the `cb` end, carrying "`ca` lies below
  the boundary value". It starts from `twoColour_shadow` for row `cb`. A low corner `A ≥ ca` either lies in `Z` (then
  the boundary value is `ca` or `A`), or has `F(⊥, A) = ca`, or is `ca ⊔ cb` with `F(⊥, ca ⊔ cb) = cb`. The last case
  is impossible (Lemma K): every element of row `cb`'s descent up to its landing lies above `ca` (ColourGain), so one
  above `ca ⊔ cb` keeps the next one above `cb`, the landing becomes `ca ⊔ cb`, and `cb` is μ-fixed.
* `certAtom_of_le_two_colours`: CertAtom whenever every colour atom is one of two given atoms of `Z`.
* `certAtom_of_twoColours`: CertAtom whenever the colour atoms are exactly two atoms with no common upper bound in `Z`.
  The self-shadow puts `ca` below `λ(ca)`, against `twoColour_not_above`.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} [CompleteLattice α] {F : α →o α →o α}

/-- **ShadowLemma.** The last high element of row `ca` lies above `ca` under row `⊥`. -/
theorem twoColour_selfShadow {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    (hno : ¬ ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q)
    {ca cb : α} (hca1 : height H ca = 1) (hca0 : F ⊥ ca = ⊥) (hcb1 : height H cb = 1) (hcb0 : F ⊥ cb = ⊥)
    (hab : ca ≠ cb)
    (hA2 : ∀ w, height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → F ⊥ w = ca ∨ F ⊥ w = cb)
    (hU : ∀ z, F ⊥ z = ⊥ → ca ≤ z → cb ≤ z → False)
    {k : ℕ} (hi : height H ((F ca)^[k + 1] (⊤ : α)) ≤ 2) (hmin : ∀ j < k + 1, 2 < height H ((F ca)^[j] (⊤ : α))) :
    ca ≤ F ⊥ ((F ca)^[k] (⊤ : α)) := by
  classical
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hk2 z (hR12 ((mem_one_iff ha).2 hz))
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hne : ∀ B, 2 < height H B → F ⊥ B ≠ ⊥ := fun B hB h => by have := hZT B h; omega
  have hpos : ∀ {z : α}, z ≠ ⊥ → 1 ≤ height H z := fun hz => by
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hz); rw [height_bot_eq_zero] at this; omega
  have hmono := (height_strictMono hn).monotone
  have hRb : cb ∈ Rk F 1 := (mem_one_iff ha).2 hcb0
  have hca_ne : ca ≠ ⊥ := fun h => by rw [h, height_bot_eq_zero] at hca1; omega
  have hnofix : ∀ {z : α}, z ≤ F ⊥ z → z = ⊥ := fun h => le_bot_iff.1 (ha ▸ le_a h)
  -- row `cb`: landing, ColourGain, and the shadow of `ca` at its last high element
  obtain ⟨i', hi', hmin'⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hRb))
  have hi'0 : i' ≠ 0 := land_index_pos htop hi'
  obtain ⟨k', rfl⟩ : ∃ k', i' = k' + 1 := ⟨i' - 1, by omega⟩
  have hA2' : ∀ w, height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → F ⊥ w = cb ∨ F ⊥ w = ca :=
    fun w h1 h0 => (hA2 w h1 h0).symm
  have hU' : ∀ z, F ⊥ z = ⊥ → cb ≤ z → ca ≤ z → False := fun z hz h1 h2 => hU z hz h2 h1
  have hq : ca ≤ (F cb)^[k' + 1] (⊤ : α) := twoColour_gain hn ha hk2 htop hno hA2' hi' hmin'
  have he0 : ca ≤ F ⊥ ((F cb)^[k'] (⊤ : α)) :=
    twoColour_shadow hn ha hk2 htop hno hcb1 hcb0 hA2' hU' hi' hmin'
  have hanti_a : ∀ {s t : ℕ}, s ≤ t → (F ca)^[t] (⊤ : α) ≤ (F ca)^[s] (⊤ : α) :=
    fun h => iter_antitone_of_le (F ca).monotone (le_top : F ca ⊤ ≤ ⊤) h
  have hanti_b : ∀ {s t : ℕ}, s ≤ t → (F cb)^[t] (⊤ : α) ≤ (F cb)^[s] (⊤ : α) :=
    fun h => iter_antitone_of_le (F cb).monotone (le_top : F cb ⊤ ≤ ⊤) h
  -- `ca ⊔ cb` has height 2
  have hlt : ca < ca ⊔ cb := by
    refine lt_of_le_of_ne le_sup_left (fun e => hab ?_)
    have hba : cb ≤ ca := e ▸ le_sup_right
    have hb0 : cb ≠ ⊥ := fun h => by rw [h, height_bot_eq_zero] at hcb1; omega
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hb0)
    exact (eq_of_le_of_height_ge hn hba (by omega)).symm
  have hJ2 : 2 ≤ height H (ca ⊔ cb) := by have := height_strictMono hn hlt; omega
  -- Lemma K: no element of row `cb`'s descent up to its landing lies above `ca ⊔ cb` when `F(⊥, ca ⊔ cb) = cb`
  have hK : ∀ m, m ≤ k' + 1 → F ⊥ (ca ⊔ cb) = cb → ca ⊔ cb ≤ (F cb)^[m] (⊤ : α) → False := by
    intro m hm hφJ hJm
    have hup : ∀ t, m + t ≤ k' + 1 → ca ⊔ cb ≤ (F cb)^[m + t] (⊤ : α) := by
      intro t
      induction t with
      | zero => intro _; simpa using hJm
      | succ t ih =>
        intro ht
        have hprev := ih (by omega)
        have hb : cb ≤ (F cb)^[m + (t + 1)] (⊤ : α) := by
          rw [show m + (t + 1) = (m + t) + 1 by omega, Function.iterate_succ_apply']
          calc cb = F ⊥ (ca ⊔ cb) := hφJ.symm
            _ ≤ F ⊥ ((F cb)^[m + t] (⊤ : α)) := (F ⊥).mono hprev
            _ ≤ F cb ((F cb)^[m + t] (⊤ : α)) := (F.mono bot_le) _
        have ha' : ca ≤ (F cb)^[m + (t + 1)] (⊤ : α) := hq.trans (hanti_b (by omega))
        exact sup_le ha' hb
    have hland := hup (k' + 1 - m) (by omega)
    rw [show m + (k' + 1 - m) = k' + 1 by omega] at hland
    have heq : ca ⊔ cb = (F cb)^[k' + 1] (⊤ : α) := eq_of_le_of_height_ge hn hland (by omega)
    exact hno ⟨cb, hRb, hcb1, k' + 1, hi', hmin', by rw [← heq]; exact hφJ⟩
  -- the staircase of rows `ca` and `cb`
  let D : ℕ → ℕ → α := fun j k => (F ca)^[j] (⊤ : α) ⊓ (F cb)^[k] (⊤ : α)
  have hex : ∀ l, ∃ k, height H (D l k) ≤ 2 := fun l => ⟨k' + 1, le_trans (hmono inf_le_right) hi'⟩
  let κ : ℕ → ℕ := fun l => Nat.find (hex l)
  have hκlow : ∀ l, height H (D l (κ l)) ≤ 2 := fun l => Nat.find_spec (hex l)
  have hκmin : ∀ l k, k < κ l → 2 < height H (D l k) := fun l k hk => by
    have := Nat.find_min (hex l) hk; omega
  have hDk : ∀ l s t : ℕ, s ≤ t → D l t ≤ D l s := fun _ _ _ h => inf_le_inf_left _ (hanti_b h)
  have hDj : ∀ k s t : ℕ, s ≤ t → D t k ≤ D s k := fun _ _ _ h => inf_le_inf_right _ (hanti_a h)
  have hD0 : ∀ l, D l 0 = (F ca)^[l] (⊤ : α) := fun l => by simp [D]
  have hD0' : ∀ k, D 0 k = (F cb)^[k] (⊤ : α) := fun k => by simp [D]
  have hκpos : ∀ l, l < k + 1 → κ l ≠ 0 := fun l hl e => by
    have h0 := hκlow l; rw [e, hD0] at h0; have := hmin l hl; omega
  have hκanti : ∀ l, κ (l + 1) ≤ κ l := fun l =>
    Nat.find_min' (hex (l + 1)) (le_trans (hmono (hDj (κ l) _ _ (Nat.le_succ l))) (hκlow l))
  have hκ0 : κ 0 = k' + 1 := by
    apply le_antisymm
    · exact Nat.find_min' (hex 0) (by rw [hD0']; exact hi')
    · by_contra hc
      have := hmin' (κ 0) (by omega)
      have h1 := hκlow 0; rw [hD0'] at h1; omega
  have hκle : ∀ l, κ l ≤ k' + 1 := by
    intro l; induction l with
    | zero => exact le_of_eq hκ0
    | succ l ih => exact (hκanti l).trans ih
  -- the boundary value at `l` lies below the corner `D (l+1) (κ l)`
  have hbd : ∀ l, l < k + 1 → F ⊥ (D l (κ l - 1)) ≤ D (l + 1) (κ l) := by
    intro l hl
    have hk1 : κ l = κ l - 1 + 1 := by have := hκpos l hl; omega
    show F ⊥ (D l (κ l - 1)) ≤ (F ca)^[l + 1] (⊤ : α) ⊓ (F cb)^[κ l] (⊤ : α)
    refine le_inf ?_ ?_
    · rw [Function.iterate_succ_apply']
      exact ((F ⊥).mono inf_le_left).trans ((F.mono bot_le) _)
    · rw [hk1, Function.iterate_succ_apply']
      exact ((F ⊥).mono inf_le_right).trans ((F.mono bot_le) _)
  -- forward induction: `ca` lies below every boundary value
  have key : ∀ l, l < k + 1 → ca ≤ F ⊥ (D l (κ l - 1)) := by
    intro l
    induction l with
    | zero =>
      intro _
      rw [hκ0, show k' + 1 - 1 = k' by omega, hD0']; exact he0
    | succ l ih =>
      intro hl
      have hprev := ih (by omega)
      set A := D (l + 1) (κ (l + 1)) with hAdef
      set B := D (l + 1) (κ (l + 1) - 1) with hBdef
      have hk1 : κ (l + 1) - 1 < κ (l + 1) := by have := hκpos (l + 1) hl; omega
      have hBh : 2 < height H B := hκmin (l + 1) _ hk1
      have hAl : height H A ≤ 2 := hκlow (l + 1)
      have hAB : A ≤ B := hDk (l + 1) _ _ (Nat.sub_le _ 1)
      have hcaA : ca ≤ A := hprev.trans ((hbd l (by omega)).trans (hDk (l + 1) _ _ (hκanti l)))
      have heA : F ⊥ B ≤ A := (hbd (l + 1) hl).trans (hDj _ _ _ (Nat.le_succ _))
      have hφA : F ⊥ A ≤ F ⊥ B := (F ⊥).mono hAB
      have heB0 := hne B hBh
      by_cases hA0 : F ⊥ A = ⊥
      · -- `A ∈ Z`: the boundary value lies in `Z` below `A`
        have he0' : F ⊥ (F ⊥ B) = ⊥ := le_bot_iff.1 (((F ⊥).mono heA).trans (le_of_eq hA0))
        have h1 := hpos heB0
        have h2 := hmono heA
        rcases (show height H (F ⊥ B) = 1 ∨ height H (F ⊥ B) = 2 by omega) with h | h
        · rcases hA2 B h he0' with e | e
          · exact le_of_eq e.symm
          · exact absurd (hU A hA0 hcaA (e ▸ heA)) id
        · have e : F ⊥ B = A := eq_of_le_of_height_ge hn heA (by omega)
          exact e ▸ hcaA
      · -- `A ∉ Z`: `F(⊥, A)` is a colour
        have hφAA : F ⊥ A ≤ A := hφA.trans heA
        have hφne : F ⊥ A ≠ A := fun e => hca_ne (le_bot_iff.1 (hcaA.trans (le_of_eq (hnofix (le_of_eq e.symm)))))
        have hφ1 : height H (F ⊥ A) = 1 := by
          have := height_strictMono hn (lt_of_le_of_ne hφAA hφne); have := hpos hA0; omega
        have hφφ : F ⊥ (F ⊥ A) = ⊥ := by
          by_contra hb
          have h1 := hpos hb
          have hle' : F ⊥ (F ⊥ A) ≤ F ⊥ A := (F ⊥).mono hφAA
          have e : F ⊥ (F ⊥ A) = F ⊥ A := eq_of_le_of_height_ge hn hle' (by omega)
          exact hA0 (hnofix (le_of_eq e.symm))
        rcases hA2 A hφ1 hφφ with e | e
        · exact (le_of_eq e.symm).trans hφA
        · exfalso
          have hcbA : cb ≤ A := e ▸ hφAA
          have hJA : ca ⊔ cb = A := eq_of_le_of_height_ge hn (sup_le hcaA hcbA) (by omega)
          have hAw : A ≤ (F cb)^[κ (l + 1)] (⊤ : α) := inf_le_right
          exact hK (κ (l + 1)) (hκle _) (hJA ▸ e) (hJA ▸ hAw)
  have hlast := key k (by omega)
  exact hlast.trans ((F ⊥).mono inf_le_left)

/-- **CertAtom with two unbounded colours.** In W0, if the colour atoms (atoms of `Z` that are values of row `⊥`) are
exactly `ca ≠ cb` and no element of `Z` lies above both, some atom of `R_1` is μ-fixed. -/
theorem certAtom_of_twoColours {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    {ca cb : α} (hca1 : height H ca = 1) (hca0 : F ⊥ ca = ⊥) (hcb1 : height H cb = 1) (hcb0 : F ⊥ cb = ⊥)
    (hab : ca ≠ cb)
    (hA2 : ∀ w, height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → F ⊥ w = ca ∨ F ⊥ w = cb)
    (hU : ∀ z, F ⊥ z = ⊥ → ca ≤ z → cb ≤ z → False) :
    ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q := by
  by_contra hno
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hRa : ca ∈ Rk F 1 := (mem_one_iff ha).2 hca0
  obtain ⟨i, hi, hmin⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hRa))
  have hi0 : i ≠ 0 := land_index_pos htop hi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hs := twoColour_selfShadow hn ha hk2 htop hno hca1 hca0 hcb1 hcb0 hab hA2 hU hi hmin
  have hland : ca ≤ (F ca)^[k + 1] (⊤ : α) := by
    rw [Function.iterate_succ_apply']; exact hs.trans ((F.mono bot_le) _)
  exact twoColour_not_above hn ha hk2 htop hno hca1 hca0 hcb1 hcb0 hab hA2 hU hi hmin hland

/-- **CertAtom with at most two colours.** In W0, if every colour atom is `ca` or `cb` (atoms of `Z`, possibly equal),
some atom of `R_1` is μ-fixed: bounded colours by `certAtom_of_boundedAtoms`, unbounded ones by
`certAtom_of_twoColours`. -/
theorem certAtom_of_le_two_colours {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    {ca cb : α} (hca1 : height H ca = 1) (hca0 : F ⊥ ca = ⊥) (hcb1 : height H cb = 1) (hcb0 : F ⊥ cb = ⊥)
    (hA2 : ∀ w, height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → F ⊥ w = ca ∨ F ⊥ w = cb) :
    ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q := by
  by_cases hB : ∃ z, F ⊥ z = ⊥ ∧ ca ≤ z ∧ cb ≤ z
  · obtain ⟨z, hz0, hz1, hz2⟩ := hB
    refine certAtom_of_boundedAtoms hn ha hk2 htop hz0 (fun w h1 h0 => ?_)
    rcases hA2 w h1 h0 with e | e
    · exact e ▸ hz1
    · exact e ▸ hz2
  · push_neg at hB
    have hab : ca ≠ cb := fun e => hB ca hca0 le_rfl (e ▸ le_rfl)
    exact certAtom_of_twoColours hn ha hk2 htop hca1 hca0 hcb1 hcb0 hab hA2
      (fun z hz h1 h2 => hB z hz h1 h2)

end Mordor.OrbitHeight
