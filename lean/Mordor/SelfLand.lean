import Mordor.ThinColour

/-!
# SelfLand: an atom below its own landing drags every row above it that keeps it (§34.3z³⁰², brief run 22)

Setting: a finite lattice (`NoChain α (H+1)`), `F` monotone in both arguments, `φ = F ⊥`.
Only two hypotheses are used about `F`: high elements are outside `Z` (`hne`, a consequence of ZT), and row `q` has
no lower cell at a high column (Tb at `q`).

* `selfLand`: let `q` be an atom with Tb, and `p = (F q)^[i] ⊤` an element of height 2 of row `q`'s descent with
  `q ≤ p`.  If `y ≥ q` is a row that lands and `q ≤ λ(y)`, then `λ(y) = p`.
  (The descent of `y` stays above `p`: at the first step where it would leave `↑p`, the trap of `trap_of_tb`, run
  without its hypothesis `q ≤ F(q, p)`, finds a high column `X` where row `q` takes an atom value `t ≠ q` of `p`;
  that atom lies in the next descent element, and so does `q`, so `p = q ⊔ t` does too.)
* `selfPair` (D2′ of brief run 25, in its strong form): in W0, if `c ∈ Z` is an atom with `c ≤ λ(c) = m ∈ Z`, then
  `c ≰ λ(m)`.  No NoFix, no ColourGain, no universality.
* `certAtom_of_closed` (S4 closed): in W0, an atom `c ∈ Z` with `c ≤ λ(c)`, and `c ≤ λ(λ(c))` if `λ(c) ∈ Z`,
  `c ≤ λ(F(⊥, λ(c)))` if `λ(c) ∉ Z`, gives a μ-fixed atom.  So a colour below the landing of every colour row and
  every pair-join row (a universal colour) gives a μ-fixed atom.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} [CompleteLattice α] {F : α →o α →o α}

/-- **SelfLand.** `q` an atom with Tb, `p` a height-2 element of row `q`'s descent with `q ≤ p`; a row `y ≥ q`
landing at index `i'` with `q ≤ λ(y)` lands at `p`. -/
theorem selfLand {H : ℕ} (hn : NoChain α (H + 1)) (hne : ∀ B, 2 < height H B → F ⊥ B ≠ ⊥)
    {q y : α} {i : ℕ} (hq : height H q = 1) (hTb : ∀ B, 2 < height H B → ¬ F q B ≤ q)
    (hp2 : height H ((F q)^[i] (⊤ : α)) = 2) (hqp : q ≤ (F q)^[i] (⊤ : α)) (hqy : q ≤ y)
    {i' : ℕ} (hi' : height H ((F y)^[i'] (⊤ : α)) ≤ 2) (hmin' : ∀ j < i', 2 < height H ((F y)^[j] (⊤ : α)))
    (hql : q ≤ (F y)^[i'] (⊤ : α)) :
    (F y)^[i'] (⊤ : α) = (F q)^[i] (⊤ : α) := by
  set p := (F q)^[i] (⊤ : α) with hpdef
  have hanti_q : ∀ {s t : ℕ}, s ≤ t → (F q)^[t] (⊤ : α) ≤ (F q)^[s] (⊤ : α) :=
    fun h => iter_antitone_of_le (F q).monotone (le_top : F q ⊤ ≤ ⊤) h
  have hanti_y : ∀ {s t : ℕ}, s ≤ t → (F y)^[t] (⊤ : α) ≤ (F y)^[s] (⊤ : α) :=
    fun h => iter_antitone_of_le (F y).monotone (le_top : F y ⊤ ≤ ⊤) h
  have hpos : ∀ {z : α}, z ≠ ⊥ → 1 ≤ height H z := fun hz => by
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hz); rw [height_bot_eq_zero] at this; omega
  -- every element of row `y`'s descent up to the landing lies above `p`
  have hall : ∀ j, j ≤ i' → p ≤ (F y)^[j] (⊤ : α) := by
    intro j
    induction j with
    | zero => intro _; exact le_top
    | succ j ih =>
      intro hj
      have hr : p ≤ (F y)^[j] (⊤ : α) := ih (by omega)
      set r := (F y)^[j] (⊤ : α) with hrdef
      have hrh : 2 < height H r := hmin' j (by omega)
      by_contra hns
      have hs : (F y)^[j + 1] (⊤ : α) = F y r := by rw [Function.iterate_succ_apply']
      have hqs : q ≤ (F y)^[j + 1] (⊤ : α) := hql.trans (hanti_y hj)
      have hFr : F q r ≤ (F y)^[j + 1] (⊤ : α) := hs ▸ (F.mono hqy) r
      have hsr : (F y)^[j + 1] (⊤ : α) ≤ r := hanti_y (Nat.le_succ j)
      -- the trap, run from the landing of row `q` up to `⊤`
      have trap : ∀ t, t ≤ i → r ⊓ (F q)^[i - t] (⊤ : α) = p := by
        intro t
        induction t with
        | zero => intro _; rw [Nat.sub_zero]; exact inf_eq_right.2 hr
        | succ t iht =>
          intro ht
          have IH := iht (by omega)
          have hjs : i - t = (i - (t + 1)) + 1 := by omega
          rw [hjs, Function.iterate_succ_apply'] at IH
          set X := r ⊓ (F q)^[i - (t + 1)] (⊤ : α) with hXdef
          have hpX : p ≤ X := le_inf hr (hanti_q (by omega))
          have hFXr : F q X ≤ F q r := (F q).mono inf_le_left
          have hFX : F q X ≤ p := by
            rw [← IH]
            exact le_inf (hFXr.trans (hFr.trans hsr)) ((F q).mono inf_le_right)
          by_cases hX : 2 < height H X
          · exfalso
            have hφ : F ⊥ X ≠ ⊥ := hne X hX
            have hφle : F ⊥ X ≤ F q X := (F.mono bot_le) X
            have hFX0 : F q X ≠ ⊥ := fun e => hφ (le_bot_iff.1 (e ▸ hφle))
            have hFXs : F q X ≤ (F y)^[j + 1] (⊤ : α) := hFXr.trans hFr
            have hFXp : F q X ≠ p := fun e => hns (e ▸ hFXs)
            have hlt := height_strictMono hn (lt_of_le_of_ne hFX hFXp)
            have h1 : height H (F q X) = 1 := by have := hpos hFX0; omega
            have hnq : q ≠ F q X := fun e => hTb X hX (le_of_eq e.symm)
            obtain ⟨hJ, -⟩ := join_of_two_atoms hn hq h1 hnq hqp hFX (le_of_eq hp2)
            exact hns (hJ.le.trans (sup_le hqs hFXs))
          · exact (eq_of_le_of_height_ge hn hpX (by omega)).symm
      have h0 := trap i le_rfl
      rw [Nat.sub_self, Function.iterate_zero, id, inf_top_eq] at h0
      have : height H r = 2 := h0 ▸ hp2
      omega
  exact (eq_of_le_of_height_ge hn (hall i' le_rfl) (by omega)).symm

/-- **SelfPair** (D2′, strong form). In W0, an atom `c ∈ Z` below its own landing `m ∈ Z` is not below `λ(m)`. -/
theorem selfPair {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    {c : α} (hc1 : height H c = 1) (hc0 : F ⊥ c = ⊥)
    {i : ℕ} (hi : height H ((F c)^[i] (⊤ : α)) ≤ 2) (hmin : ∀ j < i, 2 < height H ((F c)^[j] (⊤ : α)))
    (hcl : c ≤ (F c)^[i] (⊤ : α)) (hm0 : F ⊥ ((F c)^[i] (⊤ : α)) = ⊥)
    {i' : ℕ} (hi' : height H ((F ((F c)^[i] (⊤ : α)))^[i'] (⊤ : α)) ≤ 2)
    (hmin' : ∀ j < i', 2 < height H ((F ((F c)^[i] (⊤ : α)))^[j] (⊤ : α))) :
    ¬ c ≤ (F ((F c)^[i] (⊤ : α)))^[i'] (⊤ : α) := by
  intro hcm
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hk2 z (hR12 ((mem_one_iff ha).2 hz))
  have hne : ∀ B, 2 < height H B → F ⊥ B ≠ ⊥ := fun B hB h => by have := hZT B h; omega
  set m := (F c)^[i] (⊤ : α) with hmdef
  have hcR : c ∈ Rk F 1 := (mem_one_iff ha).2 hc0
  have hmR : m ∈ Rk F 1 := (mem_one_iff ha).2 hm0
  -- `m ≠ c` (the landing is not below its row), so `m` has height 2
  have hmc : m ≠ c := fun e => land_not_le hk2 hcR htop hi hmin (le_of_eq e)
  have hm2 : height H m = 2 := by
    have := height_strictMono hn (lt_of_le_of_ne hcl (Ne.symm hmc)); omega
  have heq := selfLand hn hne hc1 (tb_of_tight hk2 hcR) hm2 hcl hcl hi' hmin' hcm
  exact land_not_le hk2 hmR htop hi' hmin' (le_of_eq heq)

/-- **Closed atom ⟹ CertAtom.** In W0, let `c ∈ Z` be an atom with `c ≤ λ(c) = p`, and `c ≤ λ(p)` if `p ∈ Z`,
`c ≤ λ(F(⊥, p))` if `p ∉ Z`.  Then some atom of `R_1` is μ-fixed (`c` itself, or the exit atom of `p`). -/
theorem certAtom_of_closed {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    {c : α} (hc1 : height H c = 1) (hc0 : F ⊥ c = ⊥)
    {i : ℕ} (hi : height H ((F c)^[i] (⊤ : α)) ≤ 2) (hmin : ∀ j < i, 2 < height H ((F c)^[j] (⊤ : α)))
    (hcl : c ≤ (F c)^[i] (⊤ : α))
    (hZc : F ⊥ ((F c)^[i] (⊤ : α)) = ⊥ → ∀ i', height H ((F ((F c)^[i] (⊤ : α)))^[i'] (⊤ : α)) ≤ 2 →
      (∀ j < i', 2 < height H ((F ((F c)^[i] (⊤ : α)))^[j] (⊤ : α))) → c ≤ (F ((F c)^[i] (⊤ : α)))^[i'] (⊤ : α))
    (hXc : F ⊥ ((F c)^[i] (⊤ : α)) ≠ ⊥ → ∀ i', height H ((F (F ⊥ ((F c)^[i] (⊤ : α))))^[i'] (⊤ : α)) ≤ 2 →
      (∀ j < i', 2 < height H ((F (F ⊥ ((F c)^[i] (⊤ : α))))^[j] (⊤ : α))) →
      c ≤ (F (F ⊥ ((F c)^[i] (⊤ : α))))^[i'] (⊤ : α)) :
    ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q := by
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hcR : c ∈ Rk F 1 := (mem_one_iff ha).2 hc0
  set p := (F c)^[i] (⊤ : α) with hpdef
  by_cases hpZ : F ⊥ p = ⊥
  · exfalso
    have hpR : p ∈ Rk F 1 := (mem_one_iff ha).2 hpZ
    obtain ⟨i', hi', hmin'⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hpR))
    exact selfPair hn ha hk2 htop hc1 hc0 hi hmin hcl hpZ hi' hmin' (hZc hpZ i' hi' hmin')
  · obtain ⟨hp2, hs1, hs0⟩ := exit_atom hn hk2 ha hcR htop hi hmin hpZ
    set s := F ⊥ p with hsdef
    by_cases hcs : s = c
    · exact ⟨c, hcR, hc1, i, hi, hmin, hcs⟩
    · -- `p = c ⊔ s`; row `s` lands above `c`, so (capture) at `p`, and `s` is μ-fixed
      have hsR : s ∈ Rk F 1 := (mem_one_iff ha).2 hs0
      have hsp : s ≤ p := (land_bot_lt hk2 ha hcR htop hi hmin).le
      obtain ⟨hJ, -⟩ := join_of_two_atoms hn hc1 hs1 (Ne.symm hcs) hcl hsp (by omega)
      obtain ⟨i', hi', hmin'⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hsR))
      have hcs' : c ≤ (F s)^[i'] (⊤ : α) := hXc hpZ i' hi' hmin'
      have hcap : p ≤ F ⊥ p ⊔ c := hJ.le.trans (sup_le le_sup_right le_sup_left)
      have hle := land_capture hcs' hcap
      have hp2' : height H p = 2 := hp2
      have hi'' : height H ((F s)^[i'] (⊤ : α)) ≤ 2 := hi'
      have heq : p = (F s)^[i'] (⊤ : α) := eq_of_le_of_height_ge hn hle (by omega)
      exact ⟨s, hsR, hs1, i', hi', hmin', by rw [← heq]⟩

/-- **Cross atom** (the trap of `trap_of_tb` run without `q ≤ F(q, p)`).  `q` an atom with Tb, `p` a height-2
element of row `q`'s descent, `y ≥ q`; if `r = (F y)^[K] ⊤` is high and above `p` but the next element of row `y`'s
descent is not, then some high `X` has `F(q, X) = F(⊥, X)` an atom below `p`, other than `q`, below `(F y)^[K+1] ⊤`. -/
theorem crossAtom {H : ℕ} (hn : NoChain α (H + 1)) (hne : ∀ B, 2 < height H B → F ⊥ B ≠ ⊥)
    {q y : α} {i K : ℕ} (hq : height H q = 1) (hTb : ∀ B, 2 < height H B → ¬ F q B ≤ q)
    (hp2 : height H ((F q)^[i] (⊤ : α)) = 2) (hqy : q ≤ y)
    (hr : (F q)^[i] (⊤ : α) ≤ (F y)^[K] (⊤ : α)) (hrh : 2 < height H ((F y)^[K] (⊤ : α)))
    (hns : ¬ (F q)^[i] (⊤ : α) ≤ (F y)^[K + 1] (⊤ : α)) :
    ∃ X, 2 < height H X ∧ F q X = F ⊥ X ∧ height H (F q X) = 1 ∧ F q X ≤ (F q)^[i] (⊤ : α) ∧
      F q X ≠ q ∧ F q X ≤ (F y)^[K + 1] (⊤ : α) := by
  set p := (F q)^[i] (⊤ : α) with hpdef
  set r := (F y)^[K] (⊤ : α) with hrdef
  have hanti_q : ∀ {s t : ℕ}, s ≤ t → (F q)^[t] (⊤ : α) ≤ (F q)^[s] (⊤ : α) :=
    fun h => iter_antitone_of_le (F q).monotone (le_top : F q ⊤ ≤ ⊤) h
  have hpos : ∀ {z : α}, z ≠ ⊥ → 1 ≤ height H z := fun hz => by
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hz); rw [height_bot_eq_zero] at this; omega
  have hs : (F y)^[K + 1] (⊤ : α) = F y r := by rw [Function.iterate_succ_apply']
  have hFr : F q r ≤ (F y)^[K + 1] (⊤ : α) := hs ▸ (F.mono hqy) r
  have hsr : (F y)^[K + 1] (⊤ : α) ≤ r :=
    iter_antitone_of_le (F y).monotone (le_top : F y ⊤ ≤ ⊤) (Nat.le_succ K)
  by_contra hno
  push_neg at hno
  have trap : ∀ t, t ≤ i → r ⊓ (F q)^[i - t] (⊤ : α) = p := by
    intro t
    induction t with
    | zero => intro _; rw [Nat.sub_zero]; exact inf_eq_right.2 hr
    | succ t iht =>
      intro ht
      have IH := iht (by omega)
      have hjs : i - t = (i - (t + 1)) + 1 := by omega
      rw [hjs, Function.iterate_succ_apply'] at IH
      set X := r ⊓ (F q)^[i - (t + 1)] (⊤ : α) with hXdef
      have hpX : p ≤ X := le_inf hr (hanti_q (by omega))
      have hFXr : F q X ≤ F q r := (F q).mono inf_le_left
      have hFX : F q X ≤ p := by
        rw [← IH]
        exact le_inf (hFXr.trans (hFr.trans hsr)) ((F q).mono inf_le_right)
      by_cases hX : 2 < height H X
      · exfalso
        have hφ : F ⊥ X ≠ ⊥ := hne X hX
        have hφle : F ⊥ X ≤ F q X := (F.mono bot_le) X
        have hFX0 : F q X ≠ ⊥ := fun e => hφ (le_bot_iff.1 (e ▸ hφle))
        have hFXs : F q X ≤ (F y)^[K + 1] (⊤ : α) := hFXr.trans hFr
        have hFXp : F q X ≠ p := fun e => hns (e ▸ hFXs)
        have hlt := height_strictMono hn (lt_of_le_of_ne hFX hFXp)
        have h1 : height H (F q X) = 1 := by have := hpos hFX0; omega
        have hφ1 : 1 ≤ height H (F ⊥ X) := hpos hφ
        have heqφ : F ⊥ X = F q X := eq_of_le_of_height_ge hn hφle (by omega)
        have hnq : F q X ≠ q := fun e => hTb X hX (le_of_eq e)
        exact hno X hX heqφ.symm h1 hFX hnq hFXs
      · exact (eq_of_le_of_height_ge hn hpX (by omega)).symm
  have h0 := trap i le_rfl
  rw [Nat.sub_self, Function.iterate_zero, id, inf_top_eq] at h0
  have : height H r = 2 := h0 ▸ hp2
  omega

/-- **TwoSelf** (the proved half of PairLocal).  Two atoms `q₁ ≠ q₂` with Tb whose rows reach the same height-2
element `p ≥ q₁, q₂`, and no other atom below `p` is a value `F(⊥, X)` at a high column.  Then every row `y ≥ q₁, q₂`
that lands lands at `p`. -/
theorem twoSelf {H : ℕ} (hn : NoChain α (H + 1)) (hne : ∀ B, 2 < height H B → F ⊥ B ≠ ⊥)
    {q₁ q₂ y : α} {i₁ i₂ : ℕ} (hq₁ : height H q₁ = 1) (hq₂ : height H q₂ = 1) (h12 : q₁ ≠ q₂)
    (hTb₁ : ∀ B, 2 < height H B → ¬ F q₁ B ≤ q₁) (hTb₂ : ∀ B, 2 < height H B → ¬ F q₂ B ≤ q₂)
    (hp : (F q₂)^[i₂] (⊤ : α) = (F q₁)^[i₁] (⊤ : α)) (hp2 : height H ((F q₁)^[i₁] (⊤ : α)) = 2)
    (hq₁p : q₁ ≤ (F q₁)^[i₁] (⊤ : α)) (hq₂p : q₂ ≤ (F q₁)^[i₁] (⊤ : α))
    (hcol : ∀ X, 2 < height H X → F ⊥ X ≤ (F q₁)^[i₁] (⊤ : α) → height H (F ⊥ X) = 1 → F ⊥ X = q₁ ∨ F ⊥ X = q₂)
    (hq₁y : q₁ ≤ y) (hq₂y : q₂ ≤ y)
    {i' : ℕ} (hi' : height H ((F y)^[i'] (⊤ : α)) ≤ 2) (hmin' : ∀ j < i', 2 < height H ((F y)^[j] (⊤ : α))) :
    (F y)^[i'] (⊤ : α) = (F q₁)^[i₁] (⊤ : α) := by
  set p := (F q₁)^[i₁] (⊤ : α) with hpdef
  have hp2' : height H ((F q₂)^[i₂] (⊤ : α)) = 2 := hp ▸ hp2
  have hall : ∀ j, j ≤ i' → p ≤ (F y)^[j] (⊤ : α) := by
    intro j
    induction j with
    | zero => intro _; exact le_top
    | succ j ih =>
      intro hj
      have hr : p ≤ (F y)^[j] (⊤ : α) := ih (by omega)
      have hrh : 2 < height H ((F y)^[j] (⊤ : α)) := hmin' j (by omega)
      by_contra hns
      obtain ⟨X₁, hX₁, he₁, h₁, hle₁, hne₁, hs₁⟩ := crossAtom hn hne hq₁ hTb₁ hp2 hq₁y hr hrh hns
      have hr2 : (F q₂)^[i₂] (⊤ : α) ≤ (F y)^[j] (⊤ : α) := hp ▸ hr
      have hns2 : ¬ (F q₂)^[i₂] (⊤ : α) ≤ (F y)^[j + 1] (⊤ : α) := hp ▸ hns
      obtain ⟨X₂, hX₂, he₂, h₂, hle₂, hne₂, hs₂⟩ := crossAtom hn hne hq₂ hTb₂ hp2' hq₂y hr2 hrh hns2
      have hle₂' : F q₂ X₂ ≤ p := hp ▸ hle₂
      have ht₁ : F q₁ X₁ = q₂ := by
        rcases hcol X₁ hX₁ (he₁ ▸ hle₁) (he₁ ▸ h₁) with e | e
        · exact absurd (he₁.trans e) hne₁
        · exact he₁.trans e
      have ht₂ : F q₂ X₂ = q₁ := by
        rcases hcol X₂ hX₂ (he₂ ▸ hle₂') (he₂ ▸ h₂) with e | e
        · exact he₂.trans e
        · exact absurd (he₂.trans e) hne₂
      obtain ⟨hJ, -⟩ := join_of_two_atoms hn hq₁ hq₂ h12 hq₁p hq₂p (le_of_eq hp2)
      exact hns (hJ.le.trans (sup_le (ht₂ ▸ hs₂) (ht₁ ▸ hs₁)))
  exact (eq_of_le_of_height_ge hn (hall i' le_rfl) (by omega)).symm

/-- **TwoSelf in W0.**  Two distinct atoms `c₁, c₂ ∈ Z` landing at the same `m ∈ Z` with `c₁, c₂ ≤ m`, where every
atom value of row `⊥` below `m` is `c₁` or `c₂`: impossible (row `m` would land at `m`). -/
theorem twoSelf_absurd {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    {c₁ c₂ : α} {i₁ i₂ : ℕ} (hc₁ : height H c₁ = 1) (hc₂ : height H c₂ = 1) (h12 : c₁ ≠ c₂)
    (hc₁0 : F ⊥ c₁ = ⊥) (hc₂0 : F ⊥ c₂ = ⊥)
    (hi₁ : height H ((F c₁)^[i₁] (⊤ : α)) ≤ 2) (hmin₁ : ∀ j < i₁, 2 < height H ((F c₁)^[j] (⊤ : α)))
    (hp : (F c₂)^[i₂] (⊤ : α) = (F c₁)^[i₁] (⊤ : α))
    (hm0 : F ⊥ ((F c₁)^[i₁] (⊤ : α)) = ⊥)
    (hc₁p : c₁ ≤ (F c₁)^[i₁] (⊤ : α)) (hc₂p : c₂ ≤ (F c₁)^[i₁] (⊤ : α))
    (hcol : ∀ X, 2 < height H X → F ⊥ X ≤ (F c₁)^[i₁] (⊤ : α) → height H (F ⊥ X) = 1 →
      F ⊥ X = c₁ ∨ F ⊥ X = c₂) : False := by
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hk2 z (hR12 ((mem_one_iff ha).2 hz))
  have hne : ∀ B, 2 < height H B → F ⊥ B ≠ ⊥ := fun B hB h => by have := hZT B h; omega
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  set m := (F c₁)^[i₁] (⊤ : α) with hmdef
  have hc₁R : c₁ ∈ Rk F 1 := (mem_one_iff ha).2 hc₁0
  have hc₂R : c₂ ∈ Rk F 1 := (mem_one_iff ha).2 hc₂0
  have hmR : m ∈ Rk F 1 := (mem_one_iff ha).2 hm0
  have hmc : m ≠ c₁ := fun e => land_not_le hk2 hc₁R htop hi₁ hmin₁ (le_of_eq e)
  have hm2 : height H m = 2 := by
    have := height_strictMono hn (lt_of_le_of_ne hc₁p (Ne.symm hmc)); omega
  obtain ⟨i', hi', hmin'⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hmR))
  have heq := twoSelf hn hne hc₁ hc₂ h12 (tb_of_tight hk2 hc₁R) (tb_of_tight hk2 hc₂R) hp hm2 hc₁p hc₂p hcol
    hc₁p hc₂p hi' hmin'
  exact land_not_le hk2 hmR htop hi' hmin' (le_of_eq heq)

/-- **Case B, conditional** (the thin proof's Case B with SCL replaced by its conclusion).  In W0, suppose every
colour row exits, and any two colour rows' landings share a colour (`hint`; SCL without breaks gives it).  Then
some atom of `R_1` is μ-fixed.  The open step D1 is needed in Case B exactly to supply `hint`. -/
theorem certAtom_of_caseB {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    (hexit : ∀ v k, height H (F ⊥ v) = 1 → F ⊥ (F ⊥ v) = ⊥ →
      height H ((F (F ⊥ v))^[k + 1] (⊤ : α)) ≤ 2 → (∀ j < k + 1, 2 < height H ((F (F ⊥ v))^[j] (⊤ : α))) →
      F ⊥ ((F (F ⊥ v))^[k + 1] (⊤ : α)) ≠ ⊥)
    (hint : ∀ v w k k', height H (F ⊥ v) = 1 → F ⊥ (F ⊥ v) = ⊥ → height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ →
      height H ((F (F ⊥ v))^[k + 1] (⊤ : α)) ≤ 2 → (∀ j < k + 1, 2 < height H ((F (F ⊥ v))^[j] (⊤ : α))) →
      height H ((F (F ⊥ w))^[k' + 1] (⊤ : α)) ≤ 2 → (∀ j < k' + 1, 2 < height H ((F (F ⊥ w))^[j] (⊤ : α))) →
      ∃ u, height H (F ⊥ u) = 1 ∧ F ⊥ (F ⊥ u) = ⊥ ∧ F ⊥ u ≤ (F (F ⊥ v))^[k + 1] (⊤ : α) ∧
        F ⊥ u ≤ (F (F ⊥ w))^[k' + 1] (⊤ : α)) :
    ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q := by
  by_contra hno
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hland : ∀ z, F ⊥ z = ⊥ → ∃ k, height H ((F z)^[k + 1] (⊤ : α)) ≤ 2 ∧
      ∀ j < k + 1, 2 < height H ((F z)^[j] (⊤ : α)) := by
    intro z hz
    obtain ⟨i, hi, hmin⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ ((mem_one_iff ha).2 hz)))
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by have := land_index_pos htop hi; omega⟩
    exact ⟨k, hi, hmin⟩
  have hfix : ∀ c k, F ⊥ c = ⊥ → height H c = 1 → height H ((F c)^[k + 1] (⊤ : α)) ≤ 2 →
      (∀ j < k + 1, 2 < height H ((F c)^[j] (⊤ : α))) → F ⊥ ((F c)^[k + 1] (⊤ : α)) = c → False :=
    fun c k hc0 hc1 hi hmin he => hno ⟨c, (mem_one_iff ha).2 hc0, hc1, k + 1, hi, hmin, he⟩
  have hb0 : F ⊥ (⊥ : α) = ⊥ := by
    have h : F ⊥ (⊥ : α) ≤ a F ⊥ := le_a ((F ⊥).mono (bot_le : (⊥ : α) ≤ F ⊥ ⊥))
    rw [ha] at h; exact le_bot_iff.1 h
  obtain ⟨kb, hib, hminb⟩ := hland ⊥ hb0
  obtain ⟨w₀, hw₀1, hw₀0, -, -⟩ := colourGain hn ha hk2 htop hno hib hminb
  set ca := F ⊥ w₀ with hcadef
  obtain ⟨ka, hia, hmina⟩ := hland ca hw₀0
  have hpa0 := hexit w₀ ka hw₀1 hw₀0 hia hmina
  obtain ⟨hpa2, hsa1, hsa0⟩ := exit_atom hn hk2 ha ((mem_one_iff ha).2 hw₀0) htop hia hmina hpa0
  set pa := (F ca)^[ka + 1] (⊤ : α) with hpadef
  set sa := F ⊥ pa with hsadef
  have hsap : sa ≤ pa := (land_bot_lt hk2 ha ((mem_one_iff ha).2 hw₀0) htop hia hmina).le
  have hall : ∀ v, height H (F ⊥ v) = 1 → F ⊥ (F ⊥ v) = ⊥ → ∀ k,
      height H ((F (F ⊥ v))^[k + 1] (⊤ : α)) ≤ 2 → (∀ j < k + 1, 2 < height H ((F (F ⊥ v))^[j] (⊤ : α))) →
      F ⊥ ((F (F ⊥ v))^[k + 1] (⊤ : α)) = sa := by
    intro v hv1 hv0 k hi hmin
    set py := (F (F ⊥ v))^[k + 1] (⊤ : α) with hpydef
    have hpy0 := hexit v k hv1 hv0 hi hmin
    obtain ⟨hpy2, hsy1, hsy0⟩ := exit_atom hn hk2 ha ((mem_one_iff ha).2 hv0) htop hi hmin hpy0
    have hsyp : F ⊥ py ≤ py := (land_bot_lt hk2 ha ((mem_one_iff ha).2 hv0) htop hi hmin).le
    have hpy2' : height H py = 2 := hpy2
    have hpa2' : height H pa = 2 := hpa2
    obtain ⟨u, hu1, hu0, hua, hup⟩ := hint w₀ v ka k hw₀1 hw₀0 hv1 hv0 hia hmina hi hmin
    by_cases hus : F ⊥ u = sa
    · by_contra hne
      have hne' : sa ≠ F ⊥ py := fun e => hne e.symm
      have hsapy : sa ≤ py := hus ▸ hup
      obtain ⟨hJ, -⟩ := join_of_two_atoms hn hsa1 hsy1 hne' hsapy hsyp (by omega)
      have hcap : py ≤ F ⊥ py ⊔ sa := hJ.le.trans (sup_le le_sup_right le_sup_left)
      have hle := land_capture hsap hcap
      have heq : py = pa := eq_of_le_of_height_ge hn hle (by omega)
      exact hne (by rw [heq])
    · obtain ⟨hJ, -⟩ := join_of_two_atoms hn hu1 hsa1 hus hua hsap (by omega)
      have hcap : pa ≤ F ⊥ pa ⊔ F ⊥ u := hJ.le.trans (sup_le le_sup_right le_sup_left)
      have hle := land_capture hup hcap
      have heq : pa = py := eq_of_le_of_height_ge hn hle (by omega)
      rw [← heq]
  obtain ⟨ks, his, hmins⟩ := hland sa hsa0
  have := hall pa hsa1 hsa0 ks his hmins
  exact hfix sa ks hsa0 hsa1 his hmins this

end Mordor.OrbitHeight
