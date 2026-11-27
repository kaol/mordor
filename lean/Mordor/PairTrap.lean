import Mordor.StairB1

/-!
# The pair staircase; CertAtom at N = 1 in every branch; TopRow and BoundedAtoms (§34.3z²⁹⁵, brief run 19)

* `pairStair` (three-row staircase): rows `x`, `y` with a common lower row `q`. Walk the boundary of
  `{(j, k) : v_j ⊓ w_k high}` (`v` = row `x`'s descent, `w` = row `y`'s). The value of row `q` at the boundary point of
  column `l` lies below `v_{l+1} ⊓ w_{κ(l)}`. If every boundary value of row `q` that lies below `p = λ(x)` equals `p`
  (`habs`) and `p` has height 2, then `p` lies below `λ(y)`.
* `certAtom_of_N1_all`: in W0, `N = 1` (`F(⊥, F(⊥, ⊤)) = ⊥`) gives a μ-fixed atom, whatever the height of `d`.
  If row `d` exits, `certAtom_of_N1_exit`. Otherwise `m = λ(d) ∈ Z`, `q = m ⊓ d` is an atom, every high `B` with
  `F(q, B) ≤ m` has `F(⊥, B) = q` (it lies below `m ⊓ d`), so `F(q, B) = m` by Tb at `q`; `pairStair` gives
  `m ≤ λ(m)`, so `λ(m) = m`, against `land_not_le`.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} [CompleteLattice α] {F : α →o α →o α}

/-- **Pair staircase.** -/
theorem pairStair {H : ℕ} (hn : NoChain α (H + 1)) {q x y : α} (hqx : q ≤ x) (hqy : q ≤ y)
    {i i' : ℕ} (hi : height H ((F x)^[i] (⊤ : α)) ≤ 2) (hmin : ∀ j < i, 2 < height H ((F x)^[j] (⊤ : α)))
    (hi' : height H ((F y)^[i'] (⊤ : α)) ≤ 2) (hmin' : ∀ j < i', 2 < height H ((F y)^[j] (⊤ : α)))
    (htop : 2 < height H (⊤ : α)) (hp2 : height H ((F x)^[i] (⊤ : α)) = 2)
    (habs : ∀ B, 2 < height H B → F q B ≤ (F x)^[i] (⊤ : α) → F q B = (F x)^[i] (⊤ : α)) :
    (F x)^[i] (⊤ : α) ≤ (F y)^[i'] (⊤ : α) := by
  classical
  set p := (F x)^[i] (⊤ : α) with hpdef
  let D : ℕ → ℕ → α := fun j k => (F x)^[j] (⊤ : α) ⊓ (F y)^[k] (⊤ : α)
  have hmono := (height_strictMono hn).monotone
  have hex : ∀ l, ∃ k, height H (D l k) ≤ 2 := fun l => ⟨i', le_trans (hmono inf_le_right) hi'⟩
  let κ : ℕ → ℕ := fun l => Nat.find (hex l)
  have hκlow : ∀ l, height H (D l (κ l)) ≤ 2 := fun l => Nat.find_spec (hex l)
  have hκmin : ∀ l k, k < κ l → 2 < height H (D l k) := fun l k hk => by
    have := Nat.find_min (hex l) hk; omega
  have hanti_x : ∀ {a b : ℕ}, a ≤ b → (F x)^[b] (⊤ : α) ≤ (F x)^[a] (⊤ : α) :=
    fun h => iter_antitone_of_le (F x).monotone (le_top : F x ⊤ ≤ ⊤) h
  have hanti_y : ∀ {a b : ℕ}, a ≤ b → (F y)^[b] (⊤ : α) ≤ (F y)^[a] (⊤ : α) :=
    fun h => iter_antitone_of_le (F y).monotone (le_top : F y ⊤ ≤ ⊤) h
  have hDk : ∀ l a b : ℕ, a ≤ b → D l b ≤ D l a := fun _ _ _ h => inf_le_inf_left _ (hanti_y h)
  have hDj : ∀ k a b : ℕ, a ≤ b → D b k ≤ D a k := fun _ _ _ h => inf_le_inf_right _ (hanti_x h)
  have hD0 : ∀ l, D l 0 = (F x)^[l] (⊤ : α) := fun l => by simp [D]
  have hD0' : ∀ k, D 0 k = (F y)^[k] (⊤ : α) := fun k => by simp [D]
  have hκpos : ∀ l, l < i → κ l ≠ 0 := fun l hl e => by
    have h0 := hκlow l; rw [e, hD0] at h0; have := hmin l hl; omega
  have hκanti : ∀ l, κ (l + 1) ≤ κ l := fun l =>
    Nat.find_min' (hex (l + 1)) (le_trans (hmono (hDj (κ l) _ _ (Nat.le_succ l))) (hκlow l))
  -- the boundary value at column `l`: row `q` at a high point, below the corner `D (l+1) (κ l)`
  have hbd : ∀ l, l < i → ∃ m, κ l = m + 1 ∧ 2 < height H (D l m) ∧ F q (D l m) ≤ D (l + 1) (m + 1) := by
    intro l hl
    refine ⟨κ l - 1, by have := hκpos l hl; omega, hκmin l _ (by have := hκpos l hl; omega), ?_⟩
    show F q (D l (κ l - 1)) ≤ (F x)^[l + 1] (⊤ : α) ⊓ (F y)^[κ l - 1 + 1] (⊤ : α)
    refine le_inf ?_ ?_
    · rw [Function.iterate_succ_apply']; exact ((F.mono hqx) _).trans ((F x).mono inf_le_left)
    · rw [Function.iterate_succ_apply']; exact ((F.mono hqy) _).trans ((F y).mono inf_le_right)
  -- a low element above `p` is `p`
  have hup : ∀ {c : α}, p ≤ c → height H c ≤ 2 → c = p := fun hpc hc =>
    (eq_of_le_of_height_ge hn hpc (by omega)).symm
  -- downward induction: every boundary value equals `p`
  have key : ∀ n l, l + n + 1 = i → ∃ m, κ l = m + 1 ∧ F q (D l m) = p := by
    intro n
    induction n with
    | zero =>
      intro l hl
      obtain ⟨m, hm, hhi, hle⟩ := hbd l (by omega)
      refine ⟨m, hm, habs _ hhi (hle.trans ?_)⟩
      have hl1 : l + 1 = i := by omega
      show D (l + 1) (m + 1) ≤ (F x)^[i] (⊤ : α)
      rw [← hl1]; exact inf_le_left
    | succ n ih =>
      intro l hl
      obtain ⟨m, hm, hhi, hle⟩ := hbd l (by omega)
      obtain ⟨m', hm', he'⟩ := ih (l + 1) (by omega)
      obtain ⟨m3, hm3, -, hle3⟩ := hbd (l + 1) (by omega)
      have hm3' : m3 = m' := by omega
      subst hm3'
      -- `p ≤ D (l+1) (κ (l+1))`, which is low, hence equal to `p`
      have hpc : p ≤ D (l + 1) (κ (l + 1)) := by
        rw [← he', hm3]; exact hle3.trans (hDj _ _ _ (Nat.le_succ _))
      have hc := hup hpc (hκlow (l + 1))
      have hle4 : F q (D l m) ≤ p := by
        rw [← hc]; exact hle.trans (by rw [← hm]; exact hDk (l + 1) _ _ (hκanti l))
      exact ⟨m, hm, habs _ hhi hle4⟩
  have hi0 : i ≠ 0 := land_index_pos htop hi
  obtain ⟨m, hm, he⟩ := key (i - 1) 0 (by omega)
  have hκ0 : κ 0 = i' := by
    apply le_antisymm
    · exact Nat.find_min' (hex 0) (by rw [hD0']; exact hi')
    · by_contra hc
      have := hmin' (κ 0) (by omega)
      have h1 := hκlow 0; rw [hD0'] at h1; omega
  obtain ⟨m0, hm0, -, hle0⟩ := hbd 0 (by omega)
  have hm0' : m0 = m := by omega
  subst hm0'
  calc p = F q (D 0 m0) := he.symm
    _ ≤ D 1 (m0 + 1) := hle0
    _ ≤ D 0 (m0 + 1) := hDj _ _ _ (Nat.zero_le 1)
    _ = (F y)^[i'] (⊤ : α) := by rw [hD0', ← hm0, hκ0]

/-- **CertAtom at N = 1, every branch.** In W0, if `F(⊥, F(⊥, ⊤)) = ⊥` then some atom of `R_1` is μ-fixed. -/
theorem certAtom_of_N1_all {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α)) (hd0 : F ⊥ (F ⊥ (⊤ : α)) = ⊥) :
    ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ i, height H ((F q)^[i] (⊤ : α)) ≤ 2 ∧
      (∀ j < i, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[i] (⊤ : α)) = q := by
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hk2 z (hR12 ((mem_one_iff ha).2 hz))
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  set d := F ⊥ (⊤ : α) with hddef
  have hdR : d ∈ Rk F 1 := (mem_one_iff ha).2 hd0
  obtain ⟨i, hi, hmin⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hdR))
  by_cases hex : F ⊥ ((F d)^[i] (⊤ : α)) ≠ ⊥
  · exact certAtom_of_N1_exit hn ha hk2 htop hd0 hi hmin hex
  exfalso
  push_neg at hex
  set m := (F d)^[i] (⊤ : α) with hmdef
  have hmR : m ∈ Rk F 1 := (mem_one_iff ha).2 hex
  obtain ⟨i', hi', hmin'⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hmR))
  have hmd : ¬ m ≤ d := land_not_le hk2 hdR htop hi hmin
  have hd2 : height H d ≤ 2 := hZT _ hd0
  have hm2 : height H m ≤ 2 := hi
  set q := m ⊓ d with hqdef
  have hqR : q ∈ Rk F 1 :=
    (mem_one_iff ha).2 (le_bot_iff.1 (((F ⊥).mono inf_le_right).trans (le_of_eq hd0)))
  -- every high `B` has `F(⊥, B) ≠ ⊥` and `F(⊥, B) ≤ d`
  have hne : ∀ B, 2 < height H B → F ⊥ B ≠ ⊥ := fun B hB h => by have := hZT B h; omega
  have hpos : ∀ {z : α}, z ≠ ⊥ → 1 ≤ height H z := fun hz => by
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hz); rw [height_bot_eq_zero] at this; omega
  -- the last high element `r` of row `d` gives `⊥ < F(⊥, r) ≤ q`
  have hi0 : i ≠ 0 := land_index_pos htop hi
  obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hrh : 2 < height H ((F d)^[k] (⊤ : α)) := hmin k (by omega)
  have hrm : F ⊥ ((F d)^[k] (⊤ : α)) ≤ m := by
    rw [hmdef, hk, Function.iterate_succ_apply']; exact (F.mono bot_le) _
  have hrq : F ⊥ ((F d)^[k] (⊤ : α)) ≤ q := le_inf hrm ((F ⊥).mono le_top)
  have hq1 : height H q = 1 := by
    have h1 : 1 ≤ height H q :=
      le_trans (hpos (hne _ hrh)) ((height_strictMono hn).monotone hrq)
    have h2 : height H q ≤ 2 := le_trans ((height_strictMono hn).monotone (inf_le_right : q ≤ d)) hd2
    rcases (show height H q = 1 ∨ height H q = 2 by omega) with h | h
    · exact h
    · exfalso
      have e1 : q = d := eq_of_le_of_height_ge hn inf_le_right (by omega)
      have e2 : q = m := eq_of_le_of_height_ge hn inf_le_left (by omega)
      exact hmd (e2 ▸ e1 ▸ le_rfl)
  have hmh : height H m = 2 := by
    have hqm : q < m := lt_of_le_of_ne inf_le_left (fun e => hmd (e ▸ inf_le_right))
    have := height_strictMono hn hqm; omega
  -- absorption: a boundary value of row `q` below `m` is `m`
  have habs : ∀ B, 2 < height H B → F q B ≤ m → F q B = m := by
    intro B hB hle
    have hb1 : F ⊥ B ≤ q := le_inf (((F.mono bot_le) B).trans hle) ((F ⊥).mono le_top)
    have hbq : F ⊥ B = q := eq_of_le_of_height_ge hn hb1 (by have := hpos (hne B hB); omega)
    have hqF : q ≤ F q B := hbq ▸ (F.mono bot_le) B
    have hlt : q < F q B := lt_of_le_of_ne hqF (fun e => tb_of_tight hk2 hqR B hB e.symm.le)
    have := height_strictMono hn hlt
    exact eq_of_le_of_height_ge hn hle (by omega)
  have hle : m ≤ (F m)^[i'] (⊤ : α) :=
    pairStair hn (inf_le_right : q ≤ d) (inf_le_left : q ≤ m) hi hmin hi' hmin' htop hmh habs
  have heq : m = (F m)^[i'] (⊤ : α) := eq_of_le_of_height_ge hn hle (by omega)
  exact land_not_le hk2 hmR htop hi' hmin' (le_of_eq heq.symm)

/-- **TopRow.** In W0, let `x` be any element whose row lands, and suppose every atom value of row `⊥` that lies in
`Z` lies below `x` (e.g. `F(⊥, ⊤) ≤ x`, or `x ∈ Z` above all of them). Then some atom of `R_1` is μ-fixed. If the landing `p` of row `x` lies outside `Z`, its exit
atom `F(⊥, p)` lies below `x` and is μ-fixed (`exitFixed_of_dom`); if `p ∈ Z`, `pairStair` with the value row `x ⊓ p`
gives `p ≤ λ(p)`, against `land_not_le`. -/
theorem certAtom_of_topRow {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α)) {x : α}
    (hA : ∀ w, height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → F ⊥ w ≤ x)
    {i : ℕ} (hi : height H ((F x)^[i] (⊤ : α)) ≤ 2) (hmin : ∀ j < i, 2 < height H ((F x)^[j] (⊤ : α))) :
    ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q := by
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hk2 z (hR12 ((mem_one_iff ha).2 hz))
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hne : ∀ B, 2 < height H B → F ⊥ B ≠ ⊥ := fun B hB h => by have := hZT B h; omega
  have hpos : ∀ {z : α}, z ≠ ⊥ → 1 ≤ height H z := fun hz => by
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hz); rw [height_bot_eq_zero] at this; omega
  have hmono := (height_strictMono hn).monotone
  set p := (F x)^[i] (⊤ : α) with hpdef
  have hi0 : i ≠ 0 := land_index_pos htop hi
  obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  set r := (F x)^[k] (⊤ : α) with hrdef
  have hrh : 2 < height H r := hmin k (by omega)
  have hpr : p = F x r := by rw [hpdef, hk, Function.iterate_succ_apply']
  have hrp : F ⊥ r ≤ p := hpr ▸ (F.mono bot_le) r
  have hple : p ≤ r := by
    rw [hpr]; have := iter_antitone_of_le (F x).monotone (le_top : F x ⊤ ≤ ⊤) (Nat.le_succ k)
    rwa [Function.iterate_succ_apply'] at this
  have hp0 : p ≠ ⊥ := fun e => hne r hrh (le_bot_iff.1 (e ▸ hrp))
  -- an element `z ≠ ⊥` with `z ≤ F(⊥, z)` is impossible (`a(⊥) = ⊥`)
  have hnofix : ∀ {z : α}, z ≤ F ⊥ z → z = ⊥ := fun h => le_bot_iff.1 (ha ▸ le_a h)
  by_cases hpZ : F ⊥ p = ⊥
  · exfalso
    have hpR : p ∈ Rk F 1 := (mem_one_iff ha).2 hpZ
    obtain ⟨i', hi', hmin'⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hpR))
    by_cases hpx : p ≤ x
    · exact tb_of_tight hk2 hpR r hrh (hpr ▸ (F.mono hpx) r)
    set q := x ⊓ p with hqdef
    have hqR : q ∈ Rk F 1 := (mem_one_iff ha).2 (le_bot_iff.1 (((F ⊥).mono inf_le_right).trans (le_of_eq hpZ)))
    have hqp : q < p := lt_of_le_of_ne inf_le_right (fun e => hpx (e ▸ inf_le_left))
    have hq1 : height H q ≤ 1 := by have := height_strictMono hn hqp; omega
    -- an atom value of row `⊥` below `p` is `q`
    have hatom : ∀ w, height H (F ⊥ w) = 1 → F ⊥ w ≤ p → F ⊥ w = q := fun w h1 hle =>
      eq_of_le_of_height_ge hn (le_inf (hA w h1 (le_bot_iff.1 (((F ⊥).mono hle).trans (le_of_eq hpZ)))) hle) (by omega)
    have hp2 : height H p = 2 := by
      rcases (show height H (F ⊥ r) = 1 ∨ 2 ≤ height H (F ⊥ r) by have := hpos (hne r hrh); omega) with h | h
      · have e := hatom r h hrp
        have hq0 : height H q = 1 := e ▸ h
        have h' := height_strictMono hn hqp
        omega
      · have := hmono hrp; omega
    have habs : ∀ B, 2 < height H B → F q B ≤ p → F q B = p := by
      intro B hB hle
      have hb : F ⊥ B ≤ p := ((F.mono bot_le) B).trans hle
      rcases (show height H (F ⊥ B) = 1 ∨ 2 ≤ height H (F ⊥ B) by have := hpos (hne B hB); omega) with h | h
      · have hbq := hatom B h hb
        have hqF : q ≤ F q B := hbq ▸ (F.mono bot_le) B
        have hlt : q < F q B := lt_of_le_of_ne hqF (fun e => tb_of_tight hk2 hqR B hB e.symm.le)
        have hq1' : height H q = 1 := hbq ▸ h
        have := height_strictMono hn hlt
        exact eq_of_le_of_height_ge hn hle (by omega)
      · have e : F ⊥ B = p := eq_of_le_of_height_ge hn hb (by omega)
        exact le_antisymm hle (e ▸ (F.mono bot_le) B)
    have hle := pairStair hn (inf_le_left : q ≤ x) (inf_le_right : q ≤ p) hi hmin hi' hmin' htop hp2 habs
    have heq : p = (F p)^[i'] (⊤ : α) := eq_of_le_of_height_ge hn hle (by omega)
    exact land_not_le hk2 hpR htop hi' hmin' (le_of_eq heq.symm)
  · -- `p ∉ Z`: its exit atom `c = F(⊥, p)` lies below `x` and is μ-fixed
    set c := F ⊥ p with hcdef
    have hcp : c ≤ p := ((F ⊥).mono hple).trans hrp
    have hcne : c ≠ p := fun e => hp0 (hnofix (le_of_eq e.symm))
    have hc0 : 1 ≤ height H c := hpos hpZ
    have hcp' := height_strictMono hn (lt_of_le_of_ne hcp hcne)
    have hp2 : height H p = 2 := by omega
    have hc1 : height H c = 1 := by omega
    have hcc : F ⊥ c ≤ c := (F ⊥).mono hcp
    have hc00 : F ⊥ c = ⊥ := by
      by_contra hb
      have h1 := hpos hb
      have e : F ⊥ c = c := eq_of_le_of_height_ge hn hcc (by omega)
      exact hpZ (hnofix (le_of_eq e.symm))
    have hcR : c ∈ Rk F 1 := (mem_one_iff ha).2 hc00
    have hcx : c ≤ x := hA p hc1 hc00
    obtain ⟨k', hk', hmink', hfix⟩ := exitFixed_of_dom hn hk2 (rfl : (F x)^[i] (⊤ : α) = p) hp2 hc1 hcR hcx rfl
    exact ⟨c, hcR, hc1, k', by rw [hk']; omega, hmink', hfix⟩

theorem certAtom_of_topRow' {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α)) {x : α}
    {i : ℕ} (hi : height H ((F x)^[i] (⊤ : α)) ≤ 2) (hmin : ∀ j < i, 2 < height H ((F x)^[j] (⊤ : α)))
    (hA : ∀ w, height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → F ⊥ w ≤ (F x)^[i] (⊤ : α) → F ⊥ w ≤ x) :
    ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q := by
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hk2 z (hR12 ((mem_one_iff ha).2 hz))
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hne : ∀ B, 2 < height H B → F ⊥ B ≠ ⊥ := fun B hB h => by have := hZT B h; omega
  have hpos : ∀ {z : α}, z ≠ ⊥ → 1 ≤ height H z := fun hz => by
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hz); rw [height_bot_eq_zero] at this; omega
  have hmono := (height_strictMono hn).monotone
  set p := (F x)^[i] (⊤ : α) with hpdef
  have hi0 : i ≠ 0 := land_index_pos htop hi
  obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  set r := (F x)^[k] (⊤ : α) with hrdef
  have hrh : 2 < height H r := hmin k (by omega)
  have hpr : p = F x r := by rw [hpdef, hk, Function.iterate_succ_apply']
  have hrp : F ⊥ r ≤ p := hpr ▸ (F.mono bot_le) r
  have hple : p ≤ r := by
    rw [hpr]; have := iter_antitone_of_le (F x).monotone (le_top : F x ⊤ ≤ ⊤) (Nat.le_succ k)
    rwa [Function.iterate_succ_apply'] at this
  have hp0 : p ≠ ⊥ := fun e => hne r hrh (le_bot_iff.1 (e ▸ hrp))
  -- an element `z ≠ ⊥` with `z ≤ F(⊥, z)` is impossible (`a(⊥) = ⊥`)
  have hnofix : ∀ {z : α}, z ≤ F ⊥ z → z = ⊥ := fun h => le_bot_iff.1 (ha ▸ le_a h)
  by_cases hpZ : F ⊥ p = ⊥
  · exfalso
    have hpR : p ∈ Rk F 1 := (mem_one_iff ha).2 hpZ
    obtain ⟨i', hi', hmin'⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hpR))
    by_cases hpx : p ≤ x
    · exact tb_of_tight hk2 hpR r hrh (hpr ▸ (F.mono hpx) r)
    set q := x ⊓ p with hqdef
    have hqR : q ∈ Rk F 1 := (mem_one_iff ha).2 (le_bot_iff.1 (((F ⊥).mono inf_le_right).trans (le_of_eq hpZ)))
    have hqp : q < p := lt_of_le_of_ne inf_le_right (fun e => hpx (e ▸ inf_le_left))
    have hq1 : height H q ≤ 1 := by have := height_strictMono hn hqp; omega
    -- an atom value of row `⊥` below `p` is `q`
    have hatom : ∀ w, height H (F ⊥ w) = 1 → F ⊥ w ≤ p → F ⊥ w = q := fun w h1 hle =>
      eq_of_le_of_height_ge hn (le_inf (hA w h1 (le_bot_iff.1 (((F ⊥).mono hle).trans (le_of_eq hpZ))) hle) hle) (by omega)
    have hp2 : height H p = 2 := by
      rcases (show height H (F ⊥ r) = 1 ∨ 2 ≤ height H (F ⊥ r) by have := hpos (hne r hrh); omega) with h | h
      · have e := hatom r h hrp
        have hq0 : height H q = 1 := e ▸ h
        have h' := height_strictMono hn hqp
        omega
      · have := hmono hrp; omega
    have habs : ∀ B, 2 < height H B → F q B ≤ p → F q B = p := by
      intro B hB hle
      have hb : F ⊥ B ≤ p := ((F.mono bot_le) B).trans hle
      rcases (show height H (F ⊥ B) = 1 ∨ 2 ≤ height H (F ⊥ B) by have := hpos (hne B hB); omega) with h | h
      · have hbq := hatom B h hb
        have hqF : q ≤ F q B := hbq ▸ (F.mono bot_le) B
        have hlt : q < F q B := lt_of_le_of_ne hqF (fun e => tb_of_tight hk2 hqR B hB e.symm.le)
        have hq1' : height H q = 1 := hbq ▸ h
        have := height_strictMono hn hlt
        exact eq_of_le_of_height_ge hn hle (by omega)
      · have e : F ⊥ B = p := eq_of_le_of_height_ge hn hb (by omega)
        exact le_antisymm hle (e ▸ (F.mono bot_le) B)
    have hle := pairStair hn (inf_le_left : q ≤ x) (inf_le_right : q ≤ p) hi hmin hi' hmin' htop hp2 habs
    have heq : p = (F p)^[i'] (⊤ : α) := eq_of_le_of_height_ge hn hle (by omega)
    exact land_not_le hk2 hpR htop hi' hmin' (le_of_eq heq.symm)
  · -- `p ∉ Z`: its exit atom `c = F(⊥, p)` lies below `x` and is μ-fixed
    set c := F ⊥ p with hcdef
    have hcp : c ≤ p := ((F ⊥).mono hple).trans hrp
    have hcne : c ≠ p := fun e => hp0 (hnofix (le_of_eq e.symm))
    have hc0 : 1 ≤ height H c := hpos hpZ
    have hcp' := height_strictMono hn (lt_of_le_of_ne hcp hcne)
    have hp2 : height H p = 2 := by omega
    have hc1 : height H c = 1 := by omega
    have hcc : F ⊥ c ≤ c := (F ⊥).mono hcp
    have hc00 : F ⊥ c = ⊥ := by
      by_contra hb
      have h1 := hpos hb
      have e : F ⊥ c = c := eq_of_le_of_height_ge hn hcc (by omega)
      exact hpZ (hnofix (le_of_eq e.symm))
    have hcR : c ∈ Rk F 1 := (mem_one_iff ha).2 hc00
    have hcx : c ≤ x := hA p hc1 hc00 hcp
    obtain ⟨k', hk', hmink', hfix⟩ := exitFixed_of_dom hn hk2 (rfl : (F x)^[i] (⊤ : α) = p) hp2 hc1 hcR hcx rfl
    exact ⟨c, hcR, hc1, k', by rw [hk']; omega, hmink', hfix⟩

/-- **ColourGain.** In W0 with no μ-fixed atom of `R_1`, every element `x` whose row lands at `p` has a colour atom
below `p` and not below `x`: an atom `c = F(⊥, w)` of `Z` with `c ≤ p`, `c ≰ x`. (Contrapositive of TopRow′, which uses
only the colour atoms below the landing.) -/
theorem colourGain {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    (hno : ¬ ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q)
    {x : α} {i : ℕ} (hi : height H ((F x)^[i] (⊤ : α)) ≤ 2) (hmin : ∀ j < i, 2 < height H ((F x)^[j] (⊤ : α))) :
    ∃ w, height H (F ⊥ w) = 1 ∧ F ⊥ (F ⊥ w) = ⊥ ∧ F ⊥ w ≤ (F x)^[i] (⊤ : α) ∧ ¬ F ⊥ w ≤ x := by
  by_contra hc
  push_neg at hc
  exact hno (certAtom_of_topRow' hn ha hk2 htop hi hmin hc)

/-- CertAtom at `N = 1` as a corollary of TopRow (`x = d = F(⊥, ⊤)`), in the form of the `CertAtom` definition. -/
theorem certAtom_N1 {H : ℕ} (hn : NoChain α (H + 1)) (hd0 : F ⊥ (F ⊥ (⊤ : α)) = ⊥) : CertAtom F H := by
  intro ha hk2 htR hnt
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have htop : 2 < height H (⊤ : α) := by
    obtain ⟨z, hzR, hz1⟩ : ∃ z ∈ Rk F 1, 1 < height H z := by
      by_contra hc; push_neg at hc; exact hnt hc
    have hz2 : height H z ≤ 2 := hk2 z (hR12 hzR)
    have hzt : z ≠ ⊤ := fun e => htR (e ▸ hR12 hzR)
    have := height_strictMono hn (lt_of_le_of_ne le_top hzt); omega
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hdR : F ⊥ (⊤ : α) ∈ Rk F 1 := (mem_one_iff ha).2 hd0
  obtain ⟨i, hi, hmin⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hdR))
  exact certAtom_of_topRow hn ha hk2 htop (fun w _ _ => (F ⊥).mono le_top) hi hmin

/-- **Bounded colour atoms.** In W0 (any `N`): if some `x ∈ Z` lies above every atom of `Z` that is a value of row `⊥`,
then some atom of `R_1` is μ-fixed (TopRow with the row of `x`, which lands by Ta). -/
theorem certAtom_of_boundedAtoms {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α)) {x : α} (hx : F ⊥ x = ⊥)
    (hA : ∀ w, height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → F ⊥ w ≤ x) :
    ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q := by
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  obtain ⟨i, hi, hmin⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ ((mem_one_iff ha).2 hx)))
  exact certAtom_of_topRow hn ha hk2 htop hA hi hmin

end Mordor.OrbitHeight
