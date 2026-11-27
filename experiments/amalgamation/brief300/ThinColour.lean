import Mordor.TwoColourShadow

/-!
# CertAtom when no element of `Z` lies above two colours (brief run 25, briefer's scratch file)

Setting: W0 (`a(⊥) = ⊥`, `R_2` tight, `2 < h(⊤)`).  A *colour* is `F(⊥, w)` with `height = 1` and `F(⊥, F(⊥, w)) = ⊥`.
**Thin**: no element of `Z = F(⊥, ·)⁻¹(⊥)` lies above two distinct colours.

* `land_capture` (GK0): if `c` lies below the landing `(F x)^[i] ⊤` and `A ≤ F(⊥, A) ⊔ c`, then `A` lies below it too.
* `phi_low_colour`: for low `A ∉ Z` with `F(⊥, A) ≤ A`, `F(⊥, A)` is a colour and `h(A) = 2`.
* `shadow_start`: under NoFix the last high element `r` of a landing row `y` of `R_1` has a colour below `F(⊥, r)`
  and below `λ(y)`.
* `thinStair` (SCL, thin form): for landing rows `x`, `y` (any elements), walking the `pairStair` staircase with value
  row `⊥` carries "some colour of `λ(y)` lies below the boundary value", so some colour below `λ(y)` lies below
  `F(⊥, r_x)`.
* `colourStair` (SCL, general form): the same walk with thinness replaced by NoPairBreak at the corners of this one
  staircase (a corner in `Z` carrying a colour of `λ(y)` carries only colours of `λ(y)`).
* `certAtom_of_thin`: in W0, thin ⟹ some atom of `R_1` is μ-fixed.  (Two unbounded colours are thin, so this
  re-proves `certAtom_of_twoColours`; any number of colours is allowed.)
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} [CompleteLattice α] {F : α →o α →o α}

/-- **GK0 (capture).** If `c` lies below `(F x)^[i] ⊤` and `A ≤ F(⊥, A) ⊔ c`, then `A ≤ (F x)^[i] ⊤`. -/
theorem land_capture {x c A : α} {i : ℕ} (hci : c ≤ (F x)^[i] (⊤ : α)) (hA : A ≤ F ⊥ A ⊔ c) :
    A ≤ (F x)^[i] (⊤ : α) := by
  have hanti : ∀ j, j < i → c ≤ (F x)^[j+1] (⊤ : α) := fun j hj =>
    hci.trans (iter_antitone_of_le (F x).monotone (le_top : F x ⊤ ≤ ⊤) (by omega))
  have hQ : A ≤ F x A ⊔ c := hA.trans (sup_le_sup_right ((F.mono bot_le) A) c)
  exact desc_ge_of_postfixed hanti hQ i le_rfl

/-- Two distinct atoms below an element of height at most 2 join to it. -/
theorem join_of_two_atoms {H : ℕ} (hn : NoChain α (H + 1)) {c c' A : α} (hc : height H c = 1)
    (hc' : height H c' = 1) (hne : c ≠ c') (hcA : c ≤ A) (hc'A : c' ≤ A) (hA : height H A ≤ 2) :
    A = c ⊔ c' ∧ height H A = 2 := by
  have hlt : c < c ⊔ c' := by
    refine lt_of_le_of_ne le_sup_left (fun e => hne ?_)
    have hba : c' ≤ c := e ▸ le_sup_right
    exact (eq_of_le_of_height_ge hn hba (by omega)).symm
  have h2 : 2 ≤ height H (c ⊔ c') := by have := height_strictMono hn hlt; omega
  have hle : c ⊔ c' ≤ A := sup_le hcA hc'A
  have e := eq_of_le_of_height_ge hn hle (by omega)
  exact ⟨e.symm, by rw [← e]; have := (height_strictMono hn).monotone hle; omega⟩

/-- For a low `A ∉ Z` with `F(⊥, A) ≤ A`: `F(⊥, A)` is a colour and `h(A) = 2`. -/
theorem phi_low_colour {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥) {A : α} (hAl : height H A ≤ 2)
    (hA0 : F ⊥ A ≠ ⊥) (hle : F ⊥ A ≤ A) :
    height H (F ⊥ A) = 1 ∧ F ⊥ (F ⊥ A) = ⊥ ∧ height H A = 2 := by
  have hnofix : ∀ {z : α}, z ≤ F ⊥ z → z = ⊥ := fun h => le_bot_iff.1 (ha ▸ le_a h)
  have hpos : ∀ {z : α}, z ≠ ⊥ → 1 ≤ height H z := fun hz => by
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hz); rw [height_bot_eq_zero] at this; omega
  have hA00 : A ≠ ⊥ := fun e => hA0 (le_bot_iff.1 (e ▸ hle))
  have hφne : F ⊥ A ≠ A := fun e => hA00 (hnofix (le_of_eq e.symm))
  have hlt := height_strictMono hn (lt_of_le_of_ne hle hφne)
  have h1 := hpos hA0
  have hφφ : F ⊥ (F ⊥ A) = ⊥ := by
    by_contra hb
    have h1' := hpos hb
    have hle' : F ⊥ (F ⊥ A) ≤ F ⊥ A := (F ⊥).mono hle
    have e : F ⊥ (F ⊥ A) = F ⊥ A := eq_of_le_of_height_ge hn hle' (by omega)
    exact hA0 (hnofix (le_of_eq e.symm))
  exact ⟨by omega, hφφ, by omega⟩

/-- **Shadow start.** Under NoFix, a landing row `y ∈ R_1` (landing index `k' + 1`) has a colour below `λ(y)` and
below `F(⊥, r_y)`, `r_y = (F y)^[k'] ⊤`. -/
theorem shadow_start {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    (hno : ¬ ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q)
    {y : α} {k' : ℕ} (hi' : height H ((F y)^[k' + 1] (⊤ : α)) ≤ 2)
    (hmin' : ∀ j < k' + 1, 2 < height H ((F y)^[j] (⊤ : α))) :
    ∃ w, height H (F ⊥ w) = 1 ∧ F ⊥ (F ⊥ w) = ⊥ ∧ F ⊥ w ≤ (F y)^[k' + 1] (⊤ : α) ∧
      F ⊥ w ≤ F ⊥ ((F y)^[k'] (⊤ : α)) := by
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hk2 z (hR12 ((mem_one_iff ha).2 hz))
  have hpos : ∀ {z : α}, z ≠ ⊥ → 1 ≤ height H z := fun hz => by
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hz); rw [height_bot_eq_zero] at this; omega
  set p := (F y)^[k' + 1] (⊤ : α) with hpdef
  set r := (F y)^[k'] (⊤ : α) with hrdef
  have hpr : p = F y r := by rw [hpdef, hrdef, Function.iterate_succ_apply']
  have hple : p ≤ r := by
    have := iter_antitone_of_le (F y).monotone (le_top : F y ⊤ ≤ ⊤) (Nat.le_succ k')
    rw [hpdef, hrdef]; exact this
  have hsp : F ⊥ r ≤ p := hpr ▸ (F.mono bot_le) r
  have hrh : 2 < height H r := hmin' k' (by omega)
  have hs0 : F ⊥ r ≠ ⊥ := fun h => by have := hZT r h; omega
  by_cases hpZ : F ⊥ p = ⊥
  · have hsZ : F ⊥ (F ⊥ r) = ⊥ := le_bot_iff.1 (((F ⊥).mono hsp).trans (le_of_eq hpZ))
    rcases (show height H (F ⊥ r) = 1 ∨ height H (F ⊥ r) = 2 by
        have := hpos hs0; have := (height_strictMono hn).monotone hsp; omega) with h1 | h2
    · exact ⟨r, h1, hsZ, hsp, le_rfl⟩
    · have e : F ⊥ r = p := eq_of_le_of_height_ge hn hsp (by omega)
      obtain ⟨w, hw1, hw0, hwp, -⟩ := colourGain hn ha hk2 htop hno hi' hmin'
      exact ⟨w, hw1, hw0, hwp, e ▸ hwp⟩
  · have hφp : F ⊥ p ≤ p := ((F ⊥).mono hple).trans hsp
    obtain ⟨h1, h0, -⟩ := phi_low_colour hn ha hi' hpZ hφp
    exact ⟨p, h1, h0, hφp, (F ⊥).mono hple⟩

/-- **Colour staircase (SCL, general form).** As `thinStair`, with thinness replaced by `hnb` (NoPairBreak at the
corners of this staircase): whenever a corner `(F x)^[j] ⊤ ⊓ (F y)^[k] ⊤` lies in `Z` and carries two colours, one
below `λ(y)`, the other is below `λ(y)` too. -/
theorem colourStair {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2)
    {x y : α} {k k' : ℕ}
    (hnb : ∀ (j m : ℕ) (w w' : α), F ⊥ ((F x)^[j] (⊤ : α) ⊓ (F y)^[m] (⊤ : α)) = ⊥ →
      height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → height H (F ⊥ w') = 1 → F ⊥ (F ⊥ w') = ⊥ →
      F ⊥ w ≤ (F x)^[j] (⊤ : α) ⊓ (F y)^[m] (⊤ : α) → F ⊥ w' ≤ (F x)^[j] (⊤ : α) ⊓ (F y)^[m] (⊤ : α) →
      F ⊥ w ≤ (F y)^[k' + 1] (⊤ : α) → F ⊥ w' ≤ (F y)^[k' + 1] (⊤ : α))
    (hmin : ∀ j < k + 1, 2 < height H ((F x)^[j] (⊤ : α)))
    (hi' : height H ((F y)^[k' + 1] (⊤ : α)) ≤ 2) (hmin' : ∀ j < k' + 1, 2 < height H ((F y)^[j] (⊤ : α)))
    (hstart : ∃ w, height H (F ⊥ w) = 1 ∧ F ⊥ (F ⊥ w) = ⊥ ∧ F ⊥ w ≤ (F y)^[k' + 1] (⊤ : α) ∧
      F ⊥ w ≤ F ⊥ ((F y)^[k'] (⊤ : α))) :
    ∃ w, height H (F ⊥ w) = 1 ∧ F ⊥ (F ⊥ w) = ⊥ ∧ F ⊥ w ≤ (F y)^[k' + 1] (⊤ : α) ∧
      F ⊥ w ≤ F ⊥ ((F x)^[k] (⊤ : α)) := by
  classical
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hk2 z (hR12 ((mem_one_iff ha).2 hz))
  have hne : ∀ B, 2 < height H B → F ⊥ B ≠ ⊥ := fun B hB h => by have := hZT B h; omega
  have hpos : ∀ {z : α}, z ≠ ⊥ → 1 ≤ height H z := fun hz => by
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hz); rw [height_bot_eq_zero] at this; omega
  have hmono := (height_strictMono hn).monotone
  set p' := (F y)^[k' + 1] (⊤ : α) with hp'def
  have hanti_a : ∀ {s t : ℕ}, s ≤ t → (F x)^[t] (⊤ : α) ≤ (F x)^[s] (⊤ : α) :=
    fun h => iter_antitone_of_le (F x).monotone (le_top : F x ⊤ ≤ ⊤) h
  have hanti_b : ∀ {s t : ℕ}, s ≤ t → (F y)^[t] (⊤ : α) ≤ (F y)^[s] (⊤ : α) :=
    fun h => iter_antitone_of_le (F y).monotone (le_top : F y ⊤ ≤ ⊤) h
  -- the staircase of rows `x` and `y`
  let D : ℕ → ℕ → α := fun j k => (F x)^[j] (⊤ : α) ⊓ (F y)^[k] (⊤ : α)
  have hex : ∀ l, ∃ k, height H (D l k) ≤ 2 := fun l => ⟨k' + 1, le_trans (hmono inf_le_right) hi'⟩
  let κ : ℕ → ℕ := fun l => Nat.find (hex l)
  have hκlow : ∀ l, height H (D l (κ l)) ≤ 2 := fun l => Nat.find_spec (hex l)
  have hκmin : ∀ l k, k < κ l → 2 < height H (D l k) := fun l k hk => by
    have := Nat.find_min (hex l) hk; omega
  have hDk : ∀ l s t : ℕ, s ≤ t → D l t ≤ D l s := fun _ _ _ h => inf_le_inf_left _ (hanti_b h)
  have hDj : ∀ k s t : ℕ, s ≤ t → D t k ≤ D s k := fun _ _ _ h => inf_le_inf_right _ (hanti_a h)
  have hD0 : ∀ l, D l 0 = (F x)^[l] (⊤ : α) := fun l => by simp [D]
  have hD0' : ∀ k, D 0 k = (F y)^[k] (⊤ : α) := fun k => by simp [D]
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
  have hbd : ∀ l, l < k + 1 → F ⊥ (D l (κ l - 1)) ≤ D (l + 1) (κ l) := by
    intro l hl
    have hk1 : κ l = κ l - 1 + 1 := by have := hκpos l hl; omega
    show F ⊥ (D l (κ l - 1)) ≤ (F x)^[l + 1] (⊤ : α) ⊓ (F y)^[κ l] (⊤ : α)
    refine le_inf ?_ ?_
    · rw [Function.iterate_succ_apply']
      exact ((F ⊥).mono inf_le_left).trans ((F.mono bot_le) _)
    · rw [hk1, Function.iterate_succ_apply']
      exact ((F ⊥).mono inf_le_right).trans ((F.mono bot_le) _)
  -- forward induction: some colour below `λ(y)` lies below every boundary value
  have key : ∀ l, l < k + 1 → ∃ w, height H (F ⊥ w) = 1 ∧ F ⊥ (F ⊥ w) = ⊥ ∧ F ⊥ w ≤ p' ∧
      F ⊥ w ≤ F ⊥ (D l (κ l - 1)) := by
    intro l
    induction l with
    | zero =>
      intro _
      rw [hκ0, show k' + 1 - 1 = k' by omega, hD0']; exact hstart
    | succ l ih =>
      intro hl
      obtain ⟨w, hw1, hw0, hwp, hwe⟩ := ih (by omega)
      set A := D (l + 1) (κ (l + 1)) with hAdef
      set B := D (l + 1) (κ (l + 1) - 1) with hBdef
      have hk1 : κ (l + 1) - 1 < κ (l + 1) := by have := hκpos (l + 1) hl; omega
      have hBh : 2 < height H B := hκmin (l + 1) _ hk1
      have hAl : height H A ≤ 2 := hκlow (l + 1)
      have hAB : A ≤ B := hDk (l + 1) _ _ (Nat.sub_le _ 1)
      have hcA : F ⊥ w ≤ A := hwe.trans ((hbd l (by omega)).trans (hDk (l + 1) _ _ (hκanti l)))
      have heA : F ⊥ B ≤ A := (hbd (l + 1) hl).trans (hDj _ _ _ (Nat.le_succ _))
      have hφA : F ⊥ A ≤ F ⊥ B := (F ⊥).mono hAB
      have heB0 := hne B hBh
      by_cases hA0 : F ⊥ A = ⊥
      · -- `A ∈ Z`: the boundary value is the colour of `A` or `A` itself
        have he0' : F ⊥ (F ⊥ B) = ⊥ := le_bot_iff.1 (((F ⊥).mono heA).trans (le_of_eq hA0))
        rcases (show height H (F ⊥ B) = 1 ∨ height H (F ⊥ B) = 2 by
            have := hpos heB0; have := hmono heA; omega) with h | h
        · exact ⟨B, h, he0', hnb (l + 1) (κ (l + 1)) w B hA0 hw1 hw0 h he0' hcA heA hwp, le_rfl⟩
        · have e : F ⊥ B = A := eq_of_le_of_height_ge hn heA (by omega)
          exact ⟨w, hw1, hw0, hwp, e ▸ hcA⟩
      · -- `A ∉ Z`: `F(⊥, A)` is a colour; if it is not below `λ(y)`, capture puts `A` below `λ(y)`
        have hφAA : F ⊥ A ≤ A := hφA.trans heA
        obtain ⟨hφ1, hφφ, hA2⟩ := phi_low_colour hn ha hAl hA0 hφAA
        by_cases hc : F ⊥ A ≤ p'
        · exact ⟨A, hφ1, hφφ, hc, hφA⟩
        · exfalso
          have hne' : F ⊥ w ≠ F ⊥ A := fun e => hc (e ▸ hwp)
          obtain ⟨hJ, -⟩ := join_of_two_atoms hn hw1 hφ1 hne' hcA hφAA hAl
          have hcap : A ≤ F ⊥ A ⊔ F ⊥ w := hJ.le.trans (sup_le le_sup_right le_sup_left)
          exact hc (hφAA.trans (land_capture hwp hcap))
  obtain ⟨w, hw1, hw0, hwp, hwe⟩ := key k (by omega)
  exact ⟨w, hw1, hw0, hwp, hwe.trans ((F ⊥).mono inf_le_left)⟩

/-- **Thin staircase (SCL).** In W0 with thin colours, for landing rows `x` (index `k + 1`) and `y` (index `k' + 1`),
if some colour below `λ(y)` lies below `F(⊥, r_y)`, then some colour below `λ(y)` lies below `F(⊥, r_x)`. -/
theorem thinStair {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2)
    (hthin : ∀ z w w', F ⊥ z = ⊥ → height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → height H (F ⊥ w') = 1 →
      F ⊥ (F ⊥ w') = ⊥ → F ⊥ w ≤ z → F ⊥ w' ≤ z → F ⊥ w = F ⊥ w')
    {x y : α} {k k' : ℕ}
    (hmin : ∀ j < k + 1, 2 < height H ((F x)^[j] (⊤ : α)))
    (hi' : height H ((F y)^[k' + 1] (⊤ : α)) ≤ 2) (hmin' : ∀ j < k' + 1, 2 < height H ((F y)^[j] (⊤ : α)))
    (hstart : ∃ w, height H (F ⊥ w) = 1 ∧ F ⊥ (F ⊥ w) = ⊥ ∧ F ⊥ w ≤ (F y)^[k' + 1] (⊤ : α) ∧
      F ⊥ w ≤ F ⊥ ((F y)^[k'] (⊤ : α))) :
    ∃ w, height H (F ⊥ w) = 1 ∧ F ⊥ (F ⊥ w) = ⊥ ∧ F ⊥ w ≤ (F y)^[k' + 1] (⊤ : α) ∧
      F ⊥ w ≤ F ⊥ ((F x)^[k] (⊤ : α)) := by
  classical
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hk2 z (hR12 ((mem_one_iff ha).2 hz))
  have hne : ∀ B, 2 < height H B → F ⊥ B ≠ ⊥ := fun B hB h => by have := hZT B h; omega
  have hpos : ∀ {z : α}, z ≠ ⊥ → 1 ≤ height H z := fun hz => by
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hz); rw [height_bot_eq_zero] at this; omega
  have hmono := (height_strictMono hn).monotone
  set p' := (F y)^[k' + 1] (⊤ : α) with hp'def
  have hanti_a : ∀ {s t : ℕ}, s ≤ t → (F x)^[t] (⊤ : α) ≤ (F x)^[s] (⊤ : α) :=
    fun h => iter_antitone_of_le (F x).monotone (le_top : F x ⊤ ≤ ⊤) h
  have hanti_b : ∀ {s t : ℕ}, s ≤ t → (F y)^[t] (⊤ : α) ≤ (F y)^[s] (⊤ : α) :=
    fun h => iter_antitone_of_le (F y).monotone (le_top : F y ⊤ ≤ ⊤) h
  -- the staircase of rows `x` and `y`
  let D : ℕ → ℕ → α := fun j k => (F x)^[j] (⊤ : α) ⊓ (F y)^[k] (⊤ : α)
  have hex : ∀ l, ∃ k, height H (D l k) ≤ 2 := fun l => ⟨k' + 1, le_trans (hmono inf_le_right) hi'⟩
  let κ : ℕ → ℕ := fun l => Nat.find (hex l)
  have hκlow : ∀ l, height H (D l (κ l)) ≤ 2 := fun l => Nat.find_spec (hex l)
  have hκmin : ∀ l k, k < κ l → 2 < height H (D l k) := fun l k hk => by
    have := Nat.find_min (hex l) hk; omega
  have hDk : ∀ l s t : ℕ, s ≤ t → D l t ≤ D l s := fun _ _ _ h => inf_le_inf_left _ (hanti_b h)
  have hDj : ∀ k s t : ℕ, s ≤ t → D t k ≤ D s k := fun _ _ _ h => inf_le_inf_right _ (hanti_a h)
  have hD0 : ∀ l, D l 0 = (F x)^[l] (⊤ : α) := fun l => by simp [D]
  have hD0' : ∀ k, D 0 k = (F y)^[k] (⊤ : α) := fun k => by simp [D]
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
  have hbd : ∀ l, l < k + 1 → F ⊥ (D l (κ l - 1)) ≤ D (l + 1) (κ l) := by
    intro l hl
    have hk1 : κ l = κ l - 1 + 1 := by have := hκpos l hl; omega
    show F ⊥ (D l (κ l - 1)) ≤ (F x)^[l + 1] (⊤ : α) ⊓ (F y)^[κ l] (⊤ : α)
    refine le_inf ?_ ?_
    · rw [Function.iterate_succ_apply']
      exact ((F ⊥).mono inf_le_left).trans ((F.mono bot_le) _)
    · rw [hk1, Function.iterate_succ_apply']
      exact ((F ⊥).mono inf_le_right).trans ((F.mono bot_le) _)
  -- forward induction: some colour below `λ(y)` lies below every boundary value
  have key : ∀ l, l < k + 1 → ∃ w, height H (F ⊥ w) = 1 ∧ F ⊥ (F ⊥ w) = ⊥ ∧ F ⊥ w ≤ p' ∧
      F ⊥ w ≤ F ⊥ (D l (κ l - 1)) := by
    intro l
    induction l with
    | zero =>
      intro _
      rw [hκ0, show k' + 1 - 1 = k' by omega, hD0']; exact hstart
    | succ l ih =>
      intro hl
      obtain ⟨w, hw1, hw0, hwp, hwe⟩ := ih (by omega)
      set A := D (l + 1) (κ (l + 1)) with hAdef
      set B := D (l + 1) (κ (l + 1) - 1) with hBdef
      have hk1 : κ (l + 1) - 1 < κ (l + 1) := by have := hκpos (l + 1) hl; omega
      have hBh : 2 < height H B := hκmin (l + 1) _ hk1
      have hAl : height H A ≤ 2 := hκlow (l + 1)
      have hAB : A ≤ B := hDk (l + 1) _ _ (Nat.sub_le _ 1)
      have hcA : F ⊥ w ≤ A := hwe.trans ((hbd l (by omega)).trans (hDk (l + 1) _ _ (hκanti l)))
      have heA : F ⊥ B ≤ A := (hbd (l + 1) hl).trans (hDj _ _ _ (Nat.le_succ _))
      have hφA : F ⊥ A ≤ F ⊥ B := (F ⊥).mono hAB
      have heB0 := hne B hBh
      by_cases hA0 : F ⊥ A = ⊥
      · -- `A ∈ Z`: the boundary value is the colour of `A` or `A` itself
        have he0' : F ⊥ (F ⊥ B) = ⊥ := le_bot_iff.1 (((F ⊥).mono heA).trans (le_of_eq hA0))
        rcases (show height H (F ⊥ B) = 1 ∨ height H (F ⊥ B) = 2 by
            have := hpos heB0; have := hmono heA; omega) with h | h
        · have e := hthin A B w hA0 h he0' hw1 hw0 heA hcA
          exact ⟨w, hw1, hw0, hwp, le_of_eq e.symm⟩
        · have e : F ⊥ B = A := eq_of_le_of_height_ge hn heA (by omega)
          exact ⟨w, hw1, hw0, hwp, e ▸ hcA⟩
      · -- `A ∉ Z`: `F(⊥, A)` is a colour; if it is not below `λ(y)`, capture puts `A` below `λ(y)`
        have hφAA : F ⊥ A ≤ A := hφA.trans heA
        obtain ⟨hφ1, hφφ, hA2⟩ := phi_low_colour hn ha hAl hA0 hφAA
        by_cases hc : F ⊥ A ≤ p'
        · exact ⟨A, hφ1, hφφ, hc, hφA⟩
        · exfalso
          have hne' : F ⊥ w ≠ F ⊥ A := fun e => hc (e ▸ hwp)
          obtain ⟨hJ, -⟩ := join_of_two_atoms hn hw1 hφ1 hne' hcA hφAA hAl
          have hcap : A ≤ F ⊥ A ⊔ F ⊥ w := hJ.le.trans (sup_le le_sup_right le_sup_left)
          exact hc (hφAA.trans (land_capture hwp hcap))
  obtain ⟨w, hw1, hw0, hwp, hwe⟩ := key k (by omega)
  exact ⟨w, hw1, hw0, hwp, hwe.trans ((F ⊥).mono inf_le_left)⟩

/-- **CertAtom with thin colours.** In W0, if no element of `Z` lies above two distinct colours, some atom of `R_1` is
μ-fixed. -/
theorem certAtom_of_thin {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    (hthin : ∀ z w w', F ⊥ z = ⊥ → height H (F ⊥ w) = 1 → F ⊥ (F ⊥ w) = ⊥ → height H (F ⊥ w') = 1 →
      F ⊥ (F ⊥ w') = ⊥ → F ⊥ w ≤ z → F ⊥ w' ≤ z → F ⊥ w = F ⊥ w') :
    ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q := by
  by_contra hno
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hmono := (height_strictMono hn).monotone
  -- every row of `R_1` lands, at an index `k + 1`
  have hland : ∀ z, F ⊥ z = ⊥ → ∃ k, height H ((F z)^[k + 1] (⊤ : α)) ≤ 2 ∧
      ∀ j < k + 1, 2 < height H ((F z)^[j] (⊤ : α)) := by
    intro z hz
    obtain ⟨i, hi, hmin⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ ((mem_one_iff ha).2 hz)))
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by have := land_index_pos htop hi; omega⟩
    exact ⟨k, hi, hmin⟩
  -- a fixed-colour witness from an exit landing equal to the colour's own value
  have hfix : ∀ c k, F ⊥ c = ⊥ → height H c = 1 → height H ((F c)^[k + 1] (⊤ : α)) ≤ 2 →
      (∀ j < k + 1, 2 < height H ((F c)^[j] (⊤ : α))) → F ⊥ ((F c)^[k + 1] (⊤ : α)) = c → False :=
    fun c k hc0 hc1 hi hmin he => hno ⟨c, (mem_one_iff ha).2 hc0, hc1, k + 1, hi, hmin, he⟩
  -- under NoFix, an exit of a colour row `c` is a different colour, and the landing is `c ⊔ c*`
  -- some colour exists: ColourGain at row `⊥`
  have hb0 : F ⊥ (⊥ : α) = ⊥ := by
    have h : F ⊥ (⊥ : α) ≤ a F ⊥ := le_a ((F ⊥).mono (bot_le : (⊥ : α) ≤ F ⊥ ⊥))
    rw [ha] at h; exact le_bot_iff.1 h
  obtain ⟨kb, hib, hminb⟩ := hland ⊥ hb0
  obtain ⟨w₀, hw₀1, hw₀0, -, -⟩ := colourGain hn ha hk2 htop hno hib hminb
  -- the shadow start for every colour row
  have hstartC : ∀ w k, F ⊥ (F ⊥ w) = ⊥ → height H ((F (F ⊥ w))^[k + 1] (⊤ : α)) ≤ 2 →
      (∀ j < k + 1, 2 < height H ((F (F ⊥ w))^[j] (⊤ : α))) →
      ∃ v, height H (F ⊥ v) = 1 ∧ F ⊥ (F ⊥ v) = ⊥ ∧ F ⊥ v ≤ (F (F ⊥ w))^[k + 1] (⊤ : α) ∧
        F ⊥ v ≤ F ⊥ ((F (F ⊥ w))^[k] (⊤ : α)) :=
    fun w k _ hi hmin => shadow_start hn ha hk2 htop hno hi hmin
  by_cases hA : ∃ w, height H (F ⊥ w) = 1 ∧ F ⊥ (F ⊥ w) = ⊥ ∧ ∃ k,
      height H ((F (F ⊥ w))^[k + 1] (⊤ : α)) ≤ 2 ∧ (∀ j < k + 1, 2 < height H ((F (F ⊥ w))^[j] (⊤ : α))) ∧
      F ⊥ ((F (F ⊥ w))^[k + 1] (⊤ : α)) = ⊥
  · -- Case A: a colour row `a` lands in `Z`; its shadow carries a single colour `c₀`, below every colour's landing
    obtain ⟨wa, hwa1, hwa0, ka, hia, hmina, hlama⟩ := hA
    set ca := F ⊥ wa with hcadef
    have hea : F ⊥ ((F ca)^[ka] (⊤ : α)) ≤ (F ca)^[ka + 1] (⊤ : α) := by
      rw [Function.iterate_succ_apply']; exact (F.mono bot_le) _
    obtain ⟨w₁, hw₁1, hw₁0, hw₁p, hw₁e⟩ := hstartC wa ka hwa0 hia hmina
    -- `c₀ := F ⊥ w₁` lies below the landing of every colour row
    have huniv : ∀ v, height H (F ⊥ v) = 1 → F ⊥ (F ⊥ v) = ⊥ → ∀ k,
        height H ((F (F ⊥ v))^[k + 1] (⊤ : α)) ≤ 2 → (∀ j < k + 1, 2 < height H ((F (F ⊥ v))^[j] (⊤ : α))) →
        F ⊥ w₁ ≤ (F (F ⊥ v))^[k + 1] (⊤ : α) := by
      intro v hv1 hv0 k hi hmin
      obtain ⟨u, hu1, hu0, hup, hue⟩ :=
        thinStair hn ha hk2 hthin hmina hi hmin (hstartC v k hv0 hi hmin)
      have e := hthin _ u w₁ hlama hu1 hu0 hw₁1 hw₁0 (hue.trans hea) (hw₁e.trans hea)
      exact e ▸ hup
    set c₀ := F ⊥ w₁ with hc₀def
    obtain ⟨k₀, hi₀, hmin₀⟩ := hland c₀ hw₁0
    have hc₀l : c₀ ≤ (F c₀)^[k₀ + 1] (⊤ : α) := huniv w₁ hw₁1 hw₁0 k₀ hi₀ hmin₀
    set p₀ := (F c₀)^[k₀ + 1] (⊤ : α) with hp₀def
    by_cases hp₀Z : F ⊥ p₀ = ⊥
    · obtain ⟨w', hw'1, hw'0, hw'p, hw'x⟩ := colourGain hn ha hk2 htop hno hi₀ hmin₀
      exact hw'x (le_of_eq (hthin p₀ w' w₁ hp₀Z hw'1 hw'0 hw₁1 hw₁0 hw'p hc₀l))
    · obtain ⟨hp2, hs1, hs0⟩ := exit_atom hn hk2 ha ((mem_one_iff ha).2 hw₁0) htop hi₀ hmin₀ hp₀Z
      set cs := F ⊥ p₀ with hcsdef
      have hsp : cs ≤ p₀ := by
        have h := land_bot_lt hk2 ha ((mem_one_iff ha).2 hw₁0) htop hi₀ hmin₀; exact h.le
      have hcs_ne : c₀ ≠ cs := by
        intro e
        obtain ⟨k', hk', hmin', hfx⟩ := exitFixed_of_dom hn hk2 (rfl : (F c₀)^[k₀ + 1] (⊤ : α) = p₀) hp2 hw₁1
          ((mem_one_iff ha).2 hw₁0) (le_refl c₀) e.symm
        exact hno ⟨c₀, (mem_one_iff ha).2 hw₁0, hw₁1, k', by rw [hk']; omega, hmin', hfx⟩
      obtain ⟨hJ, -⟩ := join_of_two_atoms hn hw₁1 hs1 hcs_ne hc₀l hsp (by omega)
      obtain ⟨ks, his, hmins⟩ := hland cs hs0
      have hc₀s : c₀ ≤ (F cs)^[ks + 1] (⊤ : α) := huniv p₀ hs1 hs0 ks his hmins
      have hcap : p₀ ≤ F ⊥ p₀ ⊔ c₀ := hJ.le.trans (sup_le le_sup_right le_sup_left)
      have hle := land_capture hc₀s hcap
      have hp2' : height H p₀ = 2 := hp2
      have his' : height H ((F cs)^[ks + 1] (⊤ : α)) ≤ 2 := his
      have heq : p₀ = (F cs)^[ks + 1] (⊤ : α) := eq_of_le_of_height_ge hn hle (by omega)
      exact hfix cs ks hs0 hs1 his hmins (by rw [← heq])
  · -- Case B: every colour row exits; all exits are one colour `c_a`, and row `c_a` exits to itself
    push_neg at hA
    set ca := F ⊥ w₀ with hcadef
    obtain ⟨ka, hia, hmina⟩ := hland ca hw₀0
    have hexit : ∀ v k, height H (F ⊥ v) = 1 → F ⊥ (F ⊥ v) = ⊥ →
        height H ((F (F ⊥ v))^[k + 1] (⊤ : α)) ≤ 2 → (∀ j < k + 1, 2 < height H ((F (F ⊥ v))^[j] (⊤ : α))) →
        F ⊥ ((F (F ⊥ v))^[k + 1] (⊤ : α)) ≠ ⊥ := fun v k h1 h0 hi hmin => hA v h1 h0 k hi hmin
    have hpa0 := hexit w₀ ka hw₀1 hw₀0 hia hmina
    obtain ⟨hpa2, hsa1, hsa0⟩ := exit_atom hn hk2 ha ((mem_one_iff ha).2 hw₀0) htop hia hmina hpa0
    set pa := (F ca)^[ka + 1] (⊤ : α) with hpadef
    set sa := F ⊥ pa with hsadef
    have hsap : sa ≤ pa := (land_bot_lt hk2 ha ((mem_one_iff ha).2 hw₀0) htop hia hmina).le
    -- every colour row's exit colour is `sa`
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
      obtain ⟨u, hu1, hu0, hup, hue⟩ :=
        thinStair hn ha hk2 hthin hmina hi hmin (hstartC v k hv0 hi hmin)
      have hua : F ⊥ u ≤ pa := by
        refine hue.trans ?_
        rw [hpadef, Function.iterate_succ_apply']; exact (F.mono bot_le) _
      by_cases hus : F ⊥ u = sa
      · -- `sa` lies below `py`; if `py`'s exit colour differs, capture puts `py` below `pa`
        by_contra hne
        have hne' : sa ≠ F ⊥ py := fun e => hne e.symm
        have hsapy : sa ≤ py := hus ▸ hup
        obtain ⟨hJ, -⟩ := join_of_two_atoms hn hsa1 hsy1 hne' hsapy hsyp (by omega)
        have hcap : py ≤ F ⊥ py ⊔ sa := hJ.le.trans (sup_le le_sup_right le_sup_left)
        have hle := land_capture hsap hcap
        have heq : py = pa := eq_of_le_of_height_ge hn hle (by omega)
        exact hne (by rw [heq])
      · -- a colour of `pa` other than its exit colour lies below `py`: capture puts `pa` below `py`
        obtain ⟨hJ, -⟩ := join_of_two_atoms hn hu1 hsa1 hus hua hsap (by omega)
        have hcap : pa ≤ F ⊥ pa ⊔ F ⊥ u := hJ.le.trans (sup_le le_sup_right le_sup_left)
        have hle := land_capture hup hcap
        have heq : pa = py := eq_of_le_of_height_ge hn hle (by omega)
        rw [← heq]
    obtain ⟨ks, his, hmins⟩ := hland sa hsa0
    have := hall pa hsa1 hsa0 ks his hmins
    exact hfix sa ks hsa0 hsa1 his hmins this

end Mordor.OrbitHeight
