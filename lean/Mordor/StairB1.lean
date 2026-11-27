import Mordor.Normalize

/-!
# The staircase lemma and CertAtom at N = 1 with an atom endpoint (§34.3z²⁹³, brief run 18)

* `tbFibre` (brief A2): a lower cell of an atom row `q` at a column `w` outside the zero fibre has value `q`, and
  `F(⊥, w) = q`. So Tb at `q` has content only on the fibre `{w : F(⊥, w) = q}`.
* `landEq_of_above` (brief 4.1, connector-free case of LandEq): if every high column `w` has `q < F(q, w)` for an atom
  `q`, then every row `x ≥ q` lands where `q` does. The proof walks the boundary of the staircase
  `{(j, k) : u_j(q) ⊓ u_k(x) high}`: the value of row `q` at each boundary point has height 2 and is squeezed between
  consecutive low corners, which chains `λ(x)` to `λ(q)`.
* `certAtom_of_N1` (brief Theorem B1): in W0, if the bottom descent is `⊤ > d > ⊥` with `d = F(⊥, ⊤)` an atom, then
  `d` is μ-fixed. Every high column lies in `d`'s fibre, so Tb at `d` gives `d < F(d, w)`; every row above `d` lands at
  `p = λ(d)`; `p ∉ Z` by `land_not_le`; and `F(⊥, p) = d`.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} [CompleteLattice α] {F : α →o α →o α}

/-- **TbFibre.** A lower cell of an atom row at a column outside the zero fibre sits in the atom's fibre. -/
theorem tbFibre {H : ℕ} (hn : NoChain α (H + 1)) {q w : α} (hq : height H q = 1) (hw0 : F ⊥ w ≠ ⊥)
    (hle : F q w ≤ q) : F q w = q ∧ F ⊥ w = q := by
  have h1 : F ⊥ w ≤ F q w := (F.mono bot_le) w
  have h0 : 0 < height H (F ⊥ w) := by
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hw0); rwa [height_bot_eq_zero] at this
  have e1 : F ⊥ w = q := eq_of_le_of_height_ge hn (h1.trans hle) (by omega)
  exact ⟨le_antisymm hle (e1.symm.le.trans h1), e1⟩

/-- The first low element of a row that lands. -/
theorem exists_first_low {H : ℕ} {x : α} (h : ∃ i, height H ((F x)^[i] (⊤ : α)) ≤ 2) :
    ∃ i, height H ((F x)^[i] (⊤ : α)) ≤ 2 ∧ ∀ j < i, 2 < height H ((F x)^[j] (⊤ : α)) := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun j hj => by have := Nat.find_min h hj; omega⟩

/-- **LandEq, connector-free case.** If row `q` (an atom) has `q < F(q, w)` at every high column, every row `x ≥ q`
lands at `λ(q)`. -/
theorem landEq_of_above {H : ℕ} (hn : NoChain α (H + 1)) {q x : α} (hq : height H q = 1) (hqx : q ≤ x)
    (hval : ∀ w, 2 < height H w → q < F q w)
    {i i' : ℕ} (hi : height H ((F q)^[i] (⊤ : α)) ≤ 2) (hmin : ∀ j < i, 2 < height H ((F q)^[j] (⊤ : α)))
    (hi' : height H ((F x)^[i'] (⊤ : α)) ≤ 2) (hmin' : ∀ j < i', 2 < height H ((F x)^[j] (⊤ : α)))
    (htop : 2 < height H (⊤ : α)) :
    (F x)^[i'] (⊤ : α) = (F q)^[i] (⊤ : α) := by
  classical
  let D : ℕ → ℕ → α := fun j k => (F q)^[j] (⊤ : α) ⊓ (F x)^[k] (⊤ : α)
  have hmono := (height_strictMono hn).monotone
  have hex : ∀ l, ∃ k, height H (D l k) ≤ 2 := fun l => ⟨i', le_trans (hmono inf_le_right) hi'⟩
  let κ : ℕ → ℕ := fun l => Nat.find (hex l)
  have hκlow : ∀ l, height H (D l (κ l)) ≤ 2 := fun l => Nat.find_spec (hex l)
  have hκmin : ∀ l k, k < κ l → 2 < height H (D l k) := fun l k hk => by
    have := Nat.find_min (hex l) hk; omega
  have hanti_q : ∀ {a b : ℕ}, a ≤ b → (F q)^[b] (⊤ : α) ≤ (F q)^[a] (⊤ : α) :=
    fun h => iter_antitone_of_le (F q).monotone (le_top : F q ⊤ ≤ ⊤) h
  have hanti_x : ∀ {a b : ℕ}, a ≤ b → (F x)^[b] (⊤ : α) ≤ (F x)^[a] (⊤ : α) :=
    fun h => iter_antitone_of_le (F x).monotone (le_top : F x ⊤ ≤ ⊤) h
  have hDk : ∀ l a b : ℕ, a ≤ b → D l b ≤ D l a := fun _ _ _ h => inf_le_inf_left _ (hanti_x h)
  have hDj : ∀ k a b : ℕ, a ≤ b → D b k ≤ D a k := fun _ _ _ h => inf_le_inf_right _ (hanti_q h)
  have hD0 : ∀ l, D l 0 = (F q)^[l] (⊤ : α) := fun l => by simp [D]
  have hD0' : ∀ k, D 0 k = (F x)^[k] (⊤ : α) := fun k => by simp [D]
  have hκpos : ∀ l, l < i → κ l ≠ 0 := fun l hl e => by
    have h0 := hκlow l; rw [e, hD0] at h0; have := hmin l hl; omega
  have hκanti : ∀ l, κ (l + 1) ≤ κ l := fun l =>
    Nat.find_min' (hex (l + 1)) (le_trans (hmono (hDj (κ l) _ _ (Nat.le_succ l))) (hκlow l))
  -- the boundary value at `l`: above `q`, below the corner `D (l+1) (κ l)`
  have hbd : ∀ l, l < i → ∃ m, κ l = m + 1 ∧ q < F q (D l m) ∧ F q (D l m) ≤ D (l + 1) (m + 1) := by
    intro l hl
    refine ⟨κ l - 1, by have := hκpos l hl; omega, hval _ (hκmin l _ (by have := hκpos l hl; omega)), ?_⟩
    show F q (D l (κ l - 1)) ≤ (F q)^[l + 1] (⊤ : α) ⊓ (F x)^[κ l - 1 + 1] (⊤ : α)
    refine le_inf ?_ ?_
    · rw [Function.iterate_succ_apply']; exact (F q).mono inf_le_left
    · rw [Function.iterate_succ_apply']; exact ((F.mono hqx) _).trans ((F x).mono inf_le_right)
  have hp2 : ∀ {e c : α}, q < e → e ≤ c → height H c ≤ 2 → c = e := fun hqe hec hc => by
    have := height_strictMono hn hqe
    exact (eq_of_le_of_height_ge hn hec (by omega)).symm
  -- downward induction: every low corner on the boundary equals `λ(q)`
  have key : ∀ n l, l + n + 1 = i → D l (κ l) = (F q)^[i] (⊤ : α) := by
    intro n
    induction n with
    | zero =>
      intro l hl
      obtain ⟨m, hm, hlt, hle⟩ := hbd l (by omega)
      have hep : F q (D l m) ≤ (F q)^[i] (⊤ : α) := hle.trans (by rw [← hl]; exact inf_le_left)
      have e1 := hp2 hlt hep hi
      have hA : F q (D l m) ≤ D l (κ l) := hle.trans (by rw [hm]; exact hDj _ _ _ (Nat.le_succ l))
      rw [hp2 hlt hA (hκlow l), e1]
    | succ n ih =>
      intro l hl
      obtain ⟨m, hm, hlt, hle⟩ := hbd l (by omega)
      have hnext := ih (l + 1) (by omega)
      have hep : F q (D l m) ≤ (F q)^[i] (⊤ : α) :=
        hnext ▸ hle.trans (hDk (l + 1) _ _ (by rw [← hm]; exact hκanti l))
      have e1 := hp2 hlt hep hi
      have hA : F q (D l m) ≤ D l (κ l) := hle.trans (by rw [hm]; exact hDj _ _ _ (Nat.le_succ l))
      rw [hp2 hlt hA (hκlow l), e1]
  have hi0 : i ≠ 0 := land_index_pos htop hi
  have h0 := key (i - 1) 0 (by omega)
  have hκ0 : κ 0 = i' := by
    apply le_antisymm
    · exact Nat.find_min' (hex 0) (by rw [hD0']; exact hi')
    · by_contra hc
      have := hmin' (κ 0) (by omega)
      have h1 := hκlow 0; rw [hD0'] at h1; omega
  rw [hκ0, hD0'] at h0
  exact h0

/-- **Theorem B1.** In W0, if `d = F(⊥, ⊤)` is an atom with `F(⊥, d) = ⊥` (the bottom descent is `⊤ > d > ⊥`), then
`d` is μ-fixed: its landing `p` lies outside `Z` and `F(⊥, p) = d`. -/
theorem certAtom_of_N1 {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htR : (⊤ : α) ∉ Rk F 2) (hnt : ¬ ∀ z ∈ Rk F 1, height H z ≤ 1)
    (hd1 : height H (F ⊥ (⊤ : α)) = 1) (hd0 : F ⊥ (F ⊥ (⊤ : α)) = ⊥) :
    ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ i, height H ((F q)^[i] (⊤ : α)) ≤ 2 ∧
      (∀ j < i, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[i] (⊤ : α)) = q := by
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hk2 z (hR12 ((mem_one_iff ha).2 hz))
  have htop : 2 < height H (⊤ : α) := by
    obtain ⟨z, hzR, hz1⟩ : ∃ z ∈ Rk F 1, 1 < height H z := by
      by_contra hc; push_neg at hc; exact hnt hc
    have hz2 : height H z ≤ 2 := hk2 z (hR12 hzR)
    have hzt : z ≠ ⊤ := fun e => htR (e ▸ hR12 hzR)
    have := height_strictMono hn (lt_top_iff_ne_top.2 hzt); omega
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hdR : F ⊥ (⊤ : α) ∈ Rk F 1 := (mem_one_iff ha).2 hd0
  have hlow : ∀ {w : α}, F ⊥ w ≠ ⊥ → F ⊥ w ≤ F ⊥ (⊤ : α) → F ⊥ w = F ⊥ (⊤ : α) := fun hne hle => by
    have := height_strictMono hn (bot_lt_iff_ne_bot.2 hne); rw [height_bot_eq_zero] at this
    exact eq_of_le_of_height_ge hn hle (by omega)
  have hfib : ∀ w, 2 < height H w → F ⊥ w = F ⊥ (⊤ : α) := fun w hw =>
    hlow (fun h => by have := hZT w h; omega) ((F ⊥).mono le_top)
  have hval : ∀ w, 2 < height H w → F ⊥ (⊤ : α) < F (F ⊥ (⊤ : α)) w := fun w hw =>
    lt_of_le_of_ne ((hfib w hw).symm.le.trans ((F.mono bot_le) w))
      (fun e => tb_of_tight hk2 hdR w hw e.symm.le)
  obtain ⟨i, hi, hmin⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hdR))
  have hip : i ≠ 0 := land_index_pos htop hi
  have hdp : F ⊥ (⊤ : α) < (F (F ⊥ (⊤ : α)))^[i] (⊤ : α) := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [Function.iterate_succ_apply']; exact hval _ (hmin k (by omega))
  have hpZ : F ⊥ ((F (F ⊥ (⊤ : α)))^[i] (⊤ : α)) ≠ ⊥ := by
    intro hp0
    have hpR := (mem_one_iff ha).2 hp0
    obtain ⟨i', hi', hmin'⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hpR))
    have heq := landEq_of_above hn hd1 hdp.le hval hi hmin hi' hmin' htop
    exact land_not_le hk2 hpR htop hi' hmin' (le_of_eq heq)
  exact ⟨_, hdR, hd1, i, hi, hmin, hlow hpZ ((F ⊥).mono le_top)⟩

/-- **UF′ (uniform fibre).** In W0: an atom `q ∈ R_1` lying below `F(⊥, w)` for every high `w`, whose last high descent
element `r` has `F(⊥, r) ∈ Z`, is μ-fixed. Every row above `q` lands at `p = λ(q)` (`landEq_of_above`), so `p ∉ Z`;
`q ≤ F(⊥, r) ≤ p` with `F(⊥, r) ∈ Z` forces `F(⊥, r) = q`, hence `F(⊥, p) = q`. -/
theorem fixed_of_uniformFibre {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α)) {q : α} (hqR : q ∈ Rk F 1)
    (hq1 : height H q = 1) (hfib : ∀ w, 2 < height H w → q ≤ F ⊥ w) {k : ℕ}
    (hi : height H ((F q)^[k + 1] (⊤ : α)) ≤ 2) (hmin : ∀ j < k + 1, 2 < height H ((F q)^[j] (⊤ : α)))
    (hrZ : F ⊥ (F ⊥ ((F q)^[k] (⊤ : α))) = ⊥) : F ⊥ ((F q)^[k + 1] (⊤ : α)) = q := by
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hval : ∀ w, 2 < height H w → q < F q w := fun w hw =>
    lt_of_le_of_ne ((hfib w hw).trans ((F.mono bot_le) w)) (fun e => tb_of_tight hk2 hqR w hw e.symm.le)
  have hrh : 2 < height H ((F q)^[k] (⊤ : α)) := hmin k (by omega)
  have hpe : (F q)^[k + 1] (⊤ : α) = F q ((F q)^[k] (⊤ : α)) := Function.iterate_succ_apply' _ _ _
  have hqp : q < (F q)^[k + 1] (⊤ : α) := by rw [hpe]; exact hval _ hrh
  have hpZ : F ⊥ ((F q)^[k + 1] (⊤ : α)) ≠ ⊥ := by
    intro hp0
    have hpR := (mem_one_iff ha).2 hp0
    obtain ⟨i', hi', hmin'⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hpR))
    have heq := landEq_of_above hn hq1 hqp.le hval hi hmin hi' hmin' htop
    exact land_not_le hk2 hpR htop hi' hmin' (le_of_eq heq)
  have hs1 : q ≤ F ⊥ ((F q)^[k] (⊤ : α)) := hfib _ hrh
  have hs2 : F ⊥ ((F q)^[k] (⊤ : α)) ≤ (F q)^[k + 1] (⊤ : α) := by rw [hpe]; exact (F.mono bot_le) _
  have hsp : F ⊥ ((F q)^[k] (⊤ : α)) ≠ (F q)^[k + 1] (⊤ : α) := fun e => hpZ (e ▸ hrZ)
  have hsq : F ⊥ ((F q)^[k] (⊤ : α)) = q := by
    have h1 := height_strictMono hn (lt_of_le_of_ne hs2 hsp)
    exact (eq_of_le_of_height_ge hn hs1 (by omega)).symm
  have hpr : (F q)^[k + 1] (⊤ : α) ≤ (F q)^[k] (⊤ : α) :=
    iter_antitone_of_le (F q).monotone (le_top : F q ⊤ ≤ ⊤) (Nat.le_succ k)
  have hle : F ⊥ ((F q)^[k + 1] (⊤ : α)) ≤ q := ((F ⊥).mono hpr).trans (le_of_eq hsq)
  have h0 := height_strictMono hn (bot_lt_iff_ne_bot.2 hpZ); rw [height_bot_eq_zero] at h0
  exact eq_of_le_of_height_ge hn hle (by omega)

/-- **A1-thin.** In W0, if `d = F(⊥, ⊤)` has height 2, `F(⊥, d) = ⊥`, and `q₀` is the only atom below `d`, then `q₀`
is μ-fixed (UF′: every high column has `F(⊥, w) ∈ {q₀, d}`). -/
theorem certAtom_of_N1_thin {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    (hd0 : F ⊥ (F ⊥ (⊤ : α)) = ⊥) {q₀ : α} (hq₀ : height H q₀ = 1) (hq₀d : q₀ ≤ F ⊥ (⊤ : α))
    (huniq : ∀ q, height H q = 1 → q ≤ F ⊥ (⊤ : α) → q = q₀) :
    ∃ i, height H ((F q₀)^[i] (⊤ : α)) ≤ 2 ∧ (∀ j < i, 2 < height H ((F q₀)^[j] (⊤ : α))) ∧
      F ⊥ ((F q₀)^[i] (⊤ : α)) = q₀ := by
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hk2 z (hR12 ((mem_one_iff ha).2 hz))
  have hq₀R : q₀ ∈ Rk F 1 :=
    (mem_one_iff ha).2 (le_bot_iff.1 (((F ⊥).mono hq₀d).trans (le_of_eq hd0)))
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hfib : ∀ w, 2 < height H w → q₀ ≤ F ⊥ w := by
    intro w hw
    have hne : F ⊥ w ≠ ⊥ := fun h => by have := hZT w h; omega
    have hle : F ⊥ w ≤ F ⊥ (⊤ : α) := (F ⊥).mono le_top
    have h0 := height_strictMono hn (bot_lt_iff_ne_bot.2 hne); rw [height_bot_eq_zero] at h0
    by_cases h1 : height H (F ⊥ w) = 1
    · exact le_of_eq (huniq _ h1 hle).symm
    · have hd2 : height H (F ⊥ (⊤ : α)) ≤ 2 := hZT _ hd0
      have e : F ⊥ w = F ⊥ (⊤ : α) := eq_of_le_of_height_ge hn hle (by omega)
      exact e ▸ hq₀d
  obtain ⟨i, hi, hmin⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hq₀R))
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by have := land_index_pos htop hi; omega⟩
  have hrZ : F ⊥ (F ⊥ ((F q₀)^[k] (⊤ : α))) = ⊥ :=
    le_bot_iff.1 (((F ⊥).mono ((F ⊥).mono le_top)).trans (le_of_eq hd0))
  exact ⟨k + 1, hi, hmin, fixed_of_uniformFibre hn ha hk2 htop hq₀R hq₀ hfib hi hmin hrZ⟩

end Mordor.OrbitHeight
