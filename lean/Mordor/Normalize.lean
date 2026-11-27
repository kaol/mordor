import Mordor.LateParent

/-!
# The normalization of the height-2 rows: GoodTop is CertAtom (§34.3z²⁹¹, brief run 17, A2)

`GoodTop` (§34.3z²⁸⁹) was proposed as a strengthening of CertAtom to the larger world W0♭ (Tb dropped at the height-2
rows of `Z`). It is not stronger. Given `F` in W0♭ with no self-landing height-2 row, the map `nrmHom` keeps every row
of `Z` of height ≤ 1, makes every row outside `Z` (or above height 2) constant `⊤`, and replaces a height-2 row `m` of
`Z` at a high column `y` by `⋀ {u_{j+1}(m) : y ≤ u_j(m)}` (`u_j(m)` the row-`m` descent from `⊤`). The new map is
monotone, has the same zero fibre and the same descents of every row of `Z` (so the same landings, exits and μ), and
satisfies Ta and Tb at every row of `Z`, so it lies in W0 (`w0_of_T`). Hence CertAtom for every map gives GoodTop
(`goodTop_of_certAtom`), and with `certAtom_of_goodTop` the two are equivalent (`goodTop_iff_certAtom`).
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} [CompleteLattice α] {F : α →o α →o α}

/-- **CertAtom** at level 1 (the conclusion of `certAtom_of_goodTop`, as a statement about `F`). -/
def CertAtom (F : α →o α →o α) (H : ℕ) : Prop :=
  a F ⊥ = ⊥ → (∀ z ∈ Rk F 2, height H z ≤ 2) → (⊤ : α) ∉ Rk F 2 → ¬ (∀ z ∈ Rk F 1, height H z ≤ 1) →
    ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ i, height H ((F q)^[i] (⊤ : α)) ≤ 2 ∧
      (∀ j < i, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[i] (⊤ : α)) = q

theorem bot_bot_of_a (ha : a F ⊥ = ⊥) : F ⊥ ⊥ = ⊥ := by
  have h : F ⊥ ⊥ ≤ a F ⊥ := le_a ((F ⊥).mono bot_le)
  rw [ha] at h; exact le_bot_iff.1 h

/-- With `a(⊥) = ⊥`, `R_1` is the zero fibre of row `⊥`. -/
theorem mem_one_iff (ha : a F ⊥ = ⊥) {z : α} : z ∈ Rk F 1 ↔ F ⊥ z = ⊥ := by
  constructor
  · intro hz
    have hz' : z ∈ step F (Rk F 0) := by rw [← Rk_succ]; exact hz
    obtain ⟨y, hzy, hy | ⟨w, hw, rfl⟩ | hb⟩ := hz'
    · have hy0 : y ≤ ⊥ := by simpa [Rk] using hy
      rw [le_bot_iff.1 (hzy.trans hy0)]; exact bot_bot_of_a ha
    · have hw0 : w ≤ ⊥ := by simpa [Rk] using hw
      rw [le_bot_iff.1 hw0, ha] at hzy; rw [le_bot_iff.1 hzy]; exact bot_bot_of_a ha
    · have hb0 : b F y ≤ ⊥ := by simpa [Rk] using hb
      have hcol : F (b F y) y = b F y := col_b y
      rw [le_bot_iff.1 hb0] at hcol
      exact le_bot_iff.1 (((F ⊥).mono hzy).trans (le_of_eq hcol))
  · intro hz
    exact mem_succ_of_cell (k := 0) (m := ⊥) (x := ⊥) (show (⊥ : α) ∈ Set.Iic ⊥ from le_rfl) le_rfl
      (Or.inl (le_of_eq hz))

/-- **(T) gives W0.** `a(⊥) = ⊥`, ZT, n1, `h(⊤) ≥ 3`, and Ta, Tb at every row of the zero fibre give `R_2` tight,
`⊤ ∉ R_2` and `R_1` not tight. -/
theorem w0_of_T {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2) (hn1 : ∃ z, F ⊥ z = ⊥ ∧ height H z = 2)
    (htop : 2 < height H (⊤ : α))
    (hTa : ∀ x, F ⊥ x = ⊥ → ∀ y, 2 < height H y → ¬ y ≤ F x y)
    (hTb : ∀ x, F ⊥ x = ⊥ → ∀ y, 2 < height H y → ¬ F x y ≤ x) :
    (∀ z ∈ Rk F 2, height H z ≤ 2) ∧ (⊤ : α) ∉ Rk F 2 ∧ ¬ (∀ z ∈ Rk F 1, height H z ≤ 1) := by
  have hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2 := by
    intro z hz
    have hz' : z ∈ step F (Rk F 1) := by rw [← Rk_succ]; exact hz
    obtain ⟨y, hzy, hy | ⟨w, hw, rfl⟩ | hb⟩ := hz'
    · exact ((height_strictMono hn).monotone hzy).trans (hZT y ((mem_one_iff ha).1 hy))
    · obtain ⟨i, hi⟩ := (ta_iff_lands hn w).1 (hTa w ((mem_one_iff ha).1 hw))
      have := (height_strictMono hn).monotone (hzy.trans (a_le_rowDesc (F := F) w i))
      omega
    · by_contra hh
      have hy : 2 < height H y := by have := (height_strictMono hn).monotone hzy; omega
      exact hTb _ ((mem_one_iff ha).1 hb) y hy (le_of_eq (col_b y))
  refine ⟨hk2, fun ht => by have := hk2 _ ht; omega, ?_⟩
  obtain ⟨z, hz0, hz2⟩ := hn1
  intro h; have := h z ((mem_one_iff ha).2 hz0); omega

/-- The descent successors of row `x` at or below column `y`. -/
def succSet (F : α →o α →o α) (x y : α) : Set α :=
  {w | ∃ j : ℕ, y ≤ (F x)^[j] (⊤ : α) ∧ w = (F x)^[j + 1] (⊤ : α)}

theorem le_sInf_succSet {x x' y y' : α} (hx : x' ≤ x) (hy : y' ≤ y) : F x' y' ≤ sInf (succSet F x y) := by
  refine le_sInf ?_
  rintro w ⟨j, hj, rfl⟩
  rw [Function.iterate_succ_apply']
  exact ((F.mono hx) y').trans ((F x).mono (hy.trans hj))

theorem sInf_succSet_mono {x y y' : α} (h : y ≤ y') : sInf (succSet F x y) ≤ sInf (succSet F x y') :=
  sInf_le_sInf fun _ ⟨j, hj, hw⟩ => ⟨j, h.trans hj, hw⟩

open Classical in
/-- The normalized map (values; see `nrmHom`). -/
noncomputable def nrm (F : α →o α →o α) (H : ℕ) (x y : α) : α :=
  if F ⊥ x = ⊥ ∧ height H x ≤ 2 then
    (if height H x = 2 ∧ 2 < height H y then sInf (succSet F x y) else F x y)
  else ⊤

theorem nrm_mono_y {H : ℕ} (hn : NoChain α (H + 1)) (x : α) : Monotone (nrm F H x) := by
  intro y y' hyy
  have hh := (height_strictMono hn).monotone hyy
  unfold nrm
  split_ifs with h1 h2 h3 h3
  · exact sInf_succSet_mono hyy
  · exact absurd ⟨h2.1, by omega⟩ h3
  · exact le_sInf_succSet le_rfl hyy
  · exact (F x).mono hyy
  · exact le_rfl

theorem nrm_mono_x {H : ℕ} (hn : NoChain α (H + 1)) {x x' : α} (hxx : x ≤ x') (y : α) :
    nrm F H x y ≤ nrm F H x' y := by
  have hh := (height_strictMono hn).monotone hxx
  by_cases hA' : F ⊥ x' = ⊥ ∧ height H x' ≤ 2
  · have hA : F ⊥ x = ⊥ ∧ height H x ≤ 2 :=
      ⟨le_bot_iff.1 (((F ⊥).mono hxx).trans (le_of_eq hA'.1)), by omega⟩
    unfold nrm; rw [if_pos hA, if_pos hA']
    by_cases hB' : height H x' = 2 ∧ 2 < height H y
    · rw [if_pos hB']
      by_cases hB : height H x = 2 ∧ 2 < height H y
      · rw [if_pos hB, eq_of_le_of_height_ge hn hxx (by omega)]
      · rw [if_neg hB]; exact le_sInf_succSet hxx le_rfl
    · rw [if_neg hB']
      by_cases hB : height H x = 2 ∧ 2 < height H y
      · exact absurd ⟨by omega, hB.2⟩ hB'
      · rw [if_neg hB]; exact (F.mono hxx) y
  · unfold nrm; rw [if_neg hA']; exact le_top

/-- **The normalization N2.** -/
noncomputable def nrmHom {H : ℕ} (hn : NoChain α (H + 1)) (F : α →o α →o α) : α →o α →o α :=
  ⟨fun x => ⟨nrm F H x, nrm_mono_y hn x⟩, fun _ _ h y => nrm_mono_x hn h y⟩

theorem nrmHom_apply {H : ℕ} (hn : NoChain α (H + 1)) (x y : α) : nrmHom hn F x y = nrm F H x y := rfl

/-- Rows of the zero fibre other than the height-2 ones are unchanged. -/
theorem nrm_low {H : ℕ} {x y : α} (hx0 : F ⊥ x = ⊥) (hx : height H x ≤ 2) (h2 : ¬ (height H x = 2 ∧ 2 < height H y)) :
    nrm F H x y = F x y := by
  unfold nrm; rw [if_pos ⟨hx0, hx⟩, if_neg h2]

theorem nrm_bot {H : ℕ} (ha : a F ⊥ = ⊥) (y : α) : nrm F H ⊥ y = F ⊥ y :=
  nrm_low (bot_bot_of_a ha) (by rw [height_bot_eq_zero]; omega) (by rw [height_bot_eq_zero]; omega)

/-- The descents of the rows of the zero fibre are unchanged. -/
theorem nrm_desc {H : ℕ} (hn : NoChain α (H + 1)) {x : α} (hx0 : F ⊥ x = ⊥) (hx : height H x ≤ 2) :
    ∀ j, (nrmHom hn F x)^[j] (⊤ : α) = (F x)^[j] (⊤ : α)
  | 0 => rfl
  | j + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', nrm_desc hn hx0 hx j, nrmHom_apply]
    by_cases h2 : height H x = 2 ∧ 2 < height H ((F x)^[j] (⊤ : α))
    · unfold nrm; rw [if_pos ⟨hx0, hx⟩, if_pos h2]
      apply le_antisymm
      · exact sInf_le ⟨j, le_rfl, by rw [Function.iterate_succ_apply']⟩
      · refine le_sInf ?_
        rintro w ⟨k, hk, rfl⟩
        rw [Function.iterate_succ_apply']
        exact (F x).mono hk
    · exact nrm_low hx0 hx h2

/-- **GoodTop from CertAtom.** If every monotone map satisfies CertAtom, `F` satisfies GoodTop. -/
theorem goodTop_of_certAtom {H : ℕ} (hn : NoChain α (H + 1)) (hC : ∀ G : α →o α →o α, CertAtom G H) :
    GoodTop F H := by
  intro ha hZT hn1 htop hTa hTb hno
  by_contra hw
  have hZT' : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hZT z ((mem_one_iff ha).2 hz)
  -- W0^desc: no height-2 row of `Z` lands at or below itself (`selfLow`)
  have hdesc : ∀ m, F ⊥ m = ⊥ → height H m = 2 → ∀ i, height H ((F m)^[i] (⊤ : α)) ≤ 2 →
      (∀ j < i, 2 < height H ((F m)^[j] (⊤ : α))) → ¬ (F m)^[i] (⊤ : α) ≤ m := by
    intro m hm0 hm2 i hi hmin hle
    have hmR := (mem_one_iff ha).2 hm0
    exact hw ⟨m, hmR, hm2, i,
      selfLow hn hZT (fun q hq h1 => hTb q hq (by omega)) htop hmR hm2 hi hmin hle⟩
  set G := nrmHom hn F with hG
  have hGb : ∀ y, G ⊥ y = F ⊥ y := fun y => nrm_bot ha y
  have hGa : a G ⊥ = ⊥ := by
    have e : G ⊥ = F ⊥ := OrderHom.ext _ _ (funext hGb)
    show OrderHom.gfp (G ⊥) = ⊥
    rw [e]; exact ha
  have hZ : ∀ z, G ⊥ z = ⊥ ↔ F ⊥ z = ⊥ := fun z => by rw [hGb]
  -- Ta and Tb for `G` at the rows of its zero fibre
  have hTaG : ∀ x, G ⊥ x = ⊥ → ∀ y, 2 < height H y → ¬ y ≤ G x y := by
    intro x hx0 y hy hle
    have hx0' := (hZ x).1 hx0
    have hx := hZT' x hx0'
    have hTaF := hTa x ((mem_one_iff ha).2 hx0')
    by_cases h2 : height H x = 2 ∧ 2 < height H y
    · rw [hG, nrmHom_apply] at hle; unfold nrm at hle; rw [if_pos ⟨hx0', hx⟩, if_pos h2] at hle
      have hall : ∀ j, y ≤ (F x)^[j] (⊤ : α) := by
        intro j; induction j with
        | zero => exact le_top
        | succ j ih => exact hle.trans (sInf_le ⟨j, ih, rfl⟩)
      obtain ⟨i, hi⟩ := (ta_iff_lands hn x).1 hTaF
      have := (height_strictMono hn).monotone (hall i); omega
    · rw [hG, nrmHom_apply, nrm_low hx0' hx h2] at hle; exact hTaF y hy hle
  have hTbG : ∀ x, G ⊥ x = ⊥ → ∀ y, 2 < height H y → ¬ G x y ≤ x := by
    intro x hx0 y hy hle
    have hx0' := (hZ x).1 hx0
    have hx := hZT' x hx0'
    by_cases h2 : height H x = 2 ∧ 2 < height H y
    · rw [hG, nrmHom_apply] at hle; unfold nrm at hle; rw [if_pos ⟨hx0', hx⟩, if_pos h2] at hle
      obtain ⟨i, hi⟩ := (ta_iff_lands hn x).1 (hTa x ((mem_one_iff ha).2 hx0'))
      have hex : ∃ k, ¬ y ≤ (F x)^[k] (⊤ : α) :=
        ⟨i, fun h => by have := (height_strictMono hn).monotone h; omega⟩
      classical
      have hk0 : Nat.find hex ≠ 0 := fun e => (e ▸ Nat.find_spec hex) le_top
      obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hyj : y ≤ (F x)^[j] (⊤ : α) := by
        by_contra hc; exact Nat.find_min hex (by omega : j < Nat.find hex) hc
      have hanti : ∀ {k l : ℕ}, k ≤ l → (F x)^[l] (⊤ : α) ≤ (F x)^[k] (⊤ : α) :=
        fun h => iter_antitone_of_le (F x).monotone (le_top : F x ⊤ ≤ ⊤) h
      have hge : (F x)^[j + 1] (⊤ : α) ≤ sInf (succSet F x y) := by
        refine le_sInf ?_
        rintro w ⟨k, hk, rfl⟩
        have hkj : k ≤ j := by
          by_contra hc
          exact (hj ▸ Nat.find_spec hex) (hk.trans (hanti (by omega)))
        exact hanti (by omega)
      have hl := hge.trans hle
      have hlow : height H ((F x)^[j + 1] (⊤ : α)) ≤ 2 := by
        have := (height_strictMono hn).monotone hl; omega
      have hmin : ∀ k < j + 1, 2 < height H ((F x)^[k] (⊤ : α)) := fun k hk => by
        have := (height_strictMono hn).monotone (hyj.trans (hanti (by omega : k ≤ j))); omega
      exact hdesc x hx0' h2.1 (j + 1) hlow hmin hl
    · rw [hG, nrmHom_apply, nrm_low hx0' hx h2] at hle
      have h1 : height H x ≤ 1 := by
        by_contra hc
        exact h2 ⟨by omega, hy⟩
      exact hTb x ((mem_one_iff ha).2 hx0') h1 y hy hle
  obtain ⟨z, hzR, hz2⟩ := hn1
  obtain ⟨hk2G, htG, hntG⟩ := w0_of_T (F := G) hn hGa
    (fun z hz => hZT' z ((hZ z).1 hz)) ⟨z, (hZ z).2 ((mem_one_iff ha).1 hzR), hz2⟩ htop hTaG hTbG
  obtain ⟨q, hqR, hq1, i, hi, hmin, hfix⟩ := hC G hGa hk2G htG hntG
  have hq0 : F ⊥ q = ⊥ := (hZ q).1 ((mem_one_iff hGa).1 hqR)
  have hd := nrm_desc hn hq0 (by omega : height H q ≤ 2)
  rw [hd] at hi hfix; rw [hGb] at hfix
  exact hno ⟨q, (mem_one_iff ha).2 hq0, hq1, i, hi, fun j hj => by rw [← hd j]; exact hmin j hj, hfix⟩

/-- **GoodTop ⟺ CertAtom** (over all monotone maps on `α`). GoodTop is CertAtom in other words. -/
theorem goodTop_iff_certAtom {H : ℕ} (hn : NoChain α (H + 1)) :
    (∀ G : α →o α →o α, GoodTop G H) ↔ (∀ G : α →o α →o α, CertAtom G H) :=
  ⟨fun h G => fun ha hk2 htR hnt => certAtom_of_goodTop hn (h G) ha hk2 htR hnt,
   fun h _ => goodTop_of_certAtom hn h⟩

end Mordor.OrbitHeight
