import Mordor.IntervalOrbit

/-!
# The orbit-height property by induction on height (round 26, §34.3z¹⁵⁷, Programme D)

`OHAt H`: for every complete lattice `β` of edge-height `≤ H` (`NoChain β (H + 1)`) and every monotone `G`,
`⊤ ∈ R^G_H` (this is the conclusion of `top_mem_of_orbitHeight`, and it gives Cut by `cutMaps_of_top_mem`).

Interval heights: `noChain_Icc_bot` (`[⊥, c]` has edge-height `≤ h(c)`) and `noChain_Icc_top` (`[m, ⊤]` has
edge-height `≤ H − h(m)`).

Assuming `OHAt H'` for every `H' < H` (in the same universe):
* `diagGood_of_lower`: every diagonal pre-fixed `c ≠ ⊤` lies in `R_{h(c)}` (via `diag_pre_mem`).
* `feeder_identity_of_lower`: feeder identity (`h(m') ≤ k`, `m' ≤ t`, `t ∉ R_k`, `F m' t ≤ m'` ⇒ `b t = m'`).
* `top_mem_of_good_post`: if some `m ≠ ⊥` with `m ≤ F m m` is *good* (`m ∈ R_j`, `j ≤ h(m)`), then `⊤ ∈ R_H`
  (via `top_mem_of_diag_post`).
* `top_mem_of_diag_fixed`: in particular if the diagonal `x ↦ F x x` has a fixed point other than `⊥` and `⊤`;
  `top_mem_of_a_bot`: or if `a ⊥ ≠ ⊥`.

* `top_mem_of_b_top`: or if `b ⊤ ≠ ⊤` (then `b ⊤` is diagonal pre-fixed and below the top, hence good).
* `top_mem_of_good_rise`: or if some good `x` (`x ∈ R_j`, `j ≤ h(x)`) has `x < a x` (then `a x` is a good
  diagonal post-fixed point).
* `top_mem_reduction`: so `OHAt H` (hence Cut at edge-height `H`) reduces, given the lower heights, to the
  **rigid** maps: `a ⊥ = ⊥`, `b ⊤ = ⊤`, and the diagonal `x ↦ F x x` fixes only `⊥` and `⊤`.
* `Rise F H` (**conjecture**, exact evidence §34.3z¹⁵⁷): `⊥ = ⊤` (the degenerate lattice), or `b ⊤ ≠ ⊤`, or a
  diagonal fixed point `∉ {⊥, ⊤}`, or a good `x < a x`. `top_mem_of_rise`; `ohAt_of_riseAt`: Rise at every height `≤ H` gives `OHAt H` by strong induction;
  `cutMaps_of_riseAt`: hence Cut at edge-height `H`.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

/-- The orbit-height property at edge-height `H`, for all complete lattices in universe `u`. -/
def OHAt (H : ℕ) : Prop :=
  ∀ (β : Type u) [CompleteLattice β] (G : β →o β →o β), NoChain β (H + 1) → (⊤ : β) ∈ Rk G H

variable {α : Type u} [CompleteLattice α] {F : α →o α →o α}

theorem chainTo_of_le {x c : α} (hxc : x ≤ c) : ∀ k, chainTo x k → chainTo c k
  | 0, _ => trivial
  | _ + 1, ⟨y, hy, hc⟩ => ⟨y, lt_of_lt_of_le hy hxc, hc⟩

theorem chainTo_val_Icc {l v : α} [Fact (l ≤ v)] (j : ℕ) (hl : chainTo l j) :
    ∀ (k : ℕ) (x : Set.Icc l v), chainTo x k → chainTo x.1 (k + j)
  | 0, x, _ => by simpa using chainTo_of_le x.2.1 j hl
  | k + 1, _, ⟨y, hy, hc⟩ => by
    rw [show k + 1 + j = (k + j) + 1 by omega]
    exact ⟨y.1, Subtype.coe_lt_coe.2 hy, chainTo_val_Icc j hl k y hc⟩

/-- `[⊥, c]` has edge-height `≤ h(c)`. -/
theorem noChain_Icc_bot {H : ℕ} (hn : NoChain α (H + 1)) (c : α) [Fact ((⊥ : α) ≤ c)] :
    NoChain (Set.Icc (⊥ : α) c) (height H c + 1) := fun x hx => by
  have h1 : chainTo c (height H c + 1) := chainTo_of_le x.2.2 _ (by simpa using chainTo_val_Icc 0 trivial _ x hx)
  by_cases hle : height H c + 1 ≤ H
  · have := le_height hle h1; omega
  · exact hn c (by have := height_le (H := H) c; rwa [show H + 1 = height H c + 1 by omega])

/-- `[m, ⊤]` has edge-height `≤ H − h(m)`. -/
theorem noChain_Icc_top {H : ℕ} (hn : NoChain α (H + 1)) (m : α) [Fact (m ≤ (⊤ : α))] :
    NoChain (Set.Icc m (⊤ : α)) (H - height H m + 1) := fun x hx => by
  have h1 := chainTo_val_Icc (height H m) (chainTo_height m) _ x hx
  have := height_le (H := H) m
  exact hn x.1 (by rwa [show H - height H m + 1 + height H m = H + 1 by omega] at h1)

theorem height_lt_of_ne_top {H : ℕ} (hn : NoChain α (H + 1)) {c : α} (ht : c ≠ ⊤) : height H c < H :=
  lt_of_lt_of_le (height_strictMono hn (lt_top_iff_ne_top.2 ht)) (height_le _)

theorem one_le_H_of_ne_bot {H : ℕ} (hn : NoChain α (H + 1)) {c : α} (hb : c ≠ ⊥) : 1 ≤ H := by
  by_contra h
  exact hn c (by rw [show H + 1 = 1 by omega]; exact ⟨⊥, bot_lt_iff_ne_bot.2 hb, trivial⟩)

theorem one_le_height_of_ne_bot {H : ℕ} {c : α} (hb : c ≠ ⊥) (hH : 1 ≤ H) :
    1 ≤ height H c :=
  le_height hH ⟨⊥, bot_lt_iff_ne_bot.2 hb, trivial⟩

/-- **Diagonal goodness below the top**, from the lower heights. -/
theorem diagGood_of_lower {H : ℕ} (IH : ∀ H' < H, OHAt.{u} H') (hn : NoChain α (H + 1)) {c : α}
    (hc : F c c ≤ c) (ht : c ≠ ⊤) : c ∈ Rk F (height H c) := by
  haveI : Fact ((⊥ : α) ≤ c) := ⟨bot_le⟩
  exact diag_pre_mem hc (IH _ (height_lt_of_ne_top hn ht) _ _ (noChain_Icc_bot hn c))

/-- **Feeder identity** at edge-height `H`, from the lower heights. -/
theorem feeder_identity_of_lower {H : ℕ} (IH : ∀ H' < H, OHAt.{u} H') (hn : NoChain α (H + 1)) {k : ℕ}
    {m' t : α} (hm'k : height H m' ≤ k) (hmt : m' ≤ t) (ht : t ∉ Rk F k) (hlo : F m' t ≤ m') : b F t = m' := by
  rcases eq_or_lt_of_le (b_le hlo) with e | hlt
  · exact e
  exfalso
  have hct : b F t ≤ t := hlt.le.trans hmt
  have hdiag : F (b F t) (b F t) ≤ b F t := ((F (b F t)).mono hct).trans (col_b t).le
  have hmem := diagGood_of_lower IH hn hdiag (ne_top_of_lt (lt_of_lt_of_le hlt le_top))
  have h1 := height_strictMono hn hlt
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact ht (mem_succ_of_b (Rk_mono (by omega) hmem))

/-- **A good diagonal post-fixed point gives the top**, from the lower heights. -/
theorem top_mem_of_good_post {H : ℕ} (IH : ∀ H' < H, OHAt.{u} H') (hn : NoChain α (H + 1)) {m : α}
    (hm : m ≤ F m m) (hb : m ≠ ⊥) {j : ℕ} (hmj : m ∈ Rk F j) (hj : j ≤ height H m) : (⊤ : α) ∈ Rk F H := by
  haveI : Fact (m ≤ (⊤ : α)) := ⟨le_top⟩
  have hH : 1 ≤ H := one_le_H_of_ne_bot hn hb
  have h1 := one_le_height_of_ne_bot hb hH
  have hmH := height_le (H := H) m
  have := top_mem_of_diag_post hm hmj (IH _ (by omega) _ _ (noChain_Icc_top hn m))
  exact Rk_mono (by omega) this

/-- **A non-trivial diagonal fixed point gives the top**, from the lower heights. -/
theorem top_mem_of_diag_fixed {H : ℕ} (IH : ∀ H' < H, OHAt.{u} H') (hn : NoChain α (H + 1)) {c : α}
    (hc : F c c = c) (hb : c ≠ ⊥) (ht : c ≠ ⊤) : (⊤ : α) ∈ Rk F H :=
  top_mem_of_good_post IH hn hc.ge hb (diagGood_of_lower IH hn hc.le ht) le_rfl

/-- **`a ⊥ ≠ ⊥` gives the top**, from the lower heights. -/
theorem top_mem_of_a_bot {H : ℕ} (IH : ∀ H' < H, OHAt.{u} H') (hn : NoChain α (H + 1)) (ha : a F ⊥ ≠ ⊥) :
    (⊤ : α) ∈ Rk F H := by
  have hm : a F ⊥ ∈ Rk F 1 := by
    rw [Rk_succ]; exact ⟨a F ⊥, le_rfl, Or.inr (Or.inl ⟨⊥, show (⊥ : α) ∈ Rk F 0 from le_rfl, rfl⟩)⟩
  have hH : 1 ≤ H := one_le_H_of_ne_bot hn ha
  exact top_mem_of_good_post IH hn (le_diag_of_a bot_le) ha hm (one_le_height_of_ne_bot ha hH)

/-- **`b ⊤ ≠ ⊤` gives the top**, from the lower heights. -/
theorem top_mem_of_b_top {H : ℕ} (IH : ∀ H' < H, OHAt.{u} H') (hn : NoChain α (H + 1)) (hb : b F ⊤ ≠ ⊤) :
    (⊤ : α) ∈ Rk F H := by
  have hdiag : F (b F ⊤) (b F ⊤) ≤ b F ⊤ := ((F (b F ⊤)).mono le_top).trans (col_b ⊤).le
  have hmem := diagGood_of_lower IH hn hdiag hb
  have := height_lt_of_ne_top hn hb
  exact Rk_mono (by omega) (mem_succ_of_b hmem)

/-- **A good rising row gives the top**, from the lower heights. -/
theorem top_mem_of_good_rise {H : ℕ} (IH : ∀ H' < H, OHAt.{u} H') (hn : NoChain α (H + 1)) {x : α} {j : ℕ}
    (hx : x ∈ Rk F j) (hj : j ≤ height H x) (hlt : x < a F x) : (⊤ : α) ∈ Rk F H := by
  have hm : a F x ∈ Rk F (j + 1) := by
    rw [Rk_succ]; exact ⟨a F x, le_rfl, Or.inr (Or.inl ⟨x, hx, rfl⟩)⟩
  have := height_strictMono hn hlt
  exact top_mem_of_good_post IH hn (le_diag_of_a hlt.le) (ne_bot_of_gt hlt) hm (by omega)

/-- **The height reduction.** Given the lower heights, the orbit-height property can fail only for rigid maps. -/
theorem top_mem_reduction {H : ℕ} (IH : ∀ H' < H, OHAt.{u} H') (hn : NoChain α (H + 1))
    (h : a F ⊥ ≠ ⊥ ∨ b F ⊤ ≠ ⊤ ∨ ∃ c, F c c = c ∧ c ≠ ⊥ ∧ c ≠ ⊤) : (⊤ : α) ∈ Rk F H := by
  rcases h with ha | hb | ⟨c, hc, h1, h2⟩
  · exact top_mem_of_a_bot IH hn ha
  · exact top_mem_of_b_top IH hn hb
  · exact top_mem_of_diag_fixed IH hn hc h1 h2

/-- **Rise** (conjecture): one of the three reductions applies. -/
def Rise (F : α →o α →o α) (H : ℕ) : Prop :=
  (⊥ : α) = ⊤ ∨ b F ⊤ ≠ ⊤ ∨ (∃ c, F c c = c ∧ c ≠ ⊥ ∧ c ≠ ⊤) ∨ ∃ x j, x ∈ Rk F j ∧ j ≤ height H x ∧ x < a F x

theorem top_mem_of_rise {H : ℕ} (IH : ∀ H' < H, OHAt.{u} H') (hn : NoChain α (H + 1)) (h : Rise F H) :
    (⊤ : α) ∈ Rk F H := by
  rcases h with h0 | hb | ⟨c, hc, h1, h2⟩ | ⟨x, j, hx, hj, hlt⟩
  · exact h0 ▸ bot_mem_Rk H
  · exact top_mem_of_b_top IH hn hb
  · exact top_mem_of_diag_fixed IH hn hc h1 h2
  · exact top_mem_of_good_rise IH hn hx hj hlt

/-- Rise at edge-height `H` for all lattices of universe `u`. -/
def RiseAt (H : ℕ) : Prop :=
  ∀ (β : Type u) [CompleteLattice β] (G : β →o β →o β), NoChain β (H + 1) → Rise G H

/-- **Rise gives the orbit-height property**, by strong induction on height. -/
theorem ohAt_of_riseAt {H : ℕ} (h : ∀ H' ≤ H, RiseAt.{u} H') : OHAt.{u} H := by
  induction H using Nat.strong_induction_on with
  | _ H ih =>
    intro β _ G hn
    exact top_mem_of_rise (fun H' hH' => ih H' hH' (fun H'' hH'' => h H'' (by omega))) hn (h H le_rfl β G hn)

/-- **Rise gives Cut.** -/
theorem cutMaps_of_riseAt {H : ℕ} (h : ∀ H' ≤ H, RiseAt.{u} H') (hn : NoChain α (H + 1)) : CutMaps F :=
  cutMaps_of_top_mem (ohAt_of_riseAt h α F hn)

/-! ### Base cases: Rise at edge-height `≤ 2` (§34.3z¹⁵⁸) -/

theorem noChain_mono {n m : ℕ} (hn : NoChain α n) (h : n ≤ m) : NoChain α m :=
  fun x hx => hn x (chainTo_mono' m n x hx h)

/-- **Rise on lattices of height `≤ 2`.** If `a ⊥ = ⊥` and `b ⊤ = ⊤`, then `v = F ⊥ ⊤` is an atom with
`F ⊥ v = ⊥` (so `v ∈ R₁`) and `F v ⊤ = ⊤` (so `v < a v`). -/
theorem rise_of_noChain3 {H : ℕ} (hH : 1 ≤ H) (hn : NoChain α 3) : Rise F H := by
  by_cases h0 : (⊥ : α) = ⊤
  · exact Or.inl h0
  by_cases hbt : b F ⊤ = ⊤
  swap
  · exact Or.inr (Or.inl hbt)
  refine Or.inr (Or.inr (Or.inr ?_))
  by_cases ha : a F ⊥ = ⊥
  swap
  · exact ⟨⊥, 0, bot_mem_Rk 0, Nat.zero_le _, bot_lt_iff_ne_bot.2 ha⟩
  set v := F ⊥ ⊤ with hvdef
  have hv0 : v ≠ ⊥ := fun e => h0 (by
    have : b F ⊤ ≤ ⊥ := b_le (by rw [← hvdef, e])
    rw [hbt] at this; exact (le_bot_iff.1 this).symm)
  have hvt : v ≠ ⊤ := fun e => h0 (by
    have : (⊤ : α) ≤ a F ⊥ := le_a (by rw [← hvdef, e])
    rw [ha] at this; exact (le_bot_iff.1 this).symm)
  -- in height ≤ 2, `⊥ < z < v` and `v < w < ⊤` are impossible
  have hatom : ∀ z, z < v → z = ⊥ := fun z hz => by
    by_contra hz0
    exact hn ⊤ ⟨v, lt_top_iff_ne_top.2 hvt, ⟨z, hz, ⟨⊥, bot_lt_iff_ne_bot.2 hz0, trivial⟩⟩⟩
  have hcoatom : ∀ w, v < w → w = ⊤ := fun w hw => by
    by_contra hwt
    exact hn ⊤ ⟨w, lt_top_iff_ne_top.2 hwt, ⟨v, hw, ⟨⊥, bot_lt_iff_ne_bot.2 hv0, trivial⟩⟩⟩
  have hFv : F ⊥ v = ⊥ := by
    have hle : F ⊥ v ≤ v := (F ⊥).mono le_top
    rcases eq_or_lt_of_le hle with e | hlt
    · exact absurd (le_bot_iff.1 (ha ▸ le_a e.symm.le)) hv0
    · exact hatom _ hlt
  have hvR : v ∈ Rk F 1 := mem_succ_of_b (show b F v ∈ Rk F 0 from b_le (le_of_eq hFv))
  have hvlt : v < F v ⊤ := by
    have hle : v ≤ F v ⊤ := F.mono bot_le ⊤
    refine lt_of_le_of_ne hle fun e => hvt ?_
    have : b F ⊤ ≤ v := b_le e.symm.le
    rw [hbt] at this; exact top_le_iff.1 this
  have htop : F v ⊤ = ⊤ := hcoatom _ hvlt
  exact ⟨v, 1, hvR, one_le_height_of_ne_bot hv0 hH, lt_of_lt_of_le (lt_top_iff_ne_top.2 hvt) (le_a htop.ge)⟩

theorem riseAt_zero : RiseAt.{u} 0 := fun β _ G hn => Or.inl (by
  by_contra h
  exact hn ⊤ ⟨⊥, bot_lt_iff_ne_bot.2 (Ne.symm h), trivial⟩)

theorem riseAt_le_two {H : ℕ} (hH : H ≤ 2) : RiseAt.{u} H := by
  rcases Nat.eq_zero_or_pos H with rfl | hpos
  · exact riseAt_zero
  · exact fun β _ G hn => rise_of_noChain3 hpos (noChain_mono hn (by omega))

/-- **Rise on lattices of height `≤ 3`.** With `a ⊥ = ⊥`, `b ⊤ = ⊤` and `v = F ⊥ ⊤`:
* if `F v ⊤ = ⊤`: either `F ⊥ v = ⊥` (so `v ∈ R₁` rises), or `p = F ⊥ v` is a good atom and either `v ∈ R₂` (via
  `F p v ≤ p` or `v ≤ F p v`) or `F p ⊤ ≥ v ⊔ F p v = ⊤` (so `p` rises);
* if `w = F v ⊤ < ⊤`: then `⊥ < v < w < ⊤`, `w` rises, and `w ∈ R₂` because `F ⊥ w ∈ {⊥, v}` and
  `F v w ∈ {v, w}`. -/
theorem rise_of_noChain4 {H : ℕ} (hH : 2 ≤ H) (hn : NoChain α 4) : Rise F H := by
  by_cases h0 : (⊥ : α) = ⊤
  · exact Or.inl h0
  by_cases hbt : b F ⊤ = ⊤
  swap
  · exact Or.inr (Or.inl hbt)
  refine Or.inr (Or.inr (Or.inr ?_))
  by_cases ha : a F ⊥ = ⊥
  swap
  · exact ⟨⊥, 0, bot_mem_Rk 0, Nat.zero_le _, bot_lt_iff_ne_bot.2 ha⟩
  have chain4 : ∀ x₁ x₂ x₃ : α, ⊥ < x₁ → x₁ < x₂ → x₂ < x₃ → x₃ < ⊤ → False := fun x₁ x₂ x₃ h1 h2 h3 h4 =>
    hn ⊤ ⟨x₃, h4, ⟨x₂, h3, ⟨x₁, h2, ⟨⊥, h1, trivial⟩⟩⟩⟩
  have hbtop : ∀ z, F z ⊤ ≤ z → z = ⊤ := fun z hz => top_le_iff.1 (hbt ▸ b_le hz)
  have habot : ∀ z, z ≤ F ⊥ z → z = ⊥ := fun z hz => le_bot_iff.1 (ha ▸ le_a hz)
  have hR1 : ∀ z, F ⊥ z = ⊥ → z ∈ Rk F 1 := fun z hz => mem_succ_of_b (show b F z ∈ Rk F 0 from b_le hz.le)
  have hR2b : ∀ {y p : α}, p ∈ Rk F 1 → F p y ≤ p → y ∈ Rk F 2 := fun hp h =>
    mem_succ_of_b (Rk_down 1 (b_le h) hp)
  have hR2a : ∀ {y p : α}, p ∈ Rk F 1 → y ≤ F p y → y ∈ Rk F 2 := fun {y p} hp h => by
    rw [Rk_succ]; exact ⟨a F p, le_a h, Or.inr (Or.inl ⟨p, hp, rfl⟩)⟩
  have hgood1 : ∀ {z : α}, z ≠ ⊥ → 1 ≤ height H z := fun hz => one_le_height_of_ne_bot hz (by omega)
  have hgood2 : ∀ {p z : α}, ⊥ < p → p < z → 2 ≤ height H z := fun {p z} hp hz => le_height hH ⟨p, hz, ⟨⊥, hp, trivial⟩⟩
  set v := F ⊥ ⊤ with hvdef
  have hv0 : v ≠ ⊥ := fun e => h0 (hbtop ⊥ (by rw [← hvdef, e]))
  have hvt : v ≠ ⊤ := fun e => h0 (habot ⊤ (by rw [← hvdef, e])).symm
  have hFbv : F ⊥ v < v := lt_of_le_of_ne ((F ⊥).mono le_top) fun e => hv0 (habot v e.symm.le)
  by_cases hA : F v ⊤ = ⊤
  · have hvrise : v < a F v := lt_of_lt_of_le (lt_top_iff_ne_top.2 hvt) (le_a hA.ge)
    by_cases hp0 : F ⊥ v = ⊥
    · exact ⟨v, 1, hR1 v hp0, hgood1 hv0, hvrise⟩
    set p := F ⊥ v with hpdef
    have hpb : ⊥ < p := bot_lt_iff_ne_bot.2 hp0
    have hpR : p ∈ Rk F 1 := hR1 p (by
      have hle : F ⊥ p ≤ p := (F ⊥).mono hFbv.le
      rcases eq_or_lt_of_le hle with e | hlt
      · exact absurd (habot p e.symm.le) hp0
      · by_contra hz; exact chain4 _ _ _ (bot_lt_iff_ne_bot.2 hz) hlt hFbv (lt_top_iff_ne_top.2 hvt))
    by_cases h1 : F p v ≤ p
    · exact ⟨v, 2, hR2b hpR h1, hgood2 hpb hFbv, hvrise⟩
    by_cases h2 : v ≤ F p v
    · exact ⟨v, 2, hR2a hpR h2, hgood2 hpb hFbv, hvrise⟩
    -- `w' = F p v` lies above `p`, is not below `p` and not above `v`; then `F p ⊤ = ⊤`
    have hpw : p ≤ F p v := F.mono bot_le v
    have hFpt : F p ⊤ = ⊤ := by
      by_contra hne
      have hvle : v ≤ F p ⊤ := F.mono bot_le ⊤
      have hwle : F p v ≤ F p ⊤ := (F p).mono le_top
      rcases eq_or_lt_of_le hvle with e | hlt
      · -- `F p v ≤ v`, so `F p v ∈ [p, v]`, impossible
        have hwv : F p v ≤ v := e ▸ hwle
        rcases eq_or_lt_of_le hpw with e' | hlt'
        · exact h1 e'.symm.le
        rcases eq_or_lt_of_le hwv with e'' | hlt''
        · exact h2 e''.symm.le
        · exact chain4 _ _ _ hpb hlt' hlt'' (lt_top_iff_ne_top.2 hvt)
      · exact chain4 _ _ _ hpb hFbv hlt (lt_top_iff_ne_top.2 hne)
    exact ⟨p, 1, hpR, hgood1 hp0, lt_of_lt_of_le (hFbv.trans (lt_top_iff_ne_top.2 hvt)) (le_a hFpt.ge)⟩
  · set w := F v ⊤ with hwdef
    have hvw : v < w := lt_of_le_of_ne (F.mono bot_le ⊤) fun e => hvt (hbtop v (by rw [← hwdef, ← e]))
    have hwt : w < ⊤ := lt_top_iff_ne_top.2 hA
    have hvatom : ∀ z, z < v → z = ⊥ := fun z hz => by
      by_contra hz0; exact chain4 _ _ _ (bot_lt_iff_ne_bot.2 hz0) hz hvw hwt
    have hvR : v ∈ Rk F 1 := hR1 v (hvatom _ hFbv)
    have hwrise : w < a F w := by
      have hle : w ≤ F w ⊤ := F.mono hvw.le ⊤
      have hlt : w < F w ⊤ := lt_of_le_of_ne hle fun e => hA (hbtop w (by rw [← e]))
      have htop : F w ⊤ = ⊤ := by
        by_contra hne; exact chain4 _ _ _ (bot_lt_iff_ne_bot.2 hv0) hvw hlt (lt_top_iff_ne_top.2 hne)
      exact lt_of_lt_of_le hwt (le_a htop.ge)
    have hwR : w ∈ Rk F 2 := by
      have hle : F ⊥ w ≤ v := (F ⊥).mono le_top
      rcases eq_or_lt_of_le hle with e | hlt
      · have h1 : v ≤ F v w := e ▸ F.mono bot_le w
        have h2 : F v w ≤ w := (F v).mono le_top
        rcases eq_or_lt_of_le h1 with e' | hlt'
        · exact hR2b hvR e'.symm.le
        rcases eq_or_lt_of_le h2 with e'' | hlt''
        · exact hR2a hvR e''.symm.le
        · exact absurd (chain4 _ _ _ (bot_lt_iff_ne_bot.2 hv0) hlt' hlt'' hwt) id
      · exact Rk_mono (by omega) (hR1 w (hvatom _ hlt))
    exact ⟨w, 2, hwR, hgood2 (bot_lt_iff_ne_bot.2 hv0) hvw, hwrise⟩

theorem riseAt_le_three {H : ℕ} (hH : H ≤ 3) : RiseAt.{u} H := by
  rcases Nat.lt_or_ge H 3 with h | h
  · exact riseAt_le_two (by omega)
  · exact fun β _ G hn => rise_of_noChain4 (by omega) (noChain_mono hn (by omega))

/-- **The orbit-height property at edge-height 3.** -/
theorem ohAt_three : OHAt.{u} 3 := ohAt_of_riseAt fun _ h => riseAt_le_three h

/-- **The orbit-height property at edge-height 2**: `⊤ ∈ R₂` for every monotone map on a lattice of height `≤ 2`. -/
theorem ohAt_two : OHAt.{u} 2 := ohAt_of_riseAt fun _ h => riseAt_le_two h

end Mordor.OrbitHeight
