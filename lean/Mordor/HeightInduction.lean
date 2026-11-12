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
* `Rise F H` (**conjecture**, exact evidence §34.3z¹⁵⁷): `b ⊤ ≠ ⊤`, or a diagonal fixed point `∉ {⊥, ⊤}`, or a good
  `x < a x`. `top_mem_of_rise`; `ohAt_of_riseAt`: Rise at every height `≤ H` gives `OHAt H` by strong induction;
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
  b F ⊤ ≠ ⊤ ∨ (∃ c, F c c = c ∧ c ≠ ⊥ ∧ c ≠ ⊤) ∨ ∃ x j, x ∈ Rk F j ∧ j ≤ height H x ∧ x < a F x

theorem top_mem_of_rise {H : ℕ} (IH : ∀ H' < H, OHAt.{u} H') (hn : NoChain α (H + 1)) (h : Rise F H) :
    (⊤ : α) ∈ Rk F H := by
  rcases h with hb | ⟨c, hc, h1, h2⟩ | ⟨x, j, hx, hj, hlt⟩
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

end Mordor.OrbitHeight
