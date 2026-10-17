import Mordor.Cut
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Order.Cofinal

/-!
# Sharpness: a complete chain satisfies CL iff it is finite (log §22.2–§22.5)

* `escape` (Ladder Lemma, §22.2): a nonempty linear order without maximum has a monotone `s` with `x < s x`.
  The log uses "every linear order has a well-ordered cofinal subset"; here: the records of any well-order
  (`isCofinal_setOf_imp_lt`) form a cofinal set on which `<` agrees with the well-order, and `s x` is the least
  record above `x`.
* `ladder` (§22.3): below a limit `λ > ⊥`, `F x y = x` (y < λ), `s x` (x < λ ≤ y), `max x y` (λ ≤ x, y) commutes
  with `m = ⊥ ≠ ⊤ = n`.
* `coladder`: above a co-limit `κ < ⊤`, the mirror `F x y = y` (κ < x), `t y` (x ≤ κ < y), `min x y` (x, y ≤ κ).
  This is `Fᵈ` of the ladder on `Cᵒᵖ` (§22.1, §22.5) written out, which avoids transporting along `αᵒᵈᵒᵈ`.
* `infinitude` (§22.4): an infinite complete chain has a limit `λ > ⊥` or a co-limit `κ < ⊤`.
  Proof here: `S = {x | [⊥, x] finite}` has `sSup S ∈ S` (predecessors) and `sSup S = ⊤` (successors).
* `sharpness`: CL holds for every monotone `F` on a complete chain `C` iff `C` is finite.
-/

namespace Mordor
open Classical

/-- **Ladder (Escape) Lemma.** -/
theorem escape {β : Type*} [LinearOrder β] [Nonempty β] [NoMaxOrder β] :
    ∃ s : β → β, Monotone s ∧ ∀ x, x < s x := by
  let r : β → β → Prop := WellOrderingRel
  have wf : WellFounded r := WellOrderingRel.isWellOrder.wf
  let W : Set β := {a | ∀ b, r b a → b < a}
  have hW : ∀ a, ∃ w ∈ W, a ≤ w := isCofinal_setOf_imp_lt r
  have hne : ∀ x : β, {w | w ∈ W ∧ x < w}.Nonempty := fun x => by
    obtain ⟨y, hy⟩ := exists_gt x
    obtain ⟨w, hw, hyw⟩ := hW y
    exact ⟨w, hw, hy.trans_le hyw⟩
  refine ⟨fun x => wf.min _ (hne x), fun x x' hxx' => ?_, fun x => (wf.min_mem _ (hne x)).2⟩
  have hm := wf.min_mem _ (hne x)
  have hm' := wf.min_mem _ (hne x')
  have hsub : wf.min _ (hne x') ∈ {w | w ∈ W ∧ x < w} := ⟨hm'.1, hxx'.trans_lt hm'.2⟩
  rcases trichotomous_of r (wf.min _ (hne x)) (wf.min _ (hne x')) with h | h | h
  · exact (hm'.1 _ h).le
  · exact h.le
  · exact absurd h (wf.not_lt_min _ (hne x) hsub)

theorem escape_down {β : Type*} [LinearOrder β] [Nonempty β] [NoMinOrder β] :
    ∃ t : β → β, Monotone t ∧ ∀ x, t x < x := by
  obtain ⟨s, hs, hlt⟩ := escape (β := βᵒᵈ)
  exact ⟨fun x => OrderDual.ofDual (s (OrderDual.toDual x)), fun x x' h => hs.dual h, fun x => hlt _⟩

variable {C : Type*} [CompleteLinearOrder C]

/-- The ladder bifunction, from an escape `s` below `λ`. -/
def ladderF (lam : C) (s : C → C) (hs : ∀ x, x < lam → x < s x) (hl : ∀ x, x < lam → s x < lam)
    (hm : ∀ x x', x ≤ x' → x' < lam → s x ≤ s x') : C →o C →o C where
  toFun x :=
    { toFun := fun y => if y < lam then x else if x < lam then s x else max x y
      monotone' := fun y y' h => by
        by_cases hy : y < lam
        · by_cases hy' : y' < lam
          · simp [hy, hy']
          · by_cases hx : x < lam
            · simp [hy, hy', hx, (hs x hx).le]
            · simp [hy, hy', hx]
        · have hy' : ¬ y' < lam := fun h' => hy (lt_of_le_of_lt h h')
          by_cases hx : x < lam
          · simp [hy, hy', hx]
          · simp only [hy, hy', hx, if_false]; exact max_le_max le_rfl h }
  monotone' := fun x x' h y => by
    show (if y < lam then x else if x < lam then s x else max x y) ≤
      (if y < lam then x' else if x' < lam then s x' else max x' y)
    by_cases hy : y < lam
    · simp [hy, h]
    · by_cases hx' : x' < lam
      · have hx : x < lam := lt_of_le_of_lt h hx'
        simp only [hy, hx, hx', if_false, if_true]; exact hm x x' h hx'
      · by_cases hx : x < lam
        · simp only [hy, hx, hx', if_false, if_true]
          exact (hl x hx).le.trans ((not_lt.mp hx').trans (le_max_left _ _))
        · simp only [hy, hx, hx', if_false]; exact max_le_max h le_rfl

/-- **Ladder Construction (§22.3).** -/
theorem ladder (lam : C) (hbot : ⊥ < lam) (hlim : ∀ x < lam, ∃ y, x < y ∧ y < lam) :
    ∃ F : C →o C →o C, (∀ x, a F (b F x) = b F (a F x)) ∧ m F ≠ n F := by
  -- an escape map on `Iio lam`, extended by the identity
  haveI : Nonempty (Set.Iio lam) := ⟨⟨⊥, hbot⟩⟩
  haveI : NoMaxOrder (Set.Iio lam) := ⟨fun ⟨x, hx⟩ => by
    obtain ⟨y, hxy, hy⟩ := hlim x hx; exact ⟨⟨y, hy⟩, hxy⟩⟩
  obtain ⟨s', hs'm, hs'lt⟩ := escape (β := Set.Iio lam)
  let s : C → C := fun x => if h : x < lam then (s' ⟨x, h⟩ : C) else x
  have hs : ∀ x, x < lam → x < s x := fun x h => by simp only [s, h, dif_pos]; exact hs'lt ⟨x, h⟩
  have hl : ∀ x, x < lam → s x < lam := fun x h => by simp only [s, h, dif_pos]; exact (s' ⟨x, h⟩).2
  have hm : ∀ x x', x ≤ x' → x' < lam → s x ≤ s x' := fun x x' hxx h' => by
    have h : x < lam := lt_of_le_of_lt hxx h'
    simp only [s, h, h', dif_pos]; exact hs'm (show (⟨x, h⟩ : Set.Iio lam) ≤ ⟨x', h'⟩ from hxx)
  let F := ladderF lam s hs hl hm
  have hF : ∀ x y, F x y = if y < lam then x else if x < lam then s x else max x y := fun _ _ => rfl
  -- derived maps
  have ha_lt : ∀ x, x < lam → a F x = x := fun x hx => by
    apply le_antisymm
    · show (F x).gfp ≤ x
      apply OrderHom.gfp_le; intro c hc
      by_cases hcl : c < lam
      · rwa [hF, if_pos hcl] at hc
      · rw [hF, if_neg hcl, if_pos hx] at hc
        exact absurd (lt_of_le_of_lt hc (hl x hx)) hcl
    · exact le_a (by rw [hF, if_pos hx])
  have ha_ge : ∀ x, ¬ x < lam → a F x = ⊤ := fun x hx =>
    top_le_iff.mp (le_a (by rw [hF, if_neg (not_lt.mpr le_top), if_neg hx]; exact le_max_right _ _))
  have hb_lt : ∀ y, y < lam → b F y = ⊥ := fun y hy =>
    le_bot_iff.mp (b_le (by rw [hF, if_pos hy]))
  have hb_ge : ∀ y, ¬ y < lam → b F y = y := fun y hy => by
    apply le_antisymm
    · exact b_le (by rw [hF, if_neg hy, if_neg hy, max_self])
    · show y ≤ (col F y).lfp
      apply OrderHom.le_lfp; intro c hc
      change F c y ≤ c at hc
      by_cases hcl : c < lam
      · rw [hF, if_neg hy, if_pos hcl] at hc; exact absurd hc (not_le.mpr (hs c hcl))
      · rw [hF, if_neg hy, if_neg hcl] at hc; exact (le_max_right _ _).trans hc
  have htop : ¬ (⊤ : C) < lam := not_lt.mpr le_top
  refine ⟨F, fun x => ?_, ?_⟩
  · by_cases hx : x < lam
    · rw [hb_lt x hx, ha_lt ⊥ hbot, ha_lt x hx, hb_lt x hx]
    · rw [hb_ge x hx, ha_ge x hx, hb_ge ⊤ htop]
  · have hm0 : m F = ⊥ := le_bot_iff.mp ((a F).lfp_le (ha_lt ⊥ hbot).le)
    have hn0 : n F = ⊤ := top_le_iff.mp ((b F).le_gfp (hb_ge ⊤ htop).ge)
    rw [hm0, hn0]; exact (hbot.trans_le le_top).ne

/-- The co-ladder bifunction, from a downward escape `t` above `κ`. -/
def coladderF (k : C) (t : C → C) (ht : ∀ y, k < y → t y < y) (hk : ∀ y, k < y → k < t y)
    (hm : ∀ y y', y ≤ y' → k < y → t y ≤ t y') : C →o C →o C where
  toFun x :=
    { toFun := fun y => if k < x then y else if k < y then t y else min x y
      monotone' := fun y y' h => by
        by_cases hx : k < x
        · simp [hx, h]
        · by_cases hy : k < y
          · have hy' : k < y' := lt_of_lt_of_le hy h
            simp only [hx, hy, hy', if_false, if_true]; exact hm y y' h hy
          · by_cases hy' : k < y'
            · simp only [hx, hy, hy', if_false, if_true]
              exact (min_le_right _ _).trans ((not_lt.mp hy).trans (hk y' hy').le)
            · simp only [hx, hy, hy', if_false]; exact min_le_min le_rfl h }
  monotone' := fun x x' h y => by
    show (if k < x then y else if k < y then t y else min x y) ≤
      (if k < x' then y else if k < y then t y else min x' y)
    by_cases hx : k < x
    · have hx' : k < x' := lt_of_lt_of_le hx h
      simp [hx, hx']
    · by_cases hx' : k < x'
      · by_cases hy : k < y
        · simp only [hx, hx', hy, if_false, if_true]; exact (ht y hy).le
        · simp only [hx, hx', hy, if_false, if_true]; exact min_le_right _ _
      · by_cases hy : k < y
        · simp [hx, hx', hy]
        · simp only [hx, hx', hy, if_false]; exact min_le_min h le_rfl

/-- **Co-ladder (the dual Ladder Construction).** -/
theorem coladder (k : C) (htop : k < ⊤) (hcolim : ∀ x, k < x → ∃ y, k < y ∧ y < x) :
    ∃ F : C →o C →o C, (∀ x, a F (b F x) = b F (a F x)) ∧ m F ≠ n F := by
  haveI : Nonempty (Set.Ioi k) := ⟨⟨⊤, htop⟩⟩
  haveI : NoMinOrder (Set.Ioi k) := ⟨fun ⟨x, hx⟩ => by
    obtain ⟨y, hy, hyx⟩ := hcolim x hx; exact ⟨⟨y, hy⟩, hyx⟩⟩
  obtain ⟨t', ht'm, ht'lt⟩ := escape_down (β := Set.Ioi k)
  let t : C → C := fun y => if h : k < y then (t' ⟨y, h⟩ : C) else y
  have ht : ∀ y, k < y → t y < y := fun y h => by simp only [t, h, dif_pos]; exact ht'lt ⟨y, h⟩
  have hk : ∀ y, k < y → k < t y := fun y h => by simp only [t, h, dif_pos]; exact (t' ⟨y, h⟩).2
  have hm : ∀ y y', y ≤ y' → k < y → t y ≤ t y' := fun y y' hyy h => by
    have h' : k < y' := lt_of_lt_of_le h hyy
    simp only [t, h, h', dif_pos]; exact ht'm (show (⟨y, h⟩ : Set.Ioi k) ≤ ⟨y', h'⟩ from hyy)
  let F := coladderF k t ht hk hm
  have hF : ∀ x y, F x y = if k < x then y else if k < y then t y else min x y := fun _ _ => rfl
  have ha_gt : ∀ x, k < x → a F x = ⊤ := fun x hx =>
    top_le_iff.mp (le_a (by rw [hF, if_pos hx]))
  have ha_le : ∀ x, ¬ k < x → a F x = x := fun x hx => by
    apply le_antisymm
    · show (F x).gfp ≤ x
      apply OrderHom.gfp_le; intro c hc
      rw [hF, if_neg hx] at hc
      by_cases hc' : k < c
      · rw [if_pos hc'] at hc; exact absurd hc (not_le.mpr (ht c hc'))
      · rw [if_neg hc'] at hc; exact hc.trans (min_le_left _ _)
    · exact le_a (by rw [hF, if_neg hx, if_neg hx, min_self])
  have hb_le : ∀ y, ¬ k < y → b F y = ⊥ := fun y hy =>
    le_bot_iff.mp (b_le (by
      rw [hF, if_neg (not_lt.mpr bot_le), if_neg hy]; exact min_le_left _ _))
  have hb_gt : ∀ y, k < y → b F y = y := fun y hy => by
    apply le_antisymm
    · exact b_le (by rw [hF, if_pos hy])
    · show y ≤ (col F y).lfp
      apply OrderHom.le_lfp; intro c hc
      change F c y ≤ c at hc
      by_cases hc' : k < c
      · rwa [hF, if_pos hc'] at hc
      · rw [hF, if_neg hc', if_pos hy] at hc
        exact absurd (lt_of_lt_of_le (hk y hy) hc) hc'
  have hbot : ¬ k < (⊥ : C) := not_lt.mpr bot_le
  refine ⟨F, fun x => ?_, ?_⟩
  · by_cases hx : k < x
    · rw [hb_gt x hx, ha_gt x hx, hb_gt ⊤ htop]
    · rw [hb_le x hx, ha_le ⊥ hbot, ha_le x hx, hb_le x hx]
  · have hm0 : m F = ⊥ := le_bot_iff.mp ((a F).lfp_le (ha_le ⊥ hbot).le)
    have hn0 : n F = ⊤ := top_le_iff.mp ((b F).le_gfp (hb_gt ⊤ htop).ge)
    rw [hm0, hn0]; exact (bot_le.trans_lt htop).ne

/-- **Infinitude Lemma (§22.4).** -/
theorem infinitude [Infinite C] :
    (∃ lam : C, ⊥ < lam ∧ ∀ x < lam, ∃ y, x < y ∧ y < lam) ∨
    (∃ k : C, k < ⊤ ∧ ∀ x, k < x → ∃ y, k < y ∧ y < x) := by
  by_contra hno
  push_neg at hno
  obtain ⟨hpred, hsucc⟩ := hno
  -- hpred: every λ > ⊥ has some x < λ with nothing strictly between; hsucc dually
  let S : Set C := {x | (Set.Icc ⊥ x).Finite}
  set s := sSup S with hs_def
  have hsS : s ∈ S := by
    by_cases h0 : s = ⊥
    · show (Set.Icc ⊥ s).Finite
      rw [h0, Set.Icc_self]; exact Set.finite_singleton _
    · obtain ⟨p, hp, hgap⟩ := hpred s (bot_lt_iff_ne_bot.mpr h0)
      obtain ⟨z, hzS, hpz⟩ : ∃ z ∈ S, p < z := by
        by_contra hz; push_neg at hz
        exact absurd (sSup_le hz) (not_le.mpr hp)
      have hzs : z ≤ s := le_sSup hzS
      rcases lt_or_eq_of_le hzs with hlt | heq
      · exact absurd hlt (not_lt.mpr (hgap z hpz))
      · exact heq ▸ hzS
  have hs_top : s = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hgap⟩ := hsucc s (lt_top_iff_ne_top.mpr hne)
    have hqS : q ∈ S := by
      show (Set.Icc ⊥ q).Finite
      apply (hsS.union (Set.finite_singleton q)).subset
      intro z ⟨hz0, hzq⟩
      rcases le_or_gt z s with hzs | hzs
      · exact Or.inl ⟨hz0, hzs⟩
      · rcases lt_or_eq_of_le hzq with hlt | heq
        · exact absurd (hgap z hzs) (not_le.mpr hlt)
        · exact Or.inr heq
    exact absurd (le_sSup hqS) (not_le.mpr hq)
  have : (Set.univ : Set C).Finite := by
    apply (hs_top ▸ hsS : (Set.Icc ⊥ (⊤ : C)).Finite).subset
    intro z _; exact ⟨bot_le, le_top⟩
  exact Set.infinite_univ this

/-- **Sharpness Theorem (§22.5).** -/
theorem sharpness :
    (∀ F : C →o C →o C, (∀ x, a F (b F x) = b F (a F x)) → m F = n F) ↔ Finite C := by
  constructor
  · intro hCL
    by_contra hfin
    haveI : Infinite C := not_finite_iff_infinite.mp hfin
    rcases infinitude (C := C) with ⟨lam, hbot, hlim⟩ | ⟨k, htop, hcolim⟩
    · obtain ⟨F, hc, hne⟩ := ladder lam hbot hlim; exact hne (hCL F hc)
    · obtain ⟨F, hc, hne⟩ := coladder k htop hcolim; exact hne (hCL F hc)
  · intro hfin F hc
    exact fcl F hc

end Mordor
