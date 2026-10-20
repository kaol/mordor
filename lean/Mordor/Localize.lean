import Mordor.FinGenAll

/-!
# Localization of the Cut Lemma (log §34.3p)

Without a witness, every cell value is pinned near the corner `c = F s t` of a box `[s, t]`: for `x ∈ D`, `y ∉ D`
in the box, `F s y ≤ F x y ≤ F x t` with `s < F s y ≤ c ≤ F x t < t`, so `F x y ⊓ c ≠ s` and `F x y ⊔ c ≠ t`
(`confine`). Three consequences:

* `capture_contra`: any finite table capturing the cells is contradictory (from `FinGen.captured`).
* `cut_of_finite_nbhd`: if `N(c) = {z | z ⊓ c ≠ ⊥ ∧ z ⊔ c ≠ ⊤}` is finite for every `c ∉ {⊥, ⊤}`, the Cut Lemma holds,
  on any bounded lattice, with no chain condition. This covers horizontal sums of finite lattices (`M_ω`,
  `⊥ ⊕ (⊔ₙ Cₙ) ⊕ ⊤`, …).
* `cut_localize`: on a chain-finite complete lattice the box can be shrunk to `[s, ⋁N(c)]` (if `c ∉ D`) or
  `[⋀N(c), t]` (if `c ∈ D`); a counterexample must reach a *stuck* box where no shrinking, no spine move and no finite capture applies.
-/

namespace Mordor.Localize
open Finset Classical
set_option linter.unusedSectionVars false

section Capture
variable {α : Type*} [Lattice α] [BoundedOrder α]

/-- **Finite capture is contradictory.** Table elements `TD ⊆ D`, `TU ⊆ Dᶜ` inside regions `X` (closed under `⊓`)
and `Y` (closed under `⊔`); every cell value with `x ∈ X ∩ D`, `y ∈ Y \ D` is below some `p ∈ TD` or above some
`u ∈ TU`; no such cell is a witness. -/
theorem capture_contra {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (TD TU : Finset α)
    (hTD : ∀ p ∈ TD, p ∈ D) (hTU : ∀ u ∈ TU, u ∉ D) (hne : TD.Nonempty) (hne' : TU.Nonempty)
    (X Y : Set α) (hTX : ∀ p ∈ TD, p ∈ X) (hTY : ∀ u ∈ TU, u ∈ Y)
    (hX : ∀ a ∈ X, ∀ b ∈ X, a ⊓ b ∈ X) (hY : ∀ a ∈ Y, ∀ b ∈ Y, a ⊔ b ∈ Y)
    (hcap : ∀ x ∈ X, ∀ y ∈ Y, x ∈ D → y ∉ D →
      (F x y ∈ D → ∃ p ∈ TD, F x y ≤ p) ∧ (F x y ∉ D → ∃ u ∈ TU, u ≤ F x y))
    (hno : ∀ x ∈ X, ∀ y ∈ Y, x ∈ D → y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) : False := by
  let p : Fin TD.card → α := fun i => (TD.equivFin.symm i : α)
  let u : Fin TU.card → α := fun j => (TU.equivFin.symm j : α)
  have hp : ∀ i, p i ∈ TD := fun i => (TD.equivFin.symm i).2
  have hu : ∀ j, u j ∈ TU := fun j => (TU.equivFin.symm j).2
  have hpS : ∀ q ∈ TD, ∃ i, p i = q := fun q hq => ⟨TD.equivFin ⟨q, hq⟩, by simp [p]⟩
  have huS : ∀ q ∈ TU, ∃ j, u j = q := fun q hq => ⟨TU.equivFin ⟨q, hq⟩, by simp [u]⟩
  have hxX : ∀ A : Finset (Fin TD.card), A.Nonempty → A.inf p ∈ X := fun A hA => by
    rw [← Finset.inf'_eq_inf hA]; exact Finset.inf'_mem X hX A hA p fun i _ => hTX _ (hp i)
  have hyY : ∀ B : Finset (Fin TU.card), B.Nonempty → B.sup u ∈ Y := fun B hB => by
    rw [← Finset.sup'_eq_sup hB]; exact Finset.sup'_mem Y hY B hB u fun j _ => hTY _ (hu j)
  have hxD : ∀ A : Finset (Fin TD.card), A.Nonempty → A.inf p ∈ D := fun A ⟨i, hi⟩ =>
    hD _ _ (Finset.inf_le hi) (hTD _ (hp i))
  have hyD : ∀ B : Finset (Fin TU.card), B.Nonempty → B.sup u ∉ D := fun B ⟨j, hj⟩ h =>
    hTU _ (hu j) (hD _ _ (Finset.le_sup hj) h)
  refine FinGen.captured (D := D) (p := p) (u := u) (card_pos.2 hne) (card_pos.2 hne') hF
    (fun A B hA hB hz => ?_) (fun A B hA hB hz => ?_) (fun A B hA hB h => ?_) (fun A B hA hB h => ?_)
  · obtain ⟨q, hq, hle⟩ := (hcap _ (hxX A hA) _ (hyY B hB) (hxD A hA) (hyD B hB)).1 hz
    obtain ⟨i, rfl⟩ := hpS q hq; exact ⟨i, hle⟩
  · obtain ⟨q, hq, hle⟩ := (hcap _ (hxX A hA) _ (hyY B hB) (hxD A hA) (hyD B hB)).2 hz
    obtain ⟨j, rfl⟩ := huS q hq; exact ⟨j, hle⟩
  · exact (hno _ (hxX A hA) _ (hyY B hB) (hxD A hA) (hyD B hB)).1 (Finset.le_inf h)
  · exact (hno _ (hxX A hA) _ (hyY B hB) (hxD A hA) (hyD B hB)).2 (Finset.sup_le h)

end Capture

section Box
variable {α : Type*} [Lattice α] {F : α → α → α} {D : Set α}
set_option linter.unusedSectionVars false

/-- The box problem: `s ∈ D`, `t ∉ D`, and cells of `[s, t]` take values in `[s, t]`. -/
def Prob (F : α → α → α) (D : Set α) (s t : α) : Prop :=
  s ∈ D ∧ t ∉ D ∧ s ≤ t ∧ ∀ x y, x ∈ D → y ∉ D → s ≤ x → x ≤ t → s ≤ y → y ≤ t → s ≤ F x y ∧ F x y ≤ t

/-- No witness among the cells of `[s, t]`. -/
def NoW (F : α → α → α) (D : Set α) (s t : α) : Prop :=
  ∀ x y, x ∈ D → y ∉ D → s ≤ x → x ≤ t → s ≤ y → y ≤ t → ¬ F x y ≤ x ∧ ¬ y ≤ F x y

/-- The neighbourhood of the corner `c = F s t` in `[s, t]`. -/
def V (F : α → α → α) (s t : α) : Set α := {z | s ≤ z ∧ z ≤ t ∧ z ⊓ F s t ≠ s ∧ z ⊔ F s t ≠ t}

variable (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
include hF hD

/-- **Confinement.** Every cell value lies in the corner's neighbourhood. -/
theorem confine {s t : α} (hP : Prob F D s t) (hN : NoW F D s t) {x y : α} (hx : x ∈ D) (hy : y ∉ D)
    (hsx : s ≤ x) (hxt : x ≤ t) (hsy : s ≤ y) (hyt : y ≤ t) : F x y ∈ V F s t := by
  obtain ⟨hs, ht, hst, hbox⟩ := hP
  have hw := hbox s y hs hy le_rfl hst hsy hyt
  have hw' := hbox x t hx ht hsx hxt hst le_rfl
  have hz := hbox x y hx hy hsx hxt hsy hyt
  have n1 := (hN s y hs hy le_rfl hst hsy hyt).1
  have n2 := (hN x t hx ht hsx hxt hst le_rfl).2
  refine ⟨hz.1, hz.2, fun h => n1 ?_, fun h => n2 ?_⟩
  · -- F s y ≤ F x y ⊓ F s t = s
    exact (le_inf (hF _ _ _ _ hsx le_rfl) (hF _ _ _ _ le_rfl hyt)).trans h.le
  · exact h.ge.trans (sup_le (hF _ _ _ _ le_rfl hyt) (hF _ _ _ _ hsx le_rfl))

theorem corner_mem {s t : α} (hP : Prob F D s t) (hN : NoW F D s t) : F s t ∈ V F s t :=
  confine hF hD hP hN hP.1 hP.2.1 le_rfl hP.2.2.1 hP.2.2.1 le_rfl

/-- **Base case.** If the neighbourhood is captured by finite tables inside the box, the box has a witness. -/
theorem box_capture [BoundedOrder α] {s t : α} (hP : Prob F D s t) (hN : NoW F D s t) (TD TU : Finset α)
    (hTD : ∀ p ∈ TD, p ∈ D ∧ s ≤ p ∧ p ≤ t) (hTU : ∀ u ∈ TU, u ∉ D ∧ s ≤ u ∧ u ≤ t)
    (hcD : ∀ z ∈ V F s t, z ∈ D → ∃ p ∈ TD, z ≤ p) (hcU : ∀ z ∈ V F s t, z ∉ D → ∃ u ∈ TU, u ≤ z) : False := by
  obtain ⟨hs, ht, hst, -⟩ := id hP
  refine capture_contra hF hD (insert s TD) (insert t TU) ?_ ?_ (insert_nonempty _ _) (insert_nonempty _ _)
    (Set.Icc s t) (Set.Icc s t) ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp; rcases mem_insert.1 hp with rfl | hp; exacts [hs, (hTD p hp).1]
  · intro u hu; rcases mem_insert.1 hu with rfl | hu; exacts [ht, (hTU u hu).1]
  · intro p hp; rcases mem_insert.1 hp with rfl | hp; exacts [⟨le_rfl, hst⟩, ⟨(hTD p hp).2.1, (hTD p hp).2.2⟩]
  · intro u hu; rcases mem_insert.1 hu with rfl | hu; exacts [⟨hst, le_rfl⟩, ⟨(hTU u hu).2.1, (hTU u hu).2.2⟩]
  · exact fun a ha b hb => ⟨le_inf ha.1 hb.1, inf_le_left.trans ha.2⟩
  · exact fun a ha b hb => ⟨ha.1.trans le_sup_left, sup_le ha.2 hb.2⟩
  · intro x hx y hy hxD hyD
    have hz := confine hF hD hP hN hxD hyD hx.1 hx.2 hy.1 hy.2
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨p, hp, hle⟩ := hcD _ hz h; exact ⟨p, mem_insert_of_mem hp, hle⟩
    · obtain ⟨u, hu, hle⟩ := hcU _ hz h; exact ⟨u, mem_insert_of_mem hu, hle⟩
  · exact fun x hx y hy hxD hyD => hN x y hxD hyD hx.1 hx.2 hy.1 hy.2

theorem box_finite [BoundedOrder α] {s t : α} (hP : Prob F D s t) (hN : NoW F D s t) (hV : (V F s t).Finite) :
    False := by
  refine box_capture hF hD hP hN (hV.toFinset.filter (· ∈ D)) (hV.toFinset.filter (· ∉ D)) ?_ ?_ ?_ ?_
  · intro p hp; simp only [mem_filter, Set.Finite.mem_toFinset] at hp; exact ⟨hp.2, hp.1.1, hp.1.2.1⟩
  · intro u hu; simp only [mem_filter, Set.Finite.mem_toFinset] at hu; exact ⟨hu.2, hu.1.1, hu.1.2.1⟩
  · intro z hz hzD; exact ⟨z, by simp [hz, hzD], le_rfl⟩
  · intro z hz hzD; exact ⟨z, by simp [hz, hzD], le_rfl⟩

end Box

section Top
variable {α : Type*} [Lattice α] [BoundedOrder α]

/-- **Finite neighbourhoods.** If every `c ∉ {⊥, ⊤}` has only finitely many `z` with `z ⊓ c ≠ ⊥` and `z ⊔ c ≠ ⊤`,
every cut of every monotone `F` has a witness. No chain condition. -/
theorem cut_of_finite_nbhd (hfin : ∀ c : α, c ≠ ⊥ → c ≠ ⊤ → {z : α | z ⊓ c ≠ ⊥ ∧ z ⊔ c ≠ ⊤}.Finite)
    (F : α → α → α) (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (D : Set α) (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  have hP : Prob F D ⊥ ⊤ := ⟨hbot, htop, bot_le, fun _ _ _ _ _ _ _ _ => ⟨bot_le, le_top⟩⟩
  have hN : NoW F D ⊥ ⊤ := fun x y hx hy _ _ _ _ => hno x hx y hy
  have hc := corner_mem hF hD hP hN
  have hc1 : F ⊥ ⊤ ≠ ⊥ := fun h => hc.2.2.1 (by rw [h, inf_idem])
  have hc2 : F ⊥ ⊤ ≠ ⊤ := fun h => hc.2.2.2 (by rw [h, sup_idem])
  refine box_finite hF hD hP hN ((hfin _ hc1 hc2).subset fun z hz => ⟨hz.2.2.1, hz.2.2.2⟩)

end Top

section Recursion
variable {α : Type*} [CompleteLattice α] {F : α → α → α} {D : Set α}
variable (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
include hF hD

theorem shrink_top {s t : α} (hP : Prob F D s t) (hN : NoW F D s t) (hc : F s t ∉ D) :
    Prob F D s (sSup (V F s t)) ∧ NoW F D s (sSup (V F s t)) := by
  have hcV := corner_mem hF hD hP hN
  have hct : F s t ≤ sSup (V F s t) := le_sSup hcV
  have htt : sSup (V F s t) ≤ t := sSup_le fun z hz => hz.2.1
  refine ⟨⟨hP.1, fun h => hc (hD _ _ hct h), hcV.1.trans hct, fun x y hx hy hsx hxt hsy hyt => ?_⟩,
    fun x y hx hy hsx hxt hsy hyt => hN x y hx hy hsx (hxt.trans htt) hsy (hyt.trans htt)⟩
  have hz := confine hF hD hP hN hx hy hsx (hxt.trans htt) hsy (hyt.trans htt)
  exact ⟨hz.1, le_sSup hz⟩

theorem shrink_bot {s t : α} (hP : Prob F D s t) (hN : NoW F D s t) (hc : F s t ∈ D) :
    Prob F D (sInf (V F s t)) t ∧ NoW F D (sInf (V F s t)) t := by
  have hcV := corner_mem hF hD hP hN
  have hcs : sInf (V F s t) ≤ F s t := sInf_le hcV
  have hss : s ≤ sInf (V F s t) := le_sInf fun z hz => hz.1
  refine ⟨⟨hD _ _ hcs hc, hP.2.1, hcs.trans hcV.2.1, fun x y hx hy hsx hxt hsy hyt => ?_⟩,
    fun x y hx hy hsx hxt hsy hyt => hN x y hx hy (hss.trans hsx) hxt (hss.trans hsy) hyt⟩
  have hz := confine hF hD hP hN hx hy (hss.trans hsx) hxt (hss.trans hsy) hyt
  exact ⟨sInf_le hz, hz.2.1⟩

/-- **Spine move, lower end.** A point `s' ∈ D` of the box comparable with every point of the box can replace `s`:
a cell value below `s'` would be a witness. -/
theorem spine_bot {s t s' : α} (hP : Prob F D s t) (hN : NoW F D s t) (hs' : s' ∈ D) (hss : s ≤ s') (hst : s' ≤ t)
    (hcmp : ∀ z, s ≤ z → z ≤ t → z ≤ s' ∨ s' ≤ z) : Prob F D s' t ∧ NoW F D s' t := by
  refine ⟨⟨hs', hP.2.1, hst, fun x y hx hy hsx hxt hsy hyt => ?_⟩,
    fun x y hx hy hsx hxt hsy hyt => hN x y hx hy (hss.trans hsx) hxt (hss.trans hsy) hyt⟩
  have hz := hP.2.2.2 x y hx hy (hss.trans hsx) hxt (hss.trans hsy) hyt
  refine ⟨?_, hz.2⟩
  rcases hcmp _ hz.1 hz.2 with h | h
  · exact absurd (h.trans hsx) (hN x y hx hy (hss.trans hsx) hxt (hss.trans hsy) hyt).1
  · exact h

/-- **Spine move, upper end.** -/
theorem spine_top {s t t' : α} (hP : Prob F D s t) (hN : NoW F D s t) (ht' : t' ∉ D) (hst : s ≤ t') (htt : t' ≤ t)
    (hcmp : ∀ z, s ≤ z → z ≤ t → z ≤ t' ∨ t' ≤ z) : Prob F D s t' ∧ NoW F D s t' := by
  refine ⟨⟨hP.1, ht', hst, fun x y hx hy hsx hxt hsy hyt => ?_⟩,
    fun x y hx hy hsx hxt hsy hyt => hN x y hx hy hsx (hxt.trans htt) hsy (hyt.trans htt)⟩
  have hz := hP.2.2.2 x y hx hy hsx (hxt.trans htt) hsy (hyt.trans htt)
  refine ⟨hz.1, ?_⟩
  rcases hcmp _ hz.1 hz.2 with h | h
  · exact h
  · exact absurd (hyt.trans h) (hN x y hx hy hsx (hxt.trans htt) hsy (hyt.trans htt)).2

/-- **Localization.** On a chain-finite complete lattice a cut has a witness unless the box recursion gets
*stuck*: some reachable box `[s, t]` cannot be closed directly (the `False` alternative: e.g. a finite capture of
the corner neighbourhood `V`, `box_capture`, or a reset, `Hubs.box_reset`), cannot shrink (`⋁V = t` when the corner
is outside `D`, `⋀V = s` when it is inside), and has no interior spine point on the correct side of the cut. The
hypothesis `halt` rules this out. -/
theorem cut_localize [WellFoundedLT α] [WellFoundedGT α] (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (halt : ∀ s t, Prob F D s t → NoW F D s t → False ∨
      (F s t ∉ D ∧ sSup (V F s t) < t) ∨ (F s t ∈ D ∧ s < sInf (V F s t)) ∨
      (∃ s', s' ∈ D ∧ s < s' ∧ s' ≤ t ∧ ∀ z, s ≤ z → z ≤ t → z ≤ s' ∨ s' ≤ z) ∨
      (∃ t', t' ∉ D ∧ s ≤ t' ∧ t' < t ∧ ∀ z, s ≤ z → z ≤ t → z ≤ t' ∨ t' ≤ z)) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  suffices key : ∀ t s, Prob F D s t → NoW F D s t → False from
    key ⊤ ⊥ ⟨hbot, htop, bot_le, fun _ _ _ _ _ _ _ _ => ⟨bot_le, le_top⟩⟩
      (fun x y hx hy _ _ _ _ => hno x hx y hy)
  intro t
  induction t using WellFoundedLT.induction with
  | _ t iht =>
    intro s
    induction s using WellFoundedGT.induction with
    | _ s ihs =>
      intro hP hN
      rcases halt s t hP hN with h | ⟨hc, hlt⟩ | ⟨hc, hlt⟩ |
          ⟨s', hs', hlt, hst, hcmp⟩ | ⟨t', ht', hst, hlt, hcmp⟩
      · exact h
      · obtain ⟨hP', hN'⟩ := shrink_top hF hD hP hN hc
        exact iht _ hlt s hP' hN'
      · obtain ⟨hP', hN'⟩ := shrink_bot hF hD hP hN hc
        exact ihs _ hlt hP' hN'
      · obtain ⟨hP', hN'⟩ := spine_bot hF hD hP hN hs' hlt.le hst hcmp
        exact ihs _ hlt hP' hN'
      · obtain ⟨hP', hN'⟩ := spine_top hF hD hP hN ht' hst hlt.le hcmp
        exact iht _ hlt s hP' hN'

/-- **Box criterion (lattice level).** On a chain-finite complete lattice the Cut Lemma holds if every box `[s, t]`
has an interior spine point, or else every interior `c` has a finite neighbourhood `V`, or one with `⋁V < t` and
`⋀V > s`. -/
theorem cut_of_box_criterion [WellFoundedLT α] [WellFoundedGT α]
    (hcrit : ∀ s t c : α, s < c → c < t →
      (∃ p, s < p ∧ p < t ∧ ∀ z, s ≤ z → z ≤ t → z ≤ p ∨ p ≤ z) ∨
      {z | s ≤ z ∧ z ≤ t ∧ z ⊓ c ≠ s ∧ z ⊔ c ≠ t}.Finite ∨
      (sSup {z | s ≤ z ∧ z ≤ t ∧ z ⊓ c ≠ s ∧ z ⊔ c ≠ t} < t ∧
        s < sInf {z | s ≤ z ∧ z ≤ t ∧ z ⊓ c ≠ s ∧ z ⊔ c ≠ t}))
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) : ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  refine cut_localize hF hD hbot htop fun s t hP hN => ?_
  have hc := corner_mem hF hD hP hN
  have hsc : s < F s t := lt_of_le_of_ne hc.1 fun h => hc.2.2.1 (by rw [← h, inf_idem])
  have hct : F s t < t := lt_of_le_of_ne hc.2.1 fun h => hc.2.2.2 (by rw [h, sup_idem])
  rcases hcrit s t (F s t) hsc hct with ⟨p, hsp, hpt, hcmp⟩ | hfin | ⟨h1, h2⟩
  · by_cases hpD : p ∈ D
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hpD, hsp, hpt.le, hcmp⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hpD, hsp.le, hpt, hcmp⟩)))
  · exact Or.inl (box_finite hF hD hP hN hfin)
  · by_cases hcD : F s t ∈ D
    · exact Or.inr (Or.inr (Or.inl ⟨hcD, h2⟩))
    · exact Or.inr (Or.inl ⟨hcD, h1⟩)

end Recursion

end Mordor.Localize

namespace Mordor
open Localize

/-- **CL on complete lattices with finite neighbourhoods** (no chain condition assumed). -/
theorem semi_of_finite_nbhd {α : Type*} [CompleteLattice α]
    (hfin : ∀ c : α, c ≠ ⊥ → c ≠ ⊤ → {z : α | z ⊓ c ≠ ⊥ ∧ z ⊔ c ≠ ⊤}.Finite)
    (F : α →o α →o α) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_of_finite_nbhd hfin (fun x y => F x y) (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy))
    D (fun x y h hy => hD h hy) (hD bot_le hd) (fun ht => hu (hD le_top ht))


/-- **Semi-CL (hence CL) under the box criterion**, on chain-finite complete lattices. -/
theorem semi_of_box_criterion {α : Type*} [CompleteLattice α] [WellFoundedLT α] [WellFoundedGT α]
    (hcrit : ∀ s t c : α, s < c → c < t →
      (∃ p, s < p ∧ p < t ∧ ∀ z, s ≤ z → z ≤ t → z ≤ p ∨ p ≤ z) ∨
      {z | s ≤ z ∧ z ≤ t ∧ z ⊓ c ≠ s ∧ z ⊔ c ≠ t}.Finite ∨
      (sSup {z | s ≤ z ∧ z ≤ t ∧ z ⊓ c ≠ s ∧ z ⊔ c ≠ t} < t ∧
        s < sInf {z | s ≤ z ∧ z ≤ t ∧ z ⊓ c ≠ s ∧ z ⊔ c ≠ t}))
    (F : α →o α →o α) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_of_box_criterion (F := fun x y => F x y)
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x y h hy => hD h hy) hcrit
    (hD bot_le hd) (fun ht => hu (hD le_top ht))

end Mordor
