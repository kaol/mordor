import Mordor.TwoSided
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Finite.Prod

/-!
# One crossing strip (log §34.3x)

`TwoSided.cut_two_sided_capture` leaves only cuts crossing an infinite interval `[s, t]` (`s ∈ D`, `t ∉ D`). This file
removes a single crossing strip.

* `extend_mono`: a bifunction monotone on the cells `D × U` extends to a globally monotone one with the same cell
  values (left Kan extension by `sSup`).
* `core_finite`: if `[s, t]` is relatively end-finite, cells `x ≥ s`, `y ≤ t` take only finitely many values in
  `[s, t]`. Such values lie below `G x t ⊓ t ≠ t` and above `G s y ⊔ s ≠ s`; one of the two corner bounds
  `(G s t ⊓ t) ⊔ s` and `(G s t ⊔ s) ⊓ t` is proper.
* `strip_contra`: off those core cells a value in `[s, t]` can never take part in a witness (`z ≤ x` forces `x ≥ s`,
  `y ≤ z` forces `y ≤ t`). So, given finitely many values outside `[s, t]`:
  - lower strip values to `s ⊔ ⋁{outside values ≤ z}` where `x ≱ s`;
  - raise them to `t ⊓ ⋀{outside values ≥ z}` where `x ≥ s` and `y ≰ t`.

  This keeps monotonicity on cells and witness-freeness, and leaves finitely many values.
* `cut_one_strip`: finitely many hubs and co-hubs, every infinite interval `[w, v]` (`⊥ < w ≤ v < ⊤`) inside one
  relatively end-finite `[s, t]`, and a modularity condition at `s, t`, give Cut. This covers `Ω × C₃`
  (`s = (⊥, 1)`, `t = (⊤, 1)`; log §34.3x).
-/

namespace Mordor.Strip
open Finset Classical
set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] {D : Set α}

/-- **Extension.** Monotone on cells ⟹ globally monotone with the same cell values. -/
theorem extend_mono (H : α → α → α)
    (hH : ∀ x x' y y', x ∈ D → x' ∈ D → y ∉ D → y' ∉ D → x ≤ x' → y ≤ y' → H x y ≤ H x' y') :
    ∃ H' : α → α → α, (∀ x x' y y', x ≤ x' → y ≤ y' → H' x y ≤ H' x' y') ∧
      ∀ x ∈ D, ∀ y, y ∉ D → H' x y = H x y := by
  refine ⟨fun x y => sSup {z | ∃ x' y', x' ≤ x ∧ x' ∈ D ∧ y' ≤ y ∧ y' ∉ D ∧ z = H x' y'}, ?_, ?_⟩
  · intro x x' y y' hx hy
    refine sSup_le_sSup fun z ⟨a, b, ha, haD, hb, hbD, hz⟩ => ⟨a, b, ha.trans hx, haD, hb.trans hy, hbD, hz⟩
  · intro x hx y hy
    refine le_antisymm (sSup_le fun z ⟨a, b, ha, haD, hb, hbD, hz⟩ => hz ▸ hH a x b y haD hx hbD hy ha hb)
      (le_sSup ⟨x, y, le_rfl, hx, le_rfl, hy, rfl⟩)

variable {G : α → α → α}
variable (hG : ∀ x x' y y', x ≤ x' → y ≤ y' → G x y ≤ G x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
include hG hD

/-- **Core finiteness.** -/
theorem core_finite (nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ G x y ≤ x ∧ ¬ y ≤ G x y) {s t : α} (hs : s ∈ D)
    (ht : t ∉ D) (hst : s ≤ t)
    (hrelI : ∀ g, s ≤ g → g ≤ t → g ≠ t → (Set.Icc s g).Finite)
    (hrelJ : ∀ g, s ≤ g → g ≤ t → g ≠ s → (Set.Icc g t).Finite)
    (hmod : ∀ g, (g ⊓ t) ⊔ s = s → (g ⊔ s) ⊓ t = t → False) :
    {z | ∃ x ∈ D, ∃ y, y ∉ D ∧ s ≤ x ∧ y ≤ t ∧ z = G x y ∧ s ≤ z ∧ z ≤ t}.Finite := by
  by_cases hμ : (G s t ⊓ t) ⊔ s = s
  · -- lower corner bound `ν = (G s t ⊔ s) ⊓ t ≠ t`
    have hν := hmod _ hμ
    have hsν : s ≤ (G s t ⊔ s) ⊓ t := le_inf le_sup_right hst
    have hfin : (Set.Icc s ((G s t ⊔ s) ⊓ t) \ {s}).Finite := (hrelI _ hsν inf_le_right fun h => hν h).diff
    refine (hfin.biUnion fun n hn =>
      hrelJ n hn.1.1 (hn.1.2.trans inf_le_right) fun h => hn.2 h).subset ?_
    rintro z ⟨x, hx, y, hy, hsx, hyt, rfl, hsz, hzt⟩
    refine Set.mem_biUnion (x := G s y ⊔ s) ⟨⟨le_sup_right, le_inf (sup_le_sup_right (hG _ _ _ _ le_rfl hyt) _)
      (sup_le ((hG _ _ _ _ hsx le_rfl).trans hzt) hst)⟩, fun h => (nw s hs y hy).1
      (le_sup_left.trans (Set.mem_singleton_iff.1 h).le)⟩ ⟨sup_le (hG _ _ _ _ hsx le_rfl) hsz, hzt⟩
  · -- upper corner bound `μ = (G s t ⊓ t) ⊔ s ≠ s`
    have hμt : (G s t ⊓ t) ⊔ s ≤ t := sup_le inf_le_right hst
    have hfin : (Set.Icc ((G s t ⊓ t) ⊔ s) t \ {t}).Finite := (hrelJ _ le_sup_right hμt hμ).diff
    refine (hfin.biUnion fun m hm =>
      hrelI m (le_sup_right.trans hm.1.1) hm.1.2 fun h => hm.2 h).subset ?_
    rintro z ⟨x, hx, y, hy, hsx, hyt, rfl, hsz, hzt⟩
    refine Set.mem_biUnion (x := G x t ⊓ t) ⟨⟨sup_le (inf_le_inf_right _ (hG _ _ _ _ hsx le_rfl))
      (le_inf (hsz.trans (hG _ _ _ _ le_rfl hyt)) hst), inf_le_right⟩, fun h => (nw x hx t ht).2
      ((Set.mem_singleton_iff.1 h).ge.trans inf_le_left)⟩ ⟨hsz, le_inf (hG _ _ _ _ le_rfl hyt) hzt⟩

/-- **Strip removal.** Finitely many values outside `[s, t]` and finitely many core values inside it are
contradictory. -/
theorem strip_contra (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ G x y ≤ x ∧ ¬ y ≤ G x y) {s t : α}
    (hNS : {z | ∃ x ∈ D, ∃ y, y ∉ D ∧ z = G x y ∧ ¬ (s ≤ z ∧ z ≤ t)}.Finite)
    (hZ : {z | ∃ x ∈ D, ∃ y, y ∉ D ∧ s ≤ x ∧ y ≤ t ∧ z = G x y ∧ s ≤ z ∧ z ≤ t}.Finite) : False := by
  set NS := {z | ∃ x ∈ D, ∃ y, y ∉ D ∧ z = G x y ∧ ¬ (s ≤ z ∧ z ≤ t)} with hNSdef
  let N : Finset α := hNS.toFinset
  have memN : ∀ {z}, z ∈ N ↔ z ∈ NS := fun {z} => hNS.mem_toFinset
  let ψd : α → α := fun z => s ⊔ (N.filter (· ≤ z)).sup id
  let ψu : α → α := fun z => t ⊓ (N.filter (z ≤ ·)).inf id
  have ψd_le : ∀ z, s ≤ z → ψd z ≤ z := fun z hz =>
    sup_le hz (Finset.sup_le fun f hf => (Finset.mem_filter.1 hf).2)
  have le_ψu : ∀ z, z ≤ t → z ≤ ψu z := fun z hz =>
    le_inf hz (Finset.le_inf fun f hf => (Finset.mem_filter.1 hf).2)
  have ψd_mono : ∀ z z', z ≤ z' → ψd z ≤ ψd z' := fun z z' h =>
    sup_le_sup_left (Finset.sup_mono fun f hf =>
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2.trans h⟩) _
  have ψu_mono : ∀ z z', z ≤ z' → ψu z ≤ ψu z' := fun z z' h =>
    inf_le_inf_left _ (Finset.inf_mono fun f hf =>
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hf).1, h.trans (Finset.mem_filter.1 hf).2⟩)
  let S : α → Prop := fun z => s ≤ z ∧ z ≤ t
  let H : α → α → α := fun x y =>
    if S (G x y) then (if s ≤ x then (if y ≤ t then G x y else ψu (G x y)) else ψd (G x y)) else G x y
  -- monotone on cells
  have hH : ∀ x x' y y', x ∈ D → x' ∈ D → y ∉ D → y' ∉ D → x ≤ x' → y ≤ y' → H x y ≤ H x' y' := by
    intro x x' y y' hx hx' hy hy' hxx hyy
    have hzz := hG _ _ _ _ hxx hyy
    have hNz : ∀ {a b}, a ∈ D → b ∉ D → ¬ S (G a b) → G a b ∈ N := fun ha hb h =>
      memN.2 ⟨_, ha, _, hb, rfl, h⟩
    by_cases h1 : S (G x y) <;> by_cases h2 : S (G x' y') <;> simp only [H, h1, h2, if_true, if_false]
    · -- both in the strip
      by_cases hsx : s ≤ x
      · have hsx' : s ≤ x' := hsx.trans hxx
        by_cases hyt' : y' ≤ t
        · have hyt : y ≤ t := hyy.trans hyt'
          simp only [hsx, hsx', hyt, hyt', if_true]; exact hzz
        · simp only [hsx, hsx', hyt', if_true, if_false]
          by_cases hyt : y ≤ t
          · simp only [hyt, if_true]; exact hzz.trans (le_ψu _ h2.2)
          · simp only [hyt, if_false]; exact ψu_mono _ _ hzz
      · simp only [hsx, if_false]
        by_cases hsx' : s ≤ x'
        · simp only [hsx', if_true]
          by_cases hyt' : y' ≤ t
          · simp only [hyt', if_true]; exact (ψd_le _ h1.1).trans hzz
          · simp only [hyt', if_false]; exact (ψd_le _ h1.1).trans (hzz.trans (le_ψu _ h2.2))
        · simp only [hsx', if_false]; exact ψd_mono _ _ hzz
    · -- only the smaller value in the strip
      have hN' := hNz hx' hy' h2
      by_cases hsx : s ≤ x
      · simp only [hsx, if_true]
        by_cases hyt : y ≤ t
        · simp only [hyt, if_true]; exact hzz
        · simp only [hyt, if_false]
          exact inf_le_of_right_le (Finset.inf_le (f := id) (Finset.mem_filter.2 ⟨hN', hzz⟩))
      · simp only [hsx, if_false]; exact (ψd_le _ h1.1).trans hzz
    · -- only the larger value in the strip
      have hN := hNz hx hy h1
      by_cases hsx' : s ≤ x'
      · simp only [hsx', if_true]
        by_cases hyt' : y' ≤ t
        · simp only [hyt', if_true]; exact hzz
        · simp only [hyt', if_false]; exact hzz.trans (le_ψu _ h2.2)
      · simp only [hsx', if_false]
        exact le_sup_of_le_right (Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hN, hzz⟩))
    · exact hzz
  -- witness-free on cells
  have nwH : ∀ x ∈ D, ∀ y, y ∉ D → ¬ H x y ≤ x ∧ ¬ y ≤ H x y := by
    intro x hx y hy
    have h0 := nw x hx y hy
    by_cases h1 : S (G x y) <;> simp only [H, h1, if_true, if_false]
    · by_cases hsx : s ≤ x
      · simp only [hsx, if_true]
        by_cases hyt : y ≤ t
        · simp only [hyt, if_true]; exact h0
        · simp only [hyt, if_false]
          exact ⟨fun h => h0.1 ((le_ψu _ h1.2).trans h), fun h => hyt (h.trans inf_le_left)⟩
      · simp only [hsx, if_false]
        exact ⟨fun h => hsx (le_sup_left.trans h), fun h => h0.2 (h.trans (ψd_le _ h1.1))⟩
    · exact h0
  -- finitely many cell values
  let T₁ : Set α := (fun P : Finset α => s ⊔ P.sup id) '' (N.powerset : Set (Finset α))
  let T₂ : Set α := (fun P : Finset α => t ⊓ P.inf id) '' (N.powerset : Set (Finset α))
  have hval : ∀ x ∈ D, ∀ y, y ∉ D → H x y ∈ NS ∪ {z | ∃ x ∈ D, ∃ y, y ∉ D ∧ s ≤ x ∧ y ≤ t ∧ z = G x y ∧
      s ≤ z ∧ z ≤ t} ∪ T₁ ∪ T₂ := by
    intro x hx y hy
    by_cases h1 : S (G x y) <;> simp only [H, h1, if_true, if_false]
    · by_cases hsx : s ≤ x
      · simp only [hsx, if_true]
        by_cases hyt : y ≤ t
        · simp only [hyt, if_true]; exact Or.inl (Or.inl (Or.inr ⟨x, hx, y, hy, hsx, hyt, rfl, h1⟩))
        · simp only [hyt, if_false]
          exact Or.inr ⟨_, Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _)), rfl⟩
      · simp only [hsx, if_false]
        exact Or.inl (Or.inr ⟨_, Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _)), rfl⟩)
    · exact Or.inl (Or.inl (Or.inl ⟨x, hx, y, hy, rfl, h1⟩))
  obtain ⟨H', hH', hHH⟩ := extend_mono H hH
  obtain ⟨x, hx, y, hy, h⟩ := Pin.cut_of_values_in_finite hH' hD hbot htop _
    (((hNS.union hZ).union ((Finset.finite_toSet _).image _)).union ((Finset.finite_toSet _).image _))
    fun _ x hx y hy => hHH x hx y hy ▸ hval x hx y hy
  rw [hHH x hx y hy] at h
  exact h.elim (nwH x hx y hy).1 (nwH x hx y hy).2

end Mordor.Strip

namespace Mordor.Strip
open Classical

/-- **One crossing strip.** Finitely many hubs and co-hubs; every infinite interval `[w, v]` with `⊥ < w ≤ v < ⊤`
lies inside one interval `[s, t]` that is relatively end-finite and satisfies the modularity condition at `s, t`.
Then every cut has a witness. -/
theorem cut_one_strip {α : Type*} [CompleteLattice α] {F : α → α → α} {D : Set α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (hH : {g : α | (Set.Ici g).Infinite}.Finite) (hH' : {g : α | (Set.Iic g).Infinite}.Finite)
    {s t : α} (hst : s ≤ t)
    (hstrip : ∀ w v : α, w ≠ ⊥ → v ≠ ⊤ → w ≤ v → (Set.Icc w v).Infinite → s ≤ w ∧ v ≤ t)
    (hrelI : ∀ g, s ≤ g → g ≤ t → g ≠ t → (Set.Icc s g).Finite)
    (hrelJ : ∀ g, s ≤ g → g ≤ t → g ≠ s → (Set.Icc g t).Finite)
    (hmod : ∀ g, (g ⊓ t) ⊔ s = s → (g ⊔ s) ⊓ t = t → False) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_cases hcross : s ∈ D ∧ t ∉ D
  · obtain ⟨hs, ht⟩ := hcross
    by_contra hno
    push_neg at hno
    obtain ⟨G, hG, nwG, W, V, hW, hV, hW0, hV1, hval⟩ :=
      TwoSided.two_sided hF hD hbot htop hH hH' fun x hx y hy => hno x hx y hy
    -- values outside `[s, t]` lie in finite intervals
    let I : Set (α × α) := {p | p.1 ∈ W ∧ p.2 ∈ V ∧ (Set.Icc p.1 p.2).Finite}
    have hI : I.Finite := (hW.biUnion fun w _ => hV.image fun v => (w, v)).subset fun p hp =>
      Set.mem_biUnion hp.1 ⟨p.2, hp.2.1, rfl⟩
    refine strip_contra hG hD hbot htop nwG ((hI.biUnion fun p hp => hp.2.2).subset ?_)
      (core_finite hG hD nwG hs ht hst hrelI hrelJ hmod)
    rintro z ⟨x, hx, y, hy, rfl, hz⟩
    obtain ⟨w, hw, v, hv, h1, h2⟩ := hval x hx y hy
    refine Set.mem_biUnion (x := (w, v)) ⟨hw, hv, ?_⟩ ⟨h1, h2⟩
    by_contra hinf
    obtain ⟨hsw, hvt⟩ := hstrip w v (fun h => hW0 (h ▸ hw)) (fun h => hV1 (h ▸ hv)) (h1.trans h2) hinf
    exact hz ⟨hsw.trans h1, h2.trans hvt⟩
  · -- no crossing: every infinite interval lies inside `D` or inside `U`
    refine TwoSided.cut_two_sided_capture hF hD hbot htop hH hH' fun w v hw hv hwv hinf => ?_
    obtain ⟨hsw, hvt⟩ := hstrip w v hw hv hwv hinf
    by_cases hs : s ∈ D
    · exact Or.inl (by_contra fun hvD => hcross ⟨hs, fun htD => hvD (hD _ _ hvt htD)⟩)
    · exact Or.inr fun hwD => hs (hD _ _ hsw hwD)

end Mordor.Strip

namespace Mordor
open Strip

/-- **Semi-CL (hence CL) with one crossing strip.** -/
theorem semi_of_one_strip {α : Type*} [CompleteLattice α]
    (hH : {g : α | (Set.Ici g).Infinite}.Finite) (hH' : {g : α | (Set.Iic g).Infinite}.Finite)
    {s t : α} (hst : s ≤ t)
    (hstrip : ∀ w v : α, w ≠ ⊥ → v ≠ ⊤ → w ≤ v → (Set.Icc w v).Infinite → s ≤ w ∧ v ≤ t)
    (hrelI : ∀ g, s ≤ g → g ≤ t → g ≠ t → (Set.Icc s g).Finite)
    (hrelJ : ∀ g, s ≤ g → g ≤ t → g ≠ s → (Set.Icc g t).Finite)
    (hmod : ∀ g, (g ⊓ t) ⊔ s = s → (g ⊔ s) ⊓ t = t → False)
    (F : α →o α →o α) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_one_strip (F := fun x y => F x y)
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x y h hy => hD h hy) (hD bot_le hd)
    (fun ht => hu (hD le_top ht)) hH hH' hst hstrip hrelI hrelJ hmod

end Mordor


/-! ### `L × C₃` for end-finite `L` -/

namespace Mordor.Strip
open Classical

variable {β : Type*} [CompleteLattice β] [Nontrivial β]

private lemma fin3_bot : (⊥ : Fin 3) = 0 := le_antisymm bot_le (Fin.zero_le _)
private lemma fin3_top : (⊤ : Fin 3) = 2 := le_antisymm (Fin.le_last _) le_top

omit [CompleteLattice β] [Nontrivial β] in
private lemma prod_fin_left {S : Set β} (hS : S.Finite) {T : Set (β × Fin 3)} (h : ∀ z ∈ T, z.1 ∈ S) :
    T.Finite := (hS.prod (Set.toFinite (Set.univ : Set (Fin 3)))).subset fun z hz => ⟨h z hz, trivial⟩

/-- **Cut on `L × C₃`** for every complete lattice `L` whose proper principal ideals and filters are finite
(e.g. `Ω × C₃`). The single strip is `[(⊥, 1), (⊤, 1)]`. -/
theorem cut_prod_three (hI : ∀ g : β, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : β, g ≠ ⊥ → (Set.Ici g).Finite)
    {F : β × Fin 3 → β × Fin 3 → β × Fin 3} {D : Set (β × Fin 3)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) : ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  -- an element with first coordinate `≠ ⊥` has a finite filter; `≠ ⊤`, a finite ideal
  have hIci : ∀ g : β × Fin 3, g.1 ≠ ⊥ → (Set.Ici g).Finite := fun g hg =>
    prod_fin_left (hJ _ hg) fun z hz => (Prod.le_def.1 hz).1
  have hIic : ∀ g : β × Fin 3, g.1 ≠ ⊤ → (Set.Iic g).Finite := fun g hg =>
    prod_fin_left (hI _ hg) fun z hz => (Prod.le_def.1 hz).1
  have hH : {g : β × Fin 3 | (Set.Ici g).Infinite}.Finite :=
    (Set.finite_range fun k : Fin 3 => ((⊥ : β), k)).subset fun g hg =>
      ⟨g.2, Prod.ext (by_contra fun h => hg (hIci g fun h' => h h'.symm)) rfl⟩
  have hH' : {g : β × Fin 3 | (Set.Iic g).Infinite}.Finite :=
    (Set.finite_range fun k : Fin 3 => ((⊤ : β), k)).subset fun g hg =>
      ⟨g.2, Prod.ext (by_contra fun h => hg (hIic g fun h' => h h'.symm)) rfl⟩
  refine cut_one_strip hF hD hbot htop hH hH' (s := ((⊥ : β), (1 : Fin 3))) (t := ((⊤ : β), (1 : Fin 3)))
    (Prod.mk_le_mk.2 ⟨bot_le, le_rfl⟩) ?_ ?_ ?_ ?_
  · -- every infinite interval lies in the middle strip
    intro w v hw hv hwv hinf
    have hw1 : w.1 = ⊥ := by
      by_contra h; exact hinf ((hIci w h).subset fun z hz => hz.1)
    have hv1 : v.1 = ⊤ := by
      by_contra h; exact hinf ((hIic v h).subset fun z hz => hz.2)
    have hw2 : w.2 ≠ 0 := fun h => hw (Prod.ext (by simpa using hw1) (by simpa [fin3_bot] using h))
    have hv2 : v.2 ≠ 2 := fun h => hv (Prod.ext (by simpa using hv1) (by simpa [fin3_top] using h))
    refine ⟨Prod.mk_le_mk.2 ⟨bot_le, ?_⟩, Prod.mk_le_mk.2 ⟨le_top, ?_⟩⟩
    · have h' : (w.2 : ℕ) ≠ 0 := fun e => hw2 (Fin.ext e)
      rw [Fin.le_iff_val_le_val]; show 1 ≤ (w.2 : ℕ); omega
    · have h' : (v.2 : ℕ) ≠ 2 := fun e => hv2 (Fin.ext e)
      have hlt := v.2.isLt
      rw [Fin.le_iff_val_le_val]; show (v.2 : ℕ) ≤ 1; omega
  · intro g hsg hgt hne
    have hg2 : g.2 = 1 := le_antisymm (Prod.le_def.1 hgt).2 (Prod.le_def.1 hsg).2
    exact (hIic g fun h => hne (Prod.ext h hg2)).subset fun z hz => hz.2
  · intro g hsg hgt hne
    have hg2 : g.2 = 1 := le_antisymm (Prod.le_def.1 hgt).2 (Prod.le_def.1 hsg).2
    exact (hIci g fun h => hne (Prod.ext h hg2)).subset fun z hz => hz.1
  · intro g h1 h2
    have e1 := congrArg Prod.fst h1
    have e2 := congrArg Prod.fst h2
    simp only [Prod.fst_sup, Prod.fst_inf, inf_top_eq, sup_bot_eq] at e1 e2
    exact bot_ne_top (e1.symm.trans e2)

end Mordor.Strip

namespace Mordor
open Strip

/-- **CL on `L × C₃`** for every complete lattice `L` with finite proper principal ideals and filters. -/
theorem semi_of_prod_three {β : Type*} [CompleteLattice β] [Nontrivial β]
    (hI : ∀ g : β, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : β, g ≠ ⊥ → (Set.Ici g).Finite)
    (F : β × Fin 3 →o β × Fin 3 →o β × Fin 3) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_prod_three hI hJ (F := fun x y => F x y)
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x y h hy => hD h hy) (hD bot_le hd)
    (fun ht => hu (hD le_top ht))

end Mordor

