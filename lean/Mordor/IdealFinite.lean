import Mordor.Hubs
import Mordor.Frontier
import Mathlib.Data.Multiset.DershowitzManna

/-!
# Finite principal ideals and ACC (log §34.3t)

**Theorem** (`cut_of_ideal_finite`). On a bounded lattice whose proper principal ideals are finite and which has no
infinite ascending chain, every cut of every monotone `F` has a witness. Dually (`cut_of_filter_finite`) for finite
proper principal filters and no infinite descending chain. So semi-CL and CL hold on every chain-finite complete
lattice with finite proper principal ideals, or with finite proper principal filters (`Mordor.semi_of_chainFinite_ideal`,
`Mordor.semi_of_chainFinite_filter`). This contains §34.3r–s (finitely many hubs force ACC).

Proof. The regions are `reg S N = ↓S ∪ ⋃_{m ∈ N} R_m`, with `R_m = {y : y ≤ z for some z ≠ ⊤ above m}` and `S`, `N`
finite. Suppose every cell value lies in `reg S N` and there is no witness. Reset (`Hubs.reset_core`) with the finite
anchor set `A = {⊥} ∪ ↓S ∪ ⋃_{m ∈ N} ↓m`. After the reset:
* joins of anchor rows take finitely many values (`↓F(h, ⊤)` is finite);
* a pinned row `x` has an anchor value `ℓ ∉ A` below `F x ⊤`. Since `ℓ ∉ ↓S`, `F x ⊤` lies in some `R_m`, below some
  `z ≠ ⊤` with `z ≥ m ⊔ ℓ`. So the row's values lie in `R_{m ⊔ ℓ}`, and `m < m ⊔ ℓ` because `ℓ ∉ ↓m`.

So the reset function has values in `reg S' N'`, where every element of `N'` lies strictly above an element of `N`.
That step is Dershowitz–Manna decreasing for the reversed order, which is well-founded by ACC. Induction ends at
`N = ∅`, where the values lie in the finite set `↓S`.
-/

namespace Mordor.IdealFinite
open Finset Classical
set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α]

/-- The region `↓S ∪ ⋃_{m ∈ N} R_m`. -/
def reg (S N : Finset α) : Set α := {y | (∃ s ∈ S, y ≤ s) ∨ ∃ m ∈ N, ∃ z, z ≠ ⊤ ∧ m ≤ z ∧ y ≤ z}

/-- `N'` *lifts* `N`: `N` is nonempty and every element of `N'` lies strictly above an element of `N`. -/
def Lift (N' N : Finset α) : Prop := N.Nonempty ∧ ∀ m' ∈ N', ∃ m ∈ N, m < m'

theorem lift_wf [WellFoundedGT α] : WellFounded (Lift (α := α)) := by
  have h : WellFounded (Multiset.IsDershowitzMannaLT (α := αᵒᵈ)) := Multiset.wellFounded_isDershowitzMannaLT
  refine Subrelation.wf (r := InvImage _ fun N : Finset α => N.val.map OrderDual.toDual) ?_ (InvImage.wf _ h)
  intro N' N hl
  obtain ⟨hne, hlt⟩ := hl
  refine ⟨0, N'.val.map OrderDual.toDual, N.val.map OrderDual.toDual, ?_, by simp, by simp, ?_⟩
  · intro h
    rw [Multiset.empty_eq_zero, Multiset.map_eq_zero] at h
    exact hne.ne_empty (Finset.val_eq_zero.1 h)
  · intro y hy
    obtain ⟨m', hm', rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨m, hm, hlt'⟩ := hlt m' hm'
    exact ⟨OrderDual.toDual m, Multiset.mem_map_of_mem _ hm, hlt'⟩

theorem key [WellFoundedGT α] {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (hI : ∀ g : α, g ≠ ⊤ → (Set.Iic g).Finite) (N : Finset α) :
    ∀ F : α → α → α, (∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') → ∀ S : Finset α, ⊤ ∉ S →
      (∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) →
      (∀ x ∈ D, ∀ y, y ∉ D → F x y ∈ reg S N) → False := by
  induction N using (lift_wf (α := α)).induction with
  | _ N ih =>
  intro F hF S hS nw hval
  have hne : ∀ x ∈ D, F x ⊤ ≠ ⊤ := fun x hx h => (nw x hx ⊤ htop).2 h.ge
  have hSt : ∀ s ∈ S, s ≠ ⊤ := fun s hs h => hS (h ▸ hs)
  rcases N.eq_empty_or_nonempty with rfl | hN
  · -- `N = ∅`: the values lie in the finite set `↓S`
    have hfin : (⋃ s ∈ (S : Set α), Set.Iic s).Finite :=
      S.finite_toSet.biUnion fun s hs => hI s (hSt s hs)
    obtain ⟨x, hx, y, hy, h⟩ := Pin.cut_of_values_in_finite hF hD hbot htop _ hfin fun _ x hx y hy => by
      rcases hval x hx y hy with ⟨s, hs, hle⟩ | ⟨m, hm, -⟩
      · exact Set.mem_biUnion (x := s) hs hle
      · exact absurd hm (Finset.notMem_empty m)
    exact h.elim (nw x hx y hy).1 (nw x hx y hy).2
  -- the finite anchor set
  let A : Set α := insert ⊥ ((⋃ s ∈ (S : Set α), Set.Iic s) ∪ ⋃ m ∈ {m | m ∈ N ∧ m ≠ ⊤}, Set.Iic m)
  have hA : A.Finite := ((S.finite_toSet.biUnion fun s hs => hI s (hSt s hs)).union
    ((N.finite_toSet.subset fun m hm => hm.1).biUnion fun m hm => hI m hm.2)).insert ⊥
  have hAS : ∀ s ∈ S, ∀ z, z ≤ s → z ∈ A := fun s hs z hz =>
    Set.mem_insert_of_mem _ (Or.inl (Set.mem_biUnion (x := s) hs hz))
  have hAN : ∀ m ∈ N, m ≠ ⊤ → ∀ z, z ≤ m → z ∈ A := fun m hm hmt z hz =>
    Set.mem_insert_of_mem _ (Or.inr (Set.mem_biUnion (x := m) ⟨hm, hmt⟩ hz))
  obtain ⟨G, hG, nwG, -, hcls⟩ := Hubs.reset_core hF hD htop A hA (Set.mem_insert _ _) nw
  have hneG : ∀ x ∈ D, G x ⊤ ≠ ⊤ := fun x hx h => (nwG x hx ⊤ htop).2 h.ge
  -- joins of anchor rows: finitely many values
  let W : Set α := ⋃ h ∈ {h | h ∈ A ∧ h ∈ D}, Set.Iic (F h ⊤)
  have hW : W.Finite := (hA.subset fun h hh => hh.1).biUnion fun h hh => hI _ (hne h hh.2)
  let T₁ : Set α := (fun s : Finset α => s.sup id) '' (hW.toFinset.powerset : Set (Finset α))
  have hT₁ : T₁.Finite := (Finset.finite_toSet _).image _
  let S' : Finset α := hT₁.toFinset.filter (· ≠ ⊤)
  -- pinned rows: new generators `m ⊔ ℓ`
  let Hn : Set α := {h | h ∈ A ∧ h ∈ D ∧ ∃ y, y ∉ D ∧ F h y ∈ D ∧ F h y ∉ A}
  have hHn : Hn.Finite := hA.subset fun h hh => hh.1
  let ℓ : α → α := fun h => if hh : ∃ y, y ∉ D ∧ F h y ∈ D ∧ F h y ∉ A then F h hh.choose else ⊥
  have hℓ : ∀ h ∈ Hn, ℓ h ∉ A ∧ ∀ x, h ≤ x → ℓ h ≤ F x ⊤ := by
    intro h hh
    have hc : ∃ y, y ∉ D ∧ F h y ∈ D ∧ F h y ∉ A := hh.2.2
    simp only [ℓ, dif_pos hc]
    exact ⟨hc.choose_spec.2.2, fun x hx => hF _ _ _ _ hx le_top⟩
  let N' : Finset α := ((N.filter (· ≠ ⊤)) ×ˢ hHn.toFinset).image fun p => p.1 ⊔ ℓ p.2
  have hlift : Lift N' N := by
    refine ⟨hN, fun m' hm' => ?_⟩
    obtain ⟨⟨m, h⟩, hp, rfl⟩ := Finset.mem_image.1 hm'
    obtain ⟨hm, hh⟩ := Finset.mem_product.1 hp
    obtain ⟨hmN, hmt⟩ := Finset.mem_filter.1 hm
    refine ⟨m, hmN, left_lt_sup.2 fun hle => (hℓ h (hHn.mem_toFinset.1 hh)).1 (hAN m hmN hmt _ hle)⟩
  refine ih N' hlift G hG S' (by simp [S']) nwG fun x hx y hy => ?_
  rcases hcls x hx with ⟨P, hP, hGP⟩ | ⟨hGF, h, hhA, hhD, hhx, hc⟩
  · refine Or.inl ⟨G x y, Finset.mem_filter.2 ⟨hT₁.mem_toFinset.2 ?_, fun h => hneG x hx
      (top_le_iff.1 (h.symm.le.trans (hG x x y ⊤ le_rfl le_top)))⟩, le_rfl⟩
    rw [hGP]
    refine ⟨P.image fun h => F h y, Finset.mem_coe.2 (Finset.mem_powerset.2 ?_), ?_⟩
    · intro z hz
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hz
      exact hW.mem_toFinset.2 (Set.mem_biUnion (x := h) ⟨(hP h hh).1, (hP h hh).2⟩
        (hF _ _ _ _ le_rfl le_top))
    · simp only [Finset.sup_image, Function.id_comp]
  · have hhn : h ∈ Hn := ⟨hhA, hhD, hc⟩
    obtain ⟨hℓA, hℓx⟩ := hℓ h hhn
    rcases hval x hx ⊤ htop with ⟨s, hs, hle⟩ | ⟨m, hm, z, hz, hmz, hle⟩
    · exact absurd (hAS s hs _ ((hℓx x hhx).trans hle)) hℓA
    · have hmt : m ≠ ⊤ := fun h => hz (top_le_iff.1 (h ▸ hmz))
      refine Or.inr ⟨m ⊔ ℓ h, Finset.mem_image.2 ⟨(m, h), Finset.mem_product.2
        ⟨Finset.mem_filter.2 ⟨hm, hmt⟩, hHn.mem_toFinset.2 hhn⟩, rfl⟩, z, hz,
        sup_le hmz ((hℓx x hhx).trans hle), ?_⟩
      rw [hGF]; exact (hF _ _ _ _ le_rfl le_top).trans hle

/-- **Finite proper principal ideals and ACC give Cut.** -/
theorem cut_of_ideal_finite [WellFoundedGT α] {F : α → α → α} {D : Set α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (hI : ∀ g : α, g ≠ ⊤ → (Set.Iic g).Finite) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  have nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y := fun x hx y hy => hno x hx y hy
  refine key hD hbot htop hI {⊥} F hF ∅ (by simp) nw fun x hx y hy => Or.inr ⟨⊥, by simp, F x y, ?_, bot_le, le_rfl⟩
  exact fun h => (nw x hx ⊤ htop).2 (h.symm.le.trans (hF x x y ⊤ le_rfl le_top))

/-- **Dual form: finite proper principal filters and DCC give Cut.** -/
theorem cut_of_filter_finite [WellFoundedLT α] {F : α → α → α} {D : Set α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (hJ : ∀ g : α, g ≠ ⊥ → (Set.Ici g).Finite) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  obtain ⟨x, hx, y, hy, h⟩ := cut_of_ideal_finite (α := αᵒᵈ)
    (F := fun x y => OrderDual.toDual (F (OrderDual.ofDual y) (OrderDual.ofDual x)))
    (D := {z | OrderDual.ofDual z ∉ D})
    (by intro x x' y y' hx hy; exact hF _ _ _ _ hy hx)
    (by intro x y hxy hy hx; exact hy (hD _ _ hxy hx))
    (by exact htop) (by intro h; exact h hbot)
    (by intro g hg; exact (hJ (OrderDual.ofDual g) hg).preimage OrderDual.ofDual.injective.injOn)
  exact ⟨OrderDual.ofDual y, not_not.1 hy, OrderDual.ofDual x, hx, h.symm⟩

/-- **Box version.** In a box `[s, t]` with no witness among its cells, finite intervals `[s, g]` (`g < t`) and ACC
are contradictory (`cut_of_ideal_finite` on the interval lattice, with `F` clamped into it). -/
theorem box_ideal_finite [WellFoundedGT α] {F : α → α → α} {D : Set α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    {s t : α} (hP : Localize.Prob F D s t) (hN : Localize.NoW F D s t)
    (hI : ∀ g, s ≤ g → g < t → (Set.Icc s g).Finite) : False := by
  obtain ⟨hs, ht, hst, hbox⟩ := id hP
  haveI : Fact (s ≤ t) := ⟨hst⟩
  let F' : Set.Icc s t → Set.Icc s t → Set.Icc s t :=
    fun x y => ⟨(F x y ⊔ s) ⊓ t, le_inf le_sup_right hst, inf_le_right⟩
  have hF' : ∀ x x' y y' : Set.Icc s t, x ≤ x' → y ≤ y' → F' x y ≤ F' x' y' := fun x x' y y' hx hy =>
    show (F x y ⊔ s) ⊓ t ≤ (F x' y' ⊔ s) ⊓ t from
      inf_le_inf_right _ (sup_le_sup_right (hF _ _ _ _ hx hy) _)
  have hval : ∀ x y : Set.Icc s t, (x : α) ∈ D → (y : α) ∉ D → ((F' x y : Set.Icc s t) : α) = F x y := by
    intro x y hx hy
    have h := hbox x y hx hy x.2.1 x.2.2 y.2.1 y.2.2
    show (F x y ⊔ s) ⊓ t = F x y
    rw [sup_eq_left.2 h.1, inf_eq_left.2 h.2]
  obtain ⟨x, hx, y, hy, h⟩ := cut_of_ideal_finite (α := Set.Icc s t) (F := F') (D := {z | (z : α) ∈ D}) hF'
    (fun x y hxy hy => hD _ _ hxy hy) hs ht (fun g hg => by
      have hgt : (g : α) < t := lt_of_le_of_ne g.2.2 fun h => hg (Subtype.ext h)
      exact ((hI g g.2.1 hgt).preimage Subtype.val_injective.injOn).subset fun z hz => ⟨z.2.1, hz⟩)
  have hxy := hN x y hx hy x.2.1 x.2.2 y.2.1 y.2.2
  rcases h with h | h
  · exact hxy.1 (by have h' : ((F' x y : Set.Icc s t) : α) ≤ x := h; rwa [hval x y hx hy] at h')
  · exact hxy.2 (by have h' : (y : α) ≤ ((F' x y : Set.Icc s t) : α) := h; rwa [hval x y hx hy] at h')

/-- **Box version, dual form**: finite intervals `[g, t]` (`g > s`) and DCC. -/
theorem box_filter_finite [WellFoundedLT α] {F : α → α → α} {D : Set α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    {s t : α} (hP : Localize.Prob F D s t) (hN : Localize.NoW F D s t)
    (hJ : ∀ g, s < g → g ≤ t → (Set.Icc g t).Finite) : False := by
  obtain ⟨hs, ht, hst, hbox⟩ := id hP
  haveI : Fact (s ≤ t) := ⟨hst⟩
  let F' : Set.Icc s t → Set.Icc s t → Set.Icc s t :=
    fun x y => ⟨(F x y ⊔ s) ⊓ t, le_inf le_sup_right hst, inf_le_right⟩
  have hF' : ∀ x x' y y' : Set.Icc s t, x ≤ x' → y ≤ y' → F' x y ≤ F' x' y' := fun x x' y y' hx hy =>
    show (F x y ⊔ s) ⊓ t ≤ (F x' y' ⊔ s) ⊓ t from
      inf_le_inf_right _ (sup_le_sup_right (hF _ _ _ _ hx hy) _)
  have hval : ∀ x y : Set.Icc s t, (x : α) ∈ D → (y : α) ∉ D → ((F' x y : Set.Icc s t) : α) = F x y := by
    intro x y hx hy
    have h := hbox x y hx hy x.2.1 x.2.2 y.2.1 y.2.2
    show (F x y ⊔ s) ⊓ t = F x y
    rw [sup_eq_left.2 h.1, inf_eq_left.2 h.2]
  obtain ⟨x, hx, y, hy, h⟩ := cut_of_filter_finite (α := Set.Icc s t) (F := F') (D := {z | (z : α) ∈ D}) hF'
    (fun x y hxy hy => hD _ _ hxy hy) hs ht (fun g hg => by
      have hsg : s < (g : α) := lt_of_le_of_ne g.2.1 fun h => hg (Subtype.ext h.symm)
      exact ((hJ g hsg g.2.2).preimage Subtype.val_injective.injOn).subset fun z hz => ⟨hz, z.2.2⟩)
  have hxy := hN x y hx hy x.2.1 x.2.2 y.2.1 y.2.2
  rcases h with h | h
  · exact hxy.1 (by have h' : ((F' x y : Set.Icc s t) : α) ≤ x := h; rwa [hval x y hx hy] at h')
  · exact hxy.2 (by have h' : (y : α) ≤ ((F' x y : Set.Icc s t) : α) := h; rwa [hval x y hx hy] at h')

/-- **Box criterion** (lattice level, chain-finite). Every cut has a witness if, for every box `[s, t]` and interior
`c` with neighbourhood `W = W s t c`: there is an interior spine point; or the intervals `[s, g]` (`g < t`) are all
finite; or the intervals `[g, t]` (`g > s`) are all finite; or both
* (`c ∈ D` case) `⋀W > s`, or inside `W` all principal filters are finite and only finitely many `g ≰ c` have an
  infinite principal ideal; and
* (`c ∉ D` case) `⋁W < t`, or inside `W` all principal ideals are finite and only finitely many `g ≱ c` have an
  infinite principal filter.

This contains `Localize.cut_of_box_criterion` (finite `W`, or `⋁W < t` and `⋀W > s`) and, with `s = ⊥`, `t = ⊤`,
`cut_of_ideal_finite` / `cut_of_filter_finite` on chain-finite lattices. -/
theorem cut_of_box_hub_criterion {α : Type*} [CompleteLattice α] [WellFoundedLT α] [WellFoundedGT α]
    {F : α → α → α} {D : Set α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hcrit : ∀ s t c : α, s < c → c < t →
      (∃ p, s < p ∧ p < t ∧ ∀ z, s ≤ z → z ≤ t → z ≤ p ∨ p ≤ z) ∨
      (∀ g, s ≤ g → g < t → (Set.Icc s g).Finite) ∨ (∀ g, s < g → g ≤ t → (Set.Icc g t).Finite) ∨
      ((s < sInf (Hubs.W s t c) ∨ ((∀ g ∈ Hubs.W s t c, (Set.Ici g ∩ Hubs.W s t c).Finite) ∧
          {g | g ∈ Hubs.W s t c ∧ ¬ g ≤ c ∧ (Set.Iic g ∩ Hubs.W s t c).Infinite}.Finite)) ∧
        (sSup (Hubs.W s t c) < t ∨ ((∀ g ∈ Hubs.W s t c, (Set.Iic g ∩ Hubs.W s t c).Finite) ∧
          {g | g ∈ Hubs.W s t c ∧ ¬ c ≤ g ∧ (Set.Ici g ∩ Hubs.W s t c).Infinite}.Finite))))
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) : ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  refine Localize.cut_localize hF hD hbot htop fun s t hP hN => ?_
  have hc := Localize.corner_mem hF hD hP hN
  have hsc : s < F s t := lt_of_le_of_ne hc.1 fun h => hc.2.2.1 (by rw [← h, inf_idem])
  have hct : F s t < t := lt_of_le_of_ne hc.2.1 fun h => hc.2.2.2 (by rw [h, sup_idem])
  rcases hcrit s t (F s t) hsc hct with ⟨p, hsp, hpt, hcmp⟩ | hI | hJ | ⟨hlo, hup⟩
  · by_cases hpD : p ∈ D
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, hpD, hsp, hpt.le, hcmp⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨p, hpD, hsp.le, hpt, hcmp⟩)))
  · exact Or.inl (box_ideal_finite hF hD hP hN hI)
  · exact Or.inl (box_filter_finite hF hD hP hN hJ)
  · by_cases hcD : F s t ∈ D
    · rcases hlo with h | ⟨hJ, hH⟩
      · exact Or.inr (Or.inr (Or.inl ⟨hcD, h⟩))
      · refine Or.inl (Hubs.box_reset_dual hF hD hP hN hJ (hH.subset fun g hg => ⟨hg.1, fun hgc => hg.2.1 ?_, hg.2.2⟩))
        exact hD _ _ hgc hcD
    · rcases hup with h | ⟨hI, hH⟩
      · exact Or.inr (Or.inl ⟨hcD, h⟩)
      · refine Or.inl (Hubs.box_reset hF hD hP hN hI (hH.subset fun g hg => ⟨hg.1, fun hcg => hcD ?_, hg.2.2⟩))
        exact hD _ _ hcg hg.2.1

end Mordor.IdealFinite

namespace Mordor
open IdealFinite

/-- **CL on chain-finite complete lattices with finite proper principal ideals.** -/
theorem semi_of_chainFinite_ideal {α : Type*} [CompleteLattice α]
    (hfin : ∀ K : Set α, IsChain (· ≤ ·) K → K.Finite) (hI : ∀ g : α, g ≠ ⊤ → (Set.Iic g).Finite)
    (F : α →o α →o α) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  haveI := wellFoundedGT_of_chainFinite hfin
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_of_ideal_finite (F := fun x y => F x y)
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x y h hy => hD h hy) (hD bot_le hd)
    (fun ht => hu (hD le_top ht)) hI

/-- **CL on chain-finite complete lattices with finite proper principal filters.** -/
theorem semi_of_chainFinite_filter {α : Type*} [CompleteLattice α]
    (hfin : ∀ K : Set α, IsChain (· ≤ ·) K → K.Finite) (hJ : ∀ g : α, g ≠ ⊥ → (Set.Ici g).Finite)
    (F : α →o α →o α) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  haveI := wellFoundedLT_of_chainFinite hfin
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_of_filter_finite (F := fun x y => F x y)
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x y h hy => hD h hy) (hD bot_le hd)
    (fun ht => hu (hD le_top ht)) hJ

/-- **Semi-CL (hence CL) under the box criterion**, on chain-finite complete lattices. -/
theorem semi_of_box_hub_criterion {α : Type*} [CompleteLattice α] [WellFoundedLT α] [WellFoundedGT α]
    (hcrit : ∀ s t c : α, s < c → c < t →
      (∃ p, s < p ∧ p < t ∧ ∀ z, s ≤ z → z ≤ t → z ≤ p ∨ p ≤ z) ∨
      (∀ g, s ≤ g → g < t → (Set.Icc s g).Finite) ∨ (∀ g, s < g → g ≤ t → (Set.Icc g t).Finite) ∨
      ((s < sInf (Hubs.W s t c) ∨ ((∀ g ∈ Hubs.W s t c, (Set.Ici g ∩ Hubs.W s t c).Finite) ∧
          {g | g ∈ Hubs.W s t c ∧ ¬ g ≤ c ∧ (Set.Iic g ∩ Hubs.W s t c).Infinite}.Finite)) ∧
        (sSup (Hubs.W s t c) < t ∨ ((∀ g ∈ Hubs.W s t c, (Set.Iic g ∩ Hubs.W s t c).Finite) ∧
          {g | g ∈ Hubs.W s t c ∧ ¬ c ≤ g ∧ (Set.Ici g ∩ Hubs.W s t c).Infinite}.Finite))))
    (F : α →o α →o α) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_of_box_hub_criterion (F := fun x y => F x y)
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x y h hy => hD h hy) hcrit
    (hD bot_le hd) (fun ht => hu (hD le_top ht))

end Mordor

