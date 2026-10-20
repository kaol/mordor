import Mordor.Pin
import Mathlib.Order.Preorder.Finite

/-!
# Finitely many hubs; the reset lemma (log §34.3s)

A *hub* is an element with an infinite principal filter.

* `cut_of_region` (**reset lemma**): if every cell value lies in a region `R`, and for some finite `A ∋ ⊥` every
  principal ideal `↓g ∩ R` (`g ≠ ⊤`) and every principal filter `↑g ∩ R` (`g ∉ A`) is finite, there is a witness.
* `cut_of_finite_hubs`: finite proper principal ideals and finitely many hubs give Cut (`R = L`, `A = {⊥} ∪ hubs`).
  `Mordor.semi_of_finite_hubs` gives semi-CL and CL. This contains `cut_of_end_finite` (no hubs) and `cut_hub`
  (`S∞′`, hubs `d, e, c`), without the shape hypotheses.
* `cut_of_finite_hubs_dual`, `cut_of_region_dual`: the order duals. Cut is self-dual with `F'(x, y) = F(y, x)`.
* `cut_of_nbhd_hubs`, `Mordor.semi_of_nbhd_hubs`: it is enough that each corner neighbourhood
  `N(c) = {z : z ⊓ c ≠ ⊥, z ⊔ c ≠ ⊤}` satisfies the hub condition on one side or the other. Here `R = N(F ⊥ ⊤)`, by
  confinement. This contains `cut_of_finite_nbhd` and covers lattices with infinitely many hubs, e.g. infinite
  horizontal sums of copies of `S∞′` and of its dual.

Proof of the reset lemma. Call an anchor row `h ∈ A ∩ D` *bad* if all of its cell values lie in `A`. A row
`x ∉ A ∪ {⊤}` is *free* if every element of `↓x ∩ A` is bad, and *pinned* otherwise.
* Pinned rows: a non-bad `h ≤ x` has a cell value `ℓ ∉ A`, so `F x ⊤ ∈ ↑ℓ ∩ R`, a finite set.
* Free rows are **reset** to `G x y = ⋁_{h ∈ ↓x ∩ A} F h y`. This keeps `G` monotone, and it keeps every cell free
  of witnesses:
  - `y ≤ G x y` would give `y ≤ F k y` for `k = ⋁(↓x ∩ A) ≤ x`;
  - `G x y ≤ x` would make `h ↦ F h y` a monotone self-map of the finite set `↓x ∩ A`; its Kleene chain from `⊥`
    reaches a fixed point `h = F h y`, which is a witness.
* After the reset, `G` has finitely many cell values, so `cut_of_values_in_finite` applies to `G`.
-/

namespace Mordor.Hubs
open Finset Classical
set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {F : α → α → α} {D : Set α}
variable (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
include hF hD

/-- **The reset lemma.** Suppose (under no witness) every cell value lies in a region `R`, and there is a finite
`A ∋ ⊥` such that inside `R` every principal ideal `↓g` (`g ≠ ⊤`) is finite and every principal filter `↑g`
(`g ∉ A`) is finite. Then there is a witness. -/
theorem cut_of_region (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (R A : Set α) (hA : A.Finite) (hA0 : ⊥ ∈ A)
    (hR : (∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) → ∀ x ∈ D, ∀ y, y ∉ D → F x y ∈ R)
    (hI : ∀ g ∈ R, g ≠ ⊤ → (Set.Iic g ∩ R).Finite) (hJ : ∀ g ∈ R, g ∉ A → (Set.Ici g ∩ R).Finite) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  have nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y := fun x hx y hy => hno x hx y hy
  have hRv := hR nw
  have hne : ∀ x ∈ D, F x ⊤ ≠ ⊤ := fun x hx h => (nw x hx ⊤ htop).2 h.ge
  -- bad anchor rows
  let Bd : α → Prop := fun h => h ∈ D ∧ ∀ y, y ∉ D → F h y ∈ A
  let P : α → Finset α := fun x => hA.toFinset.filter (· ≤ x)
  have memP : ∀ {h x}, h ∈ P x ↔ h ∈ A ∧ h ≤ x := by
    intro h x; simp only [P, Finset.mem_filter, Set.Finite.mem_toFinset]
  let free : α → Prop := fun x => x ∉ A ∧ x ≠ ⊤ ∧ ∀ h ∈ P x, Bd h
  let J : α → α → α := fun x y => (P x).sup fun h => F h y
  let G : α → α → α := fun x y => if free x then J x y else F x y
  have hJ_le : ∀ x x' y y', x ≤ x' → y ≤ y' → J x y ≤ F x' y' := fun x x' y y' hx hy =>
    Finset.sup_le fun h hh => hF _ _ _ _ ((memP.1 hh).2.trans hx) hy
  -- `G` is monotone
  have hG : ∀ x x' y y', x ≤ x' → y ≤ y' → G x y ≤ G x' y' := by
    intro x x' y y' hx hy
    by_cases h1 : free x <;> by_cases h2 : free x' <;> simp only [G, h1, h2, if_true, if_false]
    · exact Finset.sup_le fun h hh => (hF _ _ _ _ le_rfl hy).trans
        (Finset.le_sup (f := fun h => F h y') (memP.2 ⟨(memP.1 hh).1, (memP.1 hh).2.trans hx⟩))
    · exact hJ_le x x' y y' hx hy
    · -- a non-free `x` below a free `x'` lies in `A`
      obtain ⟨hx'A, hx'T, hx'B⟩ := h2
      have hxA : x ∈ A := by
        by_contra hxA
        refine h1 ⟨hxA, fun hxT => hx'T (top_le_iff.1 (hxT ▸ hx)), fun h hh => ?_⟩
        exact hx'B h (memP.2 ⟨(memP.1 hh).1, (memP.1 hh).2.trans hx⟩)
      exact (hF _ _ _ _ le_rfl hy).trans (Finset.le_sup (f := fun h => F h y') (memP.2 ⟨hxA, hx⟩))
    · exact hF _ _ _ _ hx hy
  -- `G` has no witness
  have nwG : ∀ x ∈ D, ∀ y, y ∉ D → ¬ G x y ≤ x ∧ ¬ y ≤ G x y := by
    intro x hx y hy
    by_cases hfx : free x
    · simp only [G, hfx, if_true]
      obtain ⟨-, -, hB⟩ := hfx
      refine ⟨fun hle => ?_, fun hle => ?_⟩
      · -- Kleene chain in the finite set `P x`
        let Q := (P x).filter fun h => h ≤ F h y
        have hQ : Q.Nonempty := ⟨⊥, Finset.mem_filter.2 ⟨memP.2 ⟨hA0, bot_le⟩, bot_le⟩⟩
        obtain ⟨h, hm⟩ := Q.exists_maximal hQ
        have hhQ := Finset.mem_filter.1 hm.1
        have hhD : h ∈ D := (hB h hhQ.1).1
        have hFh : F h y ∈ P x := memP.2 ⟨(hB h hhQ.1).2 y hy,
          (Finset.le_sup (f := fun h => F h y) hhQ.1).trans hle⟩
        have hFQ : F h y ∈ Q := Finset.mem_filter.2 ⟨hFh, hF _ _ _ _ hhQ.2 le_rfl⟩
        exact (nw h hhD y hy).1 (hm.2 hFQ hhQ.2)
      · have hk : (P x).sup id ≤ x := Finset.sup_le fun h hh => (memP.1 hh).2
        exact (nw _ (hD _ _ hk hx) y hy).2 (hle.trans (Finset.sup_le fun h hh =>
          hF _ _ _ _ (Finset.le_sup (f := id) hh) le_rfl))
    · simp only [G, hfx, if_false]; exact nw x hx y hy
  -- the finitely many values of `G`
  have hvR : ∀ h ∈ D, F h ⊤ ∈ R := fun h hh => hRv h hh ⊤ htop
  let W : Set α := ⋃ h ∈ {h | h ∈ A ∧ h ∈ D}, Set.Iic (F h ⊤) ∩ R
  have hW : W.Finite := (hA.subset fun h hh => hh.1).biUnion fun h hh => hI _ (hvR h hh.2) (hne h hh.2)
  let T₁ : Set α := (fun s : Finset α => s.sup id) '' (hW.toFinset.powerset : Set (Finset α))
  let ℓ : α → α := fun h => if hh : ∃ y, y ∉ D ∧ F h y ∉ A then F h hh.choose else ⊥
  let T₂ : Set α := ⋃ h ∈ {h | h ∈ A ∧ h ∈ D ∧ ∃ y, y ∉ D ∧ F h y ∉ A},
    ⋃ g ∈ (Set.Ici (ℓ h) ∩ R) \ {⊤}, Set.Iic g ∩ R
  have hT₁ : T₁.Finite := (Finset.finite_toSet _).image _
  have hT₂ : T₂.Finite := (hA.subset fun h hh => hh.1).biUnion fun h hh => by
    obtain ⟨-, hhD, hc⟩ := hh
    have hℓ : ℓ h = F h hc.choose := by simp only [ℓ, dif_pos hc]
    refine (Set.Finite.diff (hJ _ ?_ ?_)).biUnion fun g hg => hI g hg.1.2 fun h => hg.2 h
    · rw [hℓ]; exact hRv h hhD _ hc.choose_spec.1
    · rw [hℓ]; exact hc.choose_spec.2
  have hval : ∀ x ∈ D, ∀ y, y ∉ D → G x y ∈ W ∪ T₁ ∪ T₂ := by
    intro x hx y hy
    by_cases hfx : free x
    · simp only [G, hfx, if_true]
      refine Or.inl (Or.inr ⟨(P x).image fun h => F h y, Finset.mem_coe.2 (Finset.mem_powerset.2 ?_), ?_⟩)
      · intro z hz
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.1 hz
        have hhD : h ∈ D := hD _ _ (memP.1 hh).2 hx
        exact hW.mem_toFinset.2 (Set.mem_biUnion (x := h) ⟨(memP.1 hh).1, hhD⟩
          ⟨hF _ _ _ _ le_rfl le_top, hRv h hhD y hy⟩)
      · simp only [J, Finset.sup_image, Function.id_comp]
    · simp only [G, hfx, if_false]
      by_cases hxA : x ∈ A
      · exact Or.inl (Or.inl (Set.mem_biUnion (x := x) ⟨hxA, hx⟩ ⟨hF _ _ _ _ le_rfl le_top, hRv x hx y hy⟩))
      · have hxT : x ≠ ⊤ := fun h => htop (h ▸ hx)
        obtain ⟨h, hh, hnB⟩ : ∃ h ∈ P x, ¬ Bd h := by
          by_contra hc; push_neg at hc; exact hfx ⟨hxA, hxT, hc⟩
        have hhD : h ∈ D := hD _ _ (memP.1 hh).2 hx
        have hc : ∃ y, y ∉ D ∧ F h y ∉ A := by
          by_contra hc; push_neg at hc; exact hnB ⟨hhD, hc⟩
        refine Or.inr (Set.mem_biUnion (x := h) ⟨(memP.1 hh).1, hhD, hc⟩ (Set.mem_biUnion (x := F x ⊤)
          ⟨⟨?_, hvR x hx⟩, hne x hx⟩ ⟨hF _ _ _ _ le_rfl le_top, hRv x hx y hy⟩))
        simp only [ℓ, dif_pos hc]
        exact hF _ _ _ _ (memP.1 hh).2 le_top
  obtain ⟨x, hx, y, hy, h⟩ := Pin.cut_of_values_in_finite hG hD hbot htop _ ((hW.union hT₁).union hT₂)
    fun _ => hval
  exact h.elim (nwG x hx y hy).1 (nwG x hx y hy).2

/-- **Finitely many hubs.** A *hub* is an element with an infinite principal filter. -/
theorem cut_of_finite_hubs (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (hI : ∀ g : α, g ≠ ⊤ → (Set.Iic g).Finite) (hH : {g : α | (Set.Ici g).Infinite}.Finite) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) :=
  cut_of_region hF hD hbot htop Set.univ (insert ⊥ {g | (Set.Ici g).Infinite}) (hH.insert ⊥)
    (Set.mem_insert _ _) (fun _ _ _ _ _ => trivial) (fun g _ hg => (hI g hg).subset Set.inter_subset_left)
    fun _ _ hg => (Set.not_infinite.1 fun h => hg (Set.mem_insert_of_mem _ h)).subset Set.inter_subset_left

end Mordor.Hubs

namespace Mordor.Hubs

/-- **Dual form.** Finite proper principal filters and finitely many elements with an infinite principal ideal.
Cut is self-dual: on `αᵒᵈ` take the cut `U` and `F'(x, y) = F(y, x)`; witnesses correspond. -/
theorem cut_of_finite_hubs_dual {α : Type*} [Lattice α] [BoundedOrder α] {F : α → α → α} {D : Set α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (hJ : ∀ g : α, g ≠ ⊥ → (Set.Ici g).Finite) (hH : {g : α | (Set.Iic g).Infinite}.Finite) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  obtain ⟨x, hx, y, hy, h⟩ := cut_of_finite_hubs (α := αᵒᵈ)
    (F := fun x y => OrderDual.toDual (F (OrderDual.ofDual y) (OrderDual.ofDual x)))
    (D := {z | OrderDual.ofDual z ∉ D})
    (by intro x x' y y' hx hy; exact hF _ _ _ _ hy hx)
    (by intro x y hxy hy hx; exact hy (hD _ _ hxy hx))
    (by exact htop) (by intro h; exact h hbot)
    (by intro g hg; exact (hJ (OrderDual.ofDual g) hg).preimage OrderDual.ofDual.injective.injOn)
    (by exact hH.preimage OrderDual.ofDual.injective.injOn)
  exact ⟨OrderDual.ofDual y, not_not.1 hy, OrderDual.ofDual x, hx, h.symm⟩

/-- **The reset lemma, dual form** (finite filters in `R`, finite ideals outside a finite `A ∋ ⊤`). -/
theorem cut_of_region_dual {α : Type*} [Lattice α] [BoundedOrder α] {F : α → α → α} {D : Set α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (R A : Set α) (hA : A.Finite) (hA1 : ⊤ ∈ A)
    (hR : (∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) → ∀ x ∈ D, ∀ y, y ∉ D → F x y ∈ R)
    (hJ : ∀ g ∈ R, g ≠ ⊥ → (Set.Ici g ∩ R).Finite) (hI : ∀ g ∈ R, g ∉ A → (Set.Iic g ∩ R).Finite) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  obtain ⟨x, hx, y, hy, h⟩ := cut_of_region (α := αᵒᵈ)
    (F := fun x y => OrderDual.toDual (F (OrderDual.ofDual y) (OrderDual.ofDual x)))
    (D := {z | OrderDual.ofDual z ∉ D})
    (by intro x x' y y' hx hy; exact hF _ _ _ _ hy hx)
    (by intro x y hxy hy hx; exact hy (hD _ _ hxy hx))
    (by exact htop) (by intro h; exact h hbot)
    (OrderDual.ofDual ⁻¹' R) (OrderDual.ofDual ⁻¹' A) (hA.preimage OrderDual.ofDual.injective.injOn)
    (by exact hA1)
    (by
      intro nw' x hx y hy
      refine hR (fun X hX Y hY => ?_) (OrderDual.ofDual y) (not_not.1 hy) (OrderDual.ofDual x) hx
      exact (nw' (OrderDual.toDual Y) hY (OrderDual.toDual X) (not_not.2 hX)).symm)
    (by
      intro g hg hgt
      exact (hJ (OrderDual.ofDual g) hg hgt).preimage OrderDual.ofDual.injective.injOn)
    (by
      intro g hg hgA
      exact (hI (OrderDual.ofDual g) hg hgA).preimage OrderDual.ofDual.injective.injOn)
  exact ⟨OrderDual.ofDual y, not_not.1 hy, OrderDual.ofDual x, hx, h.symm⟩

/-- The corner neighbourhood `N(c) = {z : z ⊓ c ≠ ⊥, z ⊔ c ≠ ⊤}`. -/
def nbhd {α : Type*} [Lattice α] [BoundedOrder α] (c : α) : Set α := {z | z ⊓ c ≠ ⊥ ∧ z ⊔ c ≠ ⊤}

/-- **Neighbourhood hubs.** Suppose that for every `c ∉ {⊥, ⊤}`, inside `N(c)` either every principal ideal is
finite and only finitely many principal filters are infinite, or dually. Then every cut has a witness. No chain
condition. Contains `cut_of_finite_nbhd`, `cut_of_finite_hubs` and its dual. -/
theorem cut_of_nbhd_hubs {α : Type*} [Lattice α] [BoundedOrder α] {F : α → α → α} {D : Set α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (hN : ∀ c : α, c ≠ ⊥ → c ≠ ⊤ →
      ((∀ g ∈ nbhd c, (Set.Iic g ∩ nbhd c).Finite) ∧
        {g | g ∈ nbhd c ∧ (Set.Ici g ∩ nbhd c).Infinite}.Finite) ∨
      ((∀ g ∈ nbhd c, (Set.Ici g ∩ nbhd c).Finite) ∧
        {g | g ∈ nbhd c ∧ (Set.Iic g ∩ nbhd c).Infinite}.Finite)) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  have hP : Localize.Prob F D ⊥ ⊤ := ⟨hbot, htop, bot_le, fun _ _ _ _ _ _ _ _ => ⟨bot_le, le_top⟩⟩
  have hN0 : Localize.NoW F D ⊥ ⊤ := fun x y hx hy _ _ _ _ => hno x hx y hy
  have hc := Localize.corner_mem hF hD hP hN0
  have hc1 : F ⊥ ⊤ ≠ ⊥ := fun h => hc.2.2.1 (by rw [h, inf_idem])
  have hc2 : F ⊥ ⊤ ≠ ⊤ := fun h => hc.2.2.2 (by rw [h, sup_idem])
  have hval : ∀ x ∈ D, ∀ y, y ∉ D → F x y ∈ nbhd (F ⊥ ⊤) := fun x hx y hy => by
    have hz := Localize.confine hF hD hP hN0 hx hy bot_le le_top bot_le le_top
    exact ⟨hz.2.2.1, hz.2.2.2⟩
  have hnt : ∀ g ∈ nbhd (F ⊥ ⊤), g ≠ ⊤ := fun g hg h => hg.2 (by rw [h, top_sup_eq])
  have hnb : ∀ g ∈ nbhd (F ⊥ ⊤), g ≠ ⊥ := fun g hg h => hg.1 (by rw [h, bot_inf_eq])
  obtain ⟨x, hx, y, hy, h⟩ : ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
    rcases hN _ hc1 hc2 with ⟨hI, hH⟩ | ⟨hJ, hH⟩
    · refine cut_of_region hF hD hbot htop (nbhd (F ⊥ ⊤)) (insert ⊥ {g | g ∈ nbhd (F ⊥ ⊤) ∧
        (Set.Ici g ∩ nbhd (F ⊥ ⊤)).Infinite}) (hH.insert ⊥) (Set.mem_insert _ _) (fun _ => hval)
        (fun g hg _ => hI g hg) fun g hg hgA => ?_
      exact Set.not_infinite.1 fun h => hgA (Set.mem_insert_of_mem _ ⟨hg, h⟩)
    · refine cut_of_region_dual hF hD hbot htop (nbhd (F ⊥ ⊤)) (insert ⊤ {g | g ∈ nbhd (F ⊥ ⊤) ∧
        (Set.Iic g ∩ nbhd (F ⊥ ⊤)).Infinite}) (hH.insert ⊤) (Set.mem_insert _ _) (fun _ => hval)
        (fun g hg _ => hJ g hg) fun g hg hgA => ?_
      exact Set.not_infinite.1 fun h => hgA (Set.mem_insert_of_mem _ ⟨hg, h⟩)
  exact h.elim (hno x hx y hy).1 (hno x hx y hy).2

end Mordor.Hubs

namespace Mordor
open Hubs

/-- **Semi-CL (hence CL) on complete lattices with finite proper principal ideals and finitely many hubs.** -/
theorem semi_of_finite_hubs {α : Type*} [CompleteLattice α]
    (hI : ∀ g : α, g ≠ ⊤ → (Set.Iic g).Finite) (hH : {g : α | (Set.Ici g).Infinite}.Finite)
    (F : α →o α →o α) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_of_finite_hubs (F := fun x y => F x y)
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x y h hy => hD h hy) (hD bot_le hd)
    (fun ht => hu (hD le_top ht)) hI hH

/-- **Semi-CL (hence CL), dual form.** -/
theorem semi_of_finite_hubs_dual {α : Type*} [CompleteLattice α]
    (hJ : ∀ g : α, g ≠ ⊥ → (Set.Ici g).Finite) (hH : {g : α | (Set.Iic g).Infinite}.Finite)
    (F : α →o α →o α) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_of_finite_hubs_dual (F := fun x y => F x y)
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x y h hy => hD h hy) (hD bot_le hd)
    (fun ht => hu (hD le_top ht)) hJ hH

/-- **Semi-CL (hence CL) when every corner neighbourhood has finitely many hubs (one side or the other).** -/
theorem semi_of_nbhd_hubs {α : Type*} [CompleteLattice α]
    (hN : ∀ c : α, c ≠ ⊥ → c ≠ ⊤ →
      ((∀ g ∈ nbhd c, (Set.Iic g ∩ nbhd c).Finite) ∧
        {g | g ∈ nbhd c ∧ (Set.Ici g ∩ nbhd c).Infinite}.Finite) ∨
      ((∀ g ∈ nbhd c, (Set.Ici g ∩ nbhd c).Finite) ∧
        {g | g ∈ nbhd c ∧ (Set.Iic g ∩ nbhd c).Infinite}.Finite))
    (F : α →o α →o α) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_of_nbhd_hubs (F := fun x y => F x y)
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x y h hy => hD h hy) (hD bot_le hd)
    (fun ht => hu (hD le_top ht)) hN

end Mordor

