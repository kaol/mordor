import Mordor.IdealFinite

/-!
# The two-sided reset (log §34.3w)

`reset_core` resets rows to joins of anchor rows. Its order dual `reset_core_dual` resets columns to meets of
co-anchor columns. Running both (`two_sided`) on a lattice with finitely many *hubs* (elements with an infinite
principal filter) and finitely many *co-hubs* (elements with an infinite principal ideal) gives a monotone,
witness-free bifunction `G` with every cell value in an interval `[w, v]`, where `w ≠ ⊥` and `v ≠ ⊤` range over
finite sets. Concretely:
* `w` is a value of the bottom row;
* `v` is a value of the top column.

* `cut_two_sided`: if moreover all intervals `[w, v]` with `⊥ < w ≤ v < ⊤` are finite, every cut has a witness.
* `cut_two_sided_capture`: it suffices that each infinite interval `[w, v]` lies inside `D` or inside `U`. The only
  obstruction left is a cut *crossing* an infinite interval (`w ∈ D`, `v ∉ D`).
* For `Ω × K` with `K` finite, the hubs `(⊥, k)` and co-hubs `(⊤, k)` are finite in number. The infinite intervals
  are exactly the strips `Ω × [k, k']` with `⊥ < k ≤ k' < ⊤` in `K`. So `two_sided` confines every escape on `Ω × K`
  to those strips (log §34.3w).
-/

namespace Mordor.TwoSided
open Finset Classical
set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {F : α → α → α} {D : Set α}
variable (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
include hF hD

/-- **The dual reset.** Under no witness, for a finite `A' ∋ ⊤` there is a monotone, witness-free `G`. Co-anchor
columns are unchanged, and every column `y ∉ D` is either a meet of co-anchor columns, or is unchanged and
*co-pinned*: some co-anchor `h ≥ y` outside `D` has a `U`-valued cell value outside `A'`. -/
theorem reset_core_dual (hbot : ⊥ ∈ D) (A' : Set α) (hA : A'.Finite) (hA1 : ⊤ ∈ A')
    (nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) :
    ∃ G : α → α → α, (∀ x x' y y', x ≤ x' → y ≤ y' → G x y ≤ G x' y') ∧
      (∀ x ∈ D, ∀ y, y ∉ D → ¬ G x y ≤ x ∧ ¬ y ≤ G x y) ∧ (∀ y ∈ A', ∀ x, G x y = F x y) ∧
      ∀ y, y ∉ D → (∃ Q : Finset α, (∀ h ∈ Q, h ∈ A' ∧ h ∉ D) ∧ ∀ x, G x y = Q.inf fun h => F x h) ∨
        ((∀ x, G x y = F x y) ∧
          ∃ h ∈ A', h ∉ D ∧ y ≤ h ∧ ∃ x₀, x₀ ∈ D ∧ F x₀ h ∉ D ∧ F x₀ h ∉ A') := by
  -- co-bad co-anchor columns
  let Bd : α → Prop := fun h => h ∉ D ∧ ∀ x, x ∈ D → F x h ∉ D → F x h ∈ A'
  let Q : α → Finset α := fun y => hA.toFinset.filter (y ≤ ·)
  have memQ : ∀ {h y}, h ∈ Q y ↔ h ∈ A' ∧ y ≤ h := by
    intro h y; simp only [Q, Finset.mem_filter, Set.Finite.mem_toFinset]
  let free : α → Prop := fun y => y ∉ A' ∧ y ≠ ⊥ ∧ ∀ h ∈ Q y, Bd h
  let J : α → α → α := fun x y => (Q y).inf fun h => F x h
  let G : α → α → α := fun x y => if free y then J x y else F x y
  have hJ_ge : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ J x' y' := fun x x' y y' hx hy =>
    Finset.le_inf fun h hh => hF _ _ _ _ hx (hy.trans (memQ.1 hh).2)
  refine ⟨G, ?_, ?_, fun y hy x => by simp only [G, show ¬ free y from fun h => h.1 hy, if_false], ?_⟩
  · -- `G` is monotone
    intro x x' y y' hx hy
    by_cases h1 : free y <;> by_cases h2 : free y' <;> simp only [G, h1, h2, if_true, if_false]
    · exact Finset.le_inf fun h hh => (Finset.inf_le (f := fun h => F x h)
        (memQ.2 ⟨(memQ.1 hh).1, hy.trans (memQ.1 hh).2⟩)).trans (hF _ _ _ _ hx le_rfl)
    · -- a non-free `y'` above a free `y` lies in `A'`
      obtain ⟨hyA, hyB, hyQ⟩ := h1
      have hy'A : y' ∈ A' := by
        by_contra hy'A
        refine h2 ⟨hy'A, fun hb => hyB (le_bot_iff.1 (hb ▸ hy)), fun h hh => ?_⟩
        exact hyQ h (memQ.2 ⟨(memQ.1 hh).1, hy.trans (memQ.1 hh).2⟩)
      exact (Finset.inf_le (f := fun h => F x h) (memQ.2 ⟨hy'A, hy⟩)).trans (hF _ _ _ _ hx le_rfl)
    · exact hJ_ge x x' y y' hx hy
    · exact hF _ _ _ _ hx hy
  · -- `G` has no witness
    intro x hx y hy
    by_cases hfy : free y
    · simp only [G, hfy, if_true]
      obtain ⟨-, -, hB⟩ := hfy
      refine ⟨fun hle => ?_, fun hle => ?_⟩
      · have hk : y ≤ (Q y).inf id := Finset.le_inf fun h hh => (memQ.1 hh).2
        have hkD : (Q y).inf id ∉ D := fun h => hy (hD _ _ hk h)
        exact (nw x hx _ hkD).1 ((Finset.le_inf fun h hh =>
          hF _ _ _ _ le_rfl (Finset.inf_le (f := id) hh)).trans hle)
      · -- dual Kleene chain in the finite set `Q y`
        let Q' := (Q y).filter fun h => F x h ≤ h
        have hQ : Q'.Nonempty := ⟨⊤, Finset.mem_filter.2 ⟨memQ.2 ⟨hA1, le_top⟩, le_top⟩⟩
        obtain ⟨h, hm⟩ := Q'.exists_minimal hQ
        have hhQ := Finset.mem_filter.1 hm.1
        have hhD : h ∉ D := (hB h hhQ.1).1
        have hle' : y ≤ F x h := hle.trans (Finset.inf_le (f := fun h => F x h) hhQ.1)
        have hFD : F x h ∉ D := fun h' => hy (hD _ _ hle' h')
        have hFh : F x h ∈ Q y := memQ.2 ⟨(hB h hhQ.1).2 x hx hFD, hle'⟩
        have hFQ : F x h ∈ Q' := Finset.mem_filter.2 ⟨hFh, hF _ _ _ _ le_rfl hhQ.2⟩
        exact (nw x hx h hhD).2 (hm.2 hFQ hhQ.2)
    · simp only [G, hfy, if_false]; exact nw x hx y hy
  · -- classification of columns
    intro y hy
    by_cases hfy : free y
    · refine Or.inl ⟨Q y, fun h hh => ⟨(memQ.1 hh).1, fun h' => hy (hD _ _ (memQ.1 hh).2 h')⟩, fun x => ?_⟩
      simp only [G, hfy, if_true, J]
    · by_cases hyA : y ∈ A'
      · refine Or.inl ⟨{y}, by simpa using ⟨hyA, hy⟩, fun x => ?_⟩
        simp only [G, hfy, if_false, Finset.inf_singleton]
      · refine Or.inr ⟨fun x => by simp only [G, hfy, if_false], ?_⟩
        have hyB : y ≠ ⊥ := fun h => hy (h ▸ hbot)
        obtain ⟨h, hh, hnB⟩ : ∃ h ∈ Q y, ¬ Bd h := by
          by_contra hc; push_neg at hc; exact hfy ⟨hyA, hyB, hc⟩
        have hhD : h ∉ D := fun h' => hy (hD _ _ (memQ.1 hh).2 h')
        obtain ⟨x₀, hx₀, hc⟩ : ∃ x₀, x₀ ∈ D ∧ F x₀ h ∉ D ∧ F x₀ h ∉ A' := by
          by_contra hc; push_neg at hc; exact hnB ⟨hhD, hc⟩
        exact ⟨h, (memQ.1 hh).1, hhD, (memQ.1 hh).2, x₀, hx₀, hc⟩

/-- **Two-sided reset.** With finitely many hubs and co-hubs, under no witness there is a monotone witness-free `G`
and finite sets `W ∌ ⊥`, `V ∌ ⊤` such that every cell value of `G` lies in some interval `[w, v]` with `w ∈ W`,
`v ∈ V`. -/
theorem two_sided (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (hH : {g : α | (Set.Ici g).Infinite}.Finite) (hH' : {g : α | (Set.Iic g).Infinite}.Finite)
    (nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) :
    ∃ G : α → α → α, (∀ x x' y y', x ≤ x' → y ≤ y' → G x y ≤ G x' y') ∧
      (∀ x ∈ D, ∀ y, y ∉ D → ¬ G x y ≤ x ∧ ¬ y ≤ G x y) ∧
      ∃ W V : Set α, W.Finite ∧ V.Finite ∧ ⊥ ∉ W ∧ ⊤ ∉ V ∧
        ∀ x ∈ D, ∀ y, y ∉ D → ∃ w ∈ W, ∃ v ∈ V, w ≤ G x y ∧ G x y ≤ v := by
  -- rows: anchors `{⊥} ∪ hubs`
  let A : Set α := insert ⊥ {g | (Set.Ici g).Infinite}
  have hA : A.Finite := hH.insert ⊥
  obtain ⟨G₁, hG₁, nw₁, hA₁, hcls₁⟩ := Hubs.reset_core hF hD htop A hA (Set.mem_insert _ _) nw
  -- columns: co-anchors `{⊤} ∪ co-hubs`
  let A' : Set α := insert ⊤ {g | (Set.Iic g).Infinite}
  have hA' : A'.Finite := hH'.insert ⊤
  obtain ⟨G, hG, nwG, hA₂, hcls₂⟩ := reset_core_dual hG₁ hD hbot A' hA' (Set.mem_insert _ _) nw₁
  refine ⟨G, hG, nwG, ?_⟩
  have hfinI : ∀ g, g ∉ A → (Set.Ici g).Finite := fun g hg =>
    Set.not_infinite.1 fun h => hg (Set.mem_insert_of_mem _ h)
  have hfinD : ∀ g, g ∉ A' → (Set.Iic g).Finite := fun g hg =>
    Set.not_infinite.1 fun h => hg (Set.mem_insert_of_mem _ h)
  -- the top column: `G x ⊤ = G₁ x ⊤`
  have hGtop : ∀ x, G x ⊤ = G₁ x ⊤ := fun x => hA₂ ⊤ (Set.mem_insert _ _) x
  -- the bottom row: `G₁ ⊥ = F ⊥`
  have hG₁bot : ∀ y, G₁ ⊥ y = F ⊥ y := fun y => hA₁ ⊥ (Set.mem_insert _ _) y
  -- finitely many upper bounds
  let ℓ : α → α := fun h => if hh : ∃ y, y ∉ D ∧ F h y ∈ D ∧ F h y ∉ A then F h hh.choose else ⊥
  let V : Set α := (((fun s : Finset α => s.sup fun h => F h ⊤) '' (hA.toFinset.powerset : Set (Finset α))) ∪
    ⋃ h ∈ {h | h ∈ A ∧ ∃ y, y ∉ D ∧ F h y ∈ D ∧ F h y ∉ A}, Set.Ici (ℓ h)) \ {⊤}
  have hV : V.Finite := (((Finset.finite_toSet _).image _).union ((hA.subset fun h hh => hh.1).biUnion
    fun h hh => by
      have hc : ∃ y, y ∉ D ∧ F h y ∈ D ∧ F h y ∉ A := hh.2
      simp only [ℓ, dif_pos hc]; exact hfinI _ hc.choose_spec.2.2)).diff
  -- finitely many lower bounds
  let ℓ' : α → α := fun h => if hh : ∃ x, x ∈ D ∧ G₁ x h ∉ D ∧ G₁ x h ∉ A' then G₁ hh.choose h else ⊤
  let W : Set α := (((fun s : Finset α => s.inf fun h => F ⊥ h) '' (hA'.toFinset.powerset : Set (Finset α))) ∪
    ⋃ h ∈ {h | h ∈ A' ∧ ∃ x, x ∈ D ∧ G₁ x h ∉ D ∧ G₁ x h ∉ A'}, Set.Iic (ℓ' h)) \ {⊥}
  have hW : W.Finite := (((Finset.finite_toSet _).image _).union ((hA'.subset fun h hh => hh.1).biUnion
    fun h hh => by
      have hc : ∃ x, x ∈ D ∧ G₁ x h ∉ D ∧ G₁ x h ∉ A' := hh.2
      simp only [ℓ', dif_pos hc]; exact hfinD _ hc.choose_spec.2.2)).diff
  refine ⟨W, V, hW, hV, fun h => h.2 rfl, fun h => h.2 rfl, fun x hx y hy => ⟨G ⊥ y, ?_, G x ⊤, ?_,
    hG _ _ _ _ bot_le le_rfl, hG _ _ _ _ le_rfl le_top⟩⟩
  · -- `G ⊥ y ∈ W`
    refine ⟨?_, fun h => (nwG ⊥ hbot y hy).1 (le_of_eq h)⟩
    rcases hcls₂ y hy with ⟨Q, hQ, hGQ⟩ | ⟨hGF, h, hhA, hhD, hyh, x₀, hx₀, hc⟩
    · refine Or.inl ⟨Q, Finset.mem_coe.2 (Finset.mem_powerset.2 fun h hh => hA'.mem_toFinset.2 (hQ h hh).1), ?_⟩
      simp only [hGQ, hG₁bot]
    · have hc' : ∃ x, x ∈ D ∧ G₁ x h ∉ D ∧ G₁ x h ∉ A' := ⟨x₀, hx₀, hc⟩
      refine Or.inr (Set.mem_biUnion (x := h) ⟨hhA, hc'⟩ ?_)
      simp only [ℓ', dif_pos hc', Set.mem_Iic, hGF]
      exact hG₁ _ _ _ _ bot_le hyh
  · -- `G x ⊤ ∈ V`
    refine ⟨?_, fun h => (nwG x hx ⊤ htop).2 (le_of_eq h.symm)⟩
    rw [hGtop]
    rcases hcls₁ x hx with ⟨P, hP, hGP⟩ | ⟨hGF, h, hhA, hhD, hhx, y₀, hy₀, hc⟩
    · exact Or.inl ⟨P, Finset.mem_coe.2 (Finset.mem_powerset.2 fun h hh => hA.mem_toFinset.2 (hP h hh).1),
        (hGP ⊤).symm⟩
    · have hc' : ∃ y, y ∉ D ∧ F h y ∈ D ∧ F h y ∉ A := ⟨y₀, hy₀, hc⟩
      refine Or.inr (Set.mem_biUnion (x := h) ⟨hhA, hc'⟩ ?_)
      simp only [ℓ, dif_pos hc', Set.mem_Ici, hGF]
      exact hF _ _ _ _ hhx le_top

/-- **Cut from the two-sided reset.** Finitely many hubs and co-hubs, and finite intervals `[w, v]` for
`⊥ < w ≤ v < ⊤`. -/
theorem cut_two_sided (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (hH : {g : α | (Set.Ici g).Infinite}.Finite) (hH' : {g : α | (Set.Iic g).Infinite}.Finite)
    (hIcc : ∀ w v : α, w ≠ ⊥ → v ≠ ⊤ → (Set.Icc w v).Finite) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  obtain ⟨G, hG, nwG, W, V, hW, hV, hW0, hV1, hval⟩ :=
    two_sided hF hD hbot htop hH hH' fun x hx y hy => hno x hx y hy
  have hS : (⋃ w ∈ W, ⋃ v ∈ V, Set.Icc w v).Finite := hW.biUnion fun w hw => hV.biUnion fun v hv =>
    hIcc w v (fun h => hW0 (h ▸ hw)) (fun h => hV1 (h ▸ hv))
  obtain ⟨x, hx, y, hy, h⟩ := Pin.cut_of_values_in_finite hG hD hbot htop _ hS fun _ x hx y hy => by
    obtain ⟨w, hw, v, hv, h1, h2⟩ := hval x hx y hy
    exact Set.mem_biUnion hw (Set.mem_biUnion hv ⟨h1, h2⟩)
  exact h.elim (nwG x hx y hy).1 (nwG x hx y hy).2

/-- **Crossing strips are the only obstruction.** After the two-sided reset, suppose every infinite interval `[w, v]`
(`⊥ < w ≤ v < ⊤`) lies inside `D` (`v ∈ D`) or inside `U` (`w ∉ D`). Then the values are captured by finitely many
elements: the finite intervals by themselves, and an interval inside `D` by its top `v` (inside `U`, by its bottom
`w`). So every cut has a witness unless `D` *crosses* an infinite interval: `w ∈ D` and `v ∉ D`. -/
theorem cut_two_sided_capture (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (hH : {g : α | (Set.Ici g).Infinite}.Finite) (hH' : {g : α | (Set.Iic g).Infinite}.Finite)
    (hcross : ∀ w v : α, w ≠ ⊥ → v ≠ ⊤ → w ≤ v → (Set.Icc w v).Infinite → v ∈ D ∨ w ∉ D) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  obtain ⟨G, hG, nwG, W, V, hW, hV, hW0, hV1, hval⟩ :=
    two_sided hF hD hbot htop hH hH' fun x hx y hy => hno x hx y hy
  let I : Set (α × α) := {p | p.1 ∈ W ∧ p.2 ∈ V ∧ (Set.Icc p.1 p.2).Finite}
  have hI : I.Finite := (hW.biUnion fun w _ => hV.image fun v => (w, v)).subset fun p hp =>
    Set.mem_biUnion hp.1 ⟨p.2, hp.2.1, rfl⟩
  let Fn : Set α := ⋃ p ∈ I, Set.Icc p.1 p.2
  have hFn : Fn.Finite := hI.biUnion fun p hp => hp.2.2
  let TD : Finset α := insert ⊥ (hFn.toFinset.filter (· ∈ D) ∪ hV.toFinset.filter (· ∈ D))
  let TU : Finset α := insert ⊤ (hFn.toFinset.filter (· ∉ D) ∪ hW.toFinset.filter (· ∉ D))
  have hTD : ∀ p ∈ TD, p ∈ D := by
    intro p hp
    rcases Finset.mem_insert.1 hp with rfl | hp
    · exact hbot
    · rcases Finset.mem_union.1 hp with hp | hp <;> exact (Finset.mem_filter.1 hp).2
  have hTU : ∀ u ∈ TU, u ∉ D := by
    intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · exact htop
    · rcases Finset.mem_union.1 hu with hu | hu <;> exact (Finset.mem_filter.1 hu).2
  refine Localize.capture_contra hG hD TD TU hTD hTU (Finset.insert_nonempty _ _) (Finset.insert_nonempty _ _)
    D {y | y ∉ D} hTD hTU (fun a ha b _ => hD _ _ inf_le_left ha) (fun a ha b _ h => ha (hD _ _ le_sup_left h))
    ?_ (fun x _ y _ hx hy => nwG x hx y hy)
  intro x _ y _ hx hy
  obtain ⟨w, hw, v, hv, h1, h2⟩ := hval x hx y hy
  by_cases hf : (Set.Icc w v).Finite
  · have hz : G x y ∈ Fn := Set.mem_biUnion (x := (w, v)) ⟨hw, hv, hf⟩ ⟨h1, h2⟩
    refine ⟨fun h => ⟨G x y, Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_filter.2 ⟨hFn.mem_toFinset.2 hz, h⟩)), le_rfl⟩,
      fun h => ⟨G x y, Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_filter.2 ⟨hFn.mem_toFinset.2 hz, h⟩)), le_rfl⟩⟩
  · have hc := hcross w v (fun h => hW0 (h ▸ hw)) (fun h => hV1 (h ▸ hv)) (h1.trans h2) hf
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases hc with hvD | hwU
      · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hV.mem_toFinset.2 hv, hvD⟩)), h2⟩
      · exact absurd (hD _ _ h1 h) hwU
    · rcases hc with hvD | hwU
      · exact absurd (hD _ _ h2 hvD) h
      · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨hW.mem_toFinset.2 hw, hwU⟩)), h1⟩

end Mordor.TwoSided

