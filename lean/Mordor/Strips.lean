import Mordor.Strip

/-!
# Several separated strips (log §34.3y)

`Strip.cut_one_strip` handles all infinite intervals inside one strip. Here the infinite intervals may lie in finitely
many strips `[s, t]`, provided no element of one strip lies below an element of another (*separation*). Values in
different strips are then never compared.

The proof is the same as before, done for every strip at once.
* Crossing strips (`s ∈ D`, `t ∉ D`) are modified as in `Strip.strip_contra`. The finitely many values outside all
  strips are the only guide posts needed.
* Non-crossing strips are captured: by `t` when `t ∈ D`, by `s` when `s ∉ D`.
* `capture_contra` on the monotone extension gives the contradiction.

Corollary `cut_prod_antichain`: CL on `L × K` for every complete end-finite `L` and every finite complete lattice
`K` whose middle `K \ {⊥, ⊤}` is an antichain (`K = M_n`; `C₃ = M₁`), e.g. `Ω × M₃`.
-/

namespace Mordor.Strips
open Finset Classical
set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α]

theorem cut_strips {F : α → α → α} {D : Set α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (hH : {g : α | (Set.Ici g).Infinite}.Finite) (hH' : {g : α | (Set.Iic g).Infinite}.Finite)
    (P : Finset (α × α)) (hst : ∀ p ∈ P, p.1 ≤ p.2)
    (hcov : ∀ w v : α, w ≠ ⊥ → v ≠ ⊤ → w ≤ v → (Set.Icc w v).Infinite → ∃ p ∈ P, p.1 ≤ w ∧ v ≤ p.2)
    (hsep : ∀ p ∈ P, ∀ q ∈ P, ∀ z z', p.1 ≤ z → z ≤ p.2 → q.1 ≤ z' → z' ≤ q.2 → z ≤ z' → p = q)
    (hrelI : ∀ p ∈ P, ∀ g, p.1 ≤ g → g ≤ p.2 → g ≠ p.2 → (Set.Icc p.1 g).Finite)
    (hrelJ : ∀ p ∈ P, ∀ g, p.1 ≤ g → g ≤ p.2 → g ≠ p.1 → (Set.Icc g p.2).Finite)
    (hmod : ∀ p ∈ P, ∀ g, (g ⊓ p.2) ⊔ p.1 = p.1 → (g ⊔ p.1) ⊓ p.2 = p.2 → False) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  obtain ⟨G, hG, nwG, W, V, hW, hV, hW0, hV1, hval⟩ :=
    TwoSided.two_sided hF hD hbot htop hH hH' fun x hx y hy => hno x hx y hy
  let inS : α → α × α → Prop := fun z p => p.1 ≤ z ∧ z ≤ p.2
  have uniq : ∀ {z p q}, p ∈ P → q ∈ P → inS z p → inS z q → p = q := fun hp hq h1 h2 =>
    hsep _ hp _ hq _ _ h1.1 h1.2 h2.1 h2.2 le_rfl
  -- values in finite intervals; every other value lies in a strip
  let I : Set (α × α) := {p | p.1 ∈ W ∧ p.2 ∈ V ∧ (Set.Icc p.1 p.2).Finite}
  have hI : I.Finite := (hW.biUnion fun w _ => hV.image fun v => (w, v)).subset fun p hp =>
    Set.mem_biUnion hp.1 ⟨p.2, hp.2.1, rfl⟩
  let Fn : Set α := ⋃ p ∈ I, Set.Icc p.1 p.2
  have hFn : Fn.Finite := hI.biUnion fun p hp => hp.2.2
  have hloc : ∀ x ∈ D, ∀ y, y ∉ D → G x y ∈ Fn ∨ ∃ p ∈ P, inS (G x y) p := by
    intro x hx y hy
    obtain ⟨w, hw, v, hv, h1, h2⟩ := hval x hx y hy
    by_cases hf : (Set.Icc w v).Finite
    · exact Or.inl (Set.mem_biUnion (x := (w, v)) ⟨hw, hv, hf⟩ ⟨h1, h2⟩)
    · obtain ⟨p, hp, hpw, hvp⟩ := hcov w v (fun h => hW0 (h ▸ hw)) (fun h => hV1 (h ▸ hv)) (h1.trans h2) hf
      exact Or.inr ⟨p, hp, hpw.trans h1, h2.trans hvp⟩
  -- guide posts: values outside every strip
  let NSet : Set α := {z | ∃ x ∈ D, ∃ y, y ∉ D ∧ z = G x y ∧ ∀ p ∈ P, ¬ inS z p}
  have hNSet : NSet.Finite := hFn.subset fun z ⟨x, hx, y, hy, hz, hn⟩ => by
    rcases hloc x hx y hy with h | ⟨p, hp, h⟩
    · exact hz ▸ h
    · exact absurd (hz ▸ h) (hn p hp)
  let N : Finset α := hNSet.toFinset
  -- crossing strips
  let Cr : Finset (α × α) := P.filter fun p => p.1 ∈ D ∧ p.2 ∉ D
  let pick : α → α × α := fun z => if h : ∃ p ∈ Cr, inS z p then h.choose else (⊥, ⊤)
  have pick_eq : ∀ {z p}, p ∈ Cr → inS z p → pick z = p := by
    intro z p hp hz
    have h : ∃ p ∈ Cr, inS z p := ⟨p, hp, hz⟩
    simp only [pick, dif_pos h]
    exact uniq (Finset.mem_filter.1 h.choose_spec.1).1 (Finset.mem_filter.1 hp).1 h.choose_spec.2 hz
  let ψd : α × α → α → α := fun p z => p.1 ⊔ (N.filter (· ≤ z)).sup id
  let ψu : α × α → α → α := fun p z => p.2 ⊓ (N.filter (z ≤ ·)).inf id
  have ψd_le : ∀ p z, p.1 ≤ z → ψd p z ≤ z := fun p z hz =>
    sup_le hz (Finset.sup_le fun f hf => (Finset.mem_filter.1 hf).2)
  have le_ψu : ∀ p z, z ≤ p.2 → z ≤ ψu p z := fun p z hz =>
    le_inf hz (Finset.le_inf fun f hf => (Finset.mem_filter.1 hf).2)
  have ψd_mono : ∀ p z z', z ≤ z' → ψd p z ≤ ψd p z' := fun p z z' h =>
    sup_le_sup_left (Finset.sup_mono fun f hf =>
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2.trans h⟩) _
  have ψu_mono : ∀ p z z', z ≤ z' → ψu p z ≤ ψu p z' := fun p z z' h =>
    inf_le_inf_left _ (Finset.inf_mono fun f hf =>
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hf).1, h.trans (Finset.mem_filter.1 hf).2⟩)
  let md : α × α → α → α → α → α := fun p x y z =>
    if p.1 ≤ x then (if y ≤ p.2 then z else ψu p z) else ψd p z
  let C : α → Prop := fun z => ∃ p ∈ Cr, inS z p
  let H : α → α → α := fun x y => if C (G x y) then md (pick (G x y)) x y (G x y) else G x y
  have hNz : ∀ {a b}, a ∈ D → b ∉ D → (∀ p ∈ P, ¬ inS (G a b) p) → G a b ∈ N := fun ha hb h =>
    hNSet.mem_toFinset.2 ⟨_, ha, _, hb, rfl, h⟩
  -- a crossing-strip value and a comparable value outside crossing strips: the latter is a guide post
  have hguide : ∀ {a b p}, a ∈ D → b ∉ D → p ∈ Cr → ¬ C (G a b) → ∀ z, inS z p →
      (z ≤ G a b ∨ G a b ≤ z) → G a b ∈ N := by
    intro a b p ha hb hp hC z hz hcmp
    refine hNz ha hb fun q hq hzq => ?_
    have hpP := (Finset.mem_filter.1 hp).1
    rcases hcmp with h | h
    · have := hsep _ hpP _ hq _ _ hz.1 hz.2 hzq.1 hzq.2 h
      exact hC ⟨q, this ▸ hp, hzq⟩
    · have := hsep _ hq _ hpP _ _ hzq.1 hzq.2 hz.1 hz.2 h
      exact hC ⟨q, this.symm ▸ hp, hzq⟩
  -- monotone on cells
  have hHm : ∀ x x' y y', x ∈ D → x' ∈ D → y ∉ D → y' ∉ D → x ≤ x' → y ≤ y' → H x y ≤ H x' y' := by
    intro x x' y y' hx hx' hy hy' hxx hyy
    have hzz := hG _ _ _ _ hxx hyy
    by_cases h1 : C (G x y) <;> by_cases h2 : C (G x' y')
    · obtain ⟨p, hp, hzp⟩ := h1
      obtain ⟨q, hq, hzq⟩ := h2
      have hpq : p = q := hsep _ (Finset.mem_filter.1 hp).1 _ (Finset.mem_filter.1 hq).1 _ _
        hzp.1 hzp.2 hzq.1 hzq.2 hzz
      subst hpq
      simp only [H, show C (G x y) from ⟨p, hp, hzp⟩, show C (G x' y') from ⟨p, hq, hzq⟩, if_true,
        pick_eq hp hzp, pick_eq hq hzq, md]
      by_cases hsx : p.1 ≤ x
      · have hsx' : p.1 ≤ x' := hsx.trans hxx
        by_cases hyt' : y' ≤ p.2
        · have hyt : y ≤ p.2 := hyy.trans hyt'
          simp only [hsx, hsx', hyt, hyt', if_true]; exact hzz
        · simp only [hsx, hsx', hyt', if_true, if_false]
          by_cases hyt : y ≤ p.2
          · simp only [hyt, if_true]; exact hzz.trans (le_ψu _ _ hzq.2)
          · simp only [hyt, if_false]; exact ψu_mono _ _ _ hzz
      · simp only [hsx, if_false]
        by_cases hsx' : p.1 ≤ x'
        · simp only [hsx', if_true]
          by_cases hyt' : y' ≤ p.2
          · simp only [hyt', if_true]; exact (ψd_le _ _ hzp.1).trans hzz
          · simp only [hyt', if_false]; exact (ψd_le _ _ hzp.1).trans (hzz.trans (le_ψu _ _ hzq.2))
        · simp only [hsx', if_false]; exact ψd_mono _ _ _ hzz
    · obtain ⟨p, hp, hzp⟩ := h1
      have hN' := hguide hx' hy' hp h2 _ hzp (Or.inl hzz)
      simp only [H, show C (G x y) from ⟨p, hp, hzp⟩, h2, if_true, if_false, pick_eq hp hzp, md]
      by_cases hsx : p.1 ≤ x
      · simp only [hsx, if_true]
        by_cases hyt : y ≤ p.2
        · simp only [hyt, if_true]; exact hzz
        · simp only [hyt, if_false]
          exact inf_le_of_right_le (Finset.inf_le (f := id) (Finset.mem_filter.2 ⟨hN', hzz⟩))
      · simp only [hsx, if_false]; exact (ψd_le _ _ hzp.1).trans hzz
    · obtain ⟨q, hq, hzq⟩ := h2
      have hN := hguide hx hy hq h1 _ hzq (Or.inr hzz)
      simp only [H, show C (G x' y') from ⟨q, hq, hzq⟩, h1, if_true, if_false, pick_eq hq hzq, md]
      by_cases hsx' : q.1 ≤ x'
      · simp only [hsx', if_true]
        by_cases hyt' : y' ≤ q.2
        · simp only [hyt', if_true]; exact hzz
        · simp only [hyt', if_false]; exact hzz.trans (le_ψu _ _ hzq.2)
      · simp only [hsx', if_false]
        exact le_sup_of_le_right (Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hN, hzz⟩))
    · simp only [H, h1, h2, if_false]; exact hzz
  -- witness-free on cells
  have nwH : ∀ x ∈ D, ∀ y, y ∉ D → ¬ H x y ≤ x ∧ ¬ y ≤ H x y := by
    intro x hx y hy
    have h0 := nwG x hx y hy
    by_cases h1 : C (G x y)
    · obtain ⟨p, hp, hzp⟩ := h1
      simp only [H, show C (G x y) from ⟨p, hp, hzp⟩, if_true, pick_eq hp hzp, md]
      by_cases hsx : p.1 ≤ x
      · simp only [hsx, if_true]
        by_cases hyt : y ≤ p.2
        · simp only [hyt, if_true]; exact h0
        · simp only [hyt, if_false]
          exact ⟨fun h => h0.1 ((le_ψu _ _ hzp.2).trans h), fun h => hyt (h.trans inf_le_left)⟩
      · simp only [hsx, if_false]
        exact ⟨fun h => hsx (le_sup_left.trans h), fun h => h0.2 (h.trans (ψd_le _ _ hzp.1))⟩
    · simp only [H, h1, if_false]; exact h0
  -- the finite part of the values
  let Core : Set α := ⋃ p ∈ (Cr : Set (α × α)),
    {z | ∃ x ∈ D, ∃ y, y ∉ D ∧ p.1 ≤ x ∧ y ≤ p.2 ∧ z = G x y ∧ p.1 ≤ z ∧ z ≤ p.2}
  have hCore : Core.Finite := Cr.finite_toSet.biUnion fun p hp => by
    have hp' := Finset.mem_filter.1 (Finset.mem_coe.1 hp)
    exact Strip.core_finite hG hD nwG hp'.2.1 hp'.2.2 (hst p hp'.1) (hrelI p hp'.1) (hrelJ p hp'.1) (hmod p hp'.1)
  let Ψ : Set α := ⋃ p ∈ (Cr : Set (α × α)),
    ((fun Q : Finset α => p.1 ⊔ Q.sup id) '' (N.powerset : Set (Finset α))) ∪
      ((fun Q : Finset α => p.2 ⊓ Q.inf id) '' (N.powerset : Set (Finset α)))
  have hΨ : Ψ.Finite := Cr.finite_toSet.biUnion fun p _ =>
    ((Finset.finite_toSet _).image _).union ((Finset.finite_toSet _).image _)
  let Z : Set α := Fn ∪ Core ∪ Ψ
  have hZ : Z.Finite := (hFn.union hCore).union hΨ
  -- every cell value of `H` is in `Z` or in a non-crossing strip
  have hvalH : ∀ x ∈ D, ∀ y, y ∉ D → H x y ∈ Z ∨ ∃ p ∈ P, p ∉ Cr ∧ inS (H x y) p := by
    intro x hx y hy
    by_cases h1 : C (G x y)
    · obtain ⟨p, hp, hzp⟩ := h1
      refine Or.inl ?_
      simp only [H, show C (G x y) from ⟨p, hp, hzp⟩, if_true, pick_eq hp hzp, md]
      by_cases hsx : p.1 ≤ x
      · simp only [hsx, if_true]
        by_cases hyt : y ≤ p.2
        · simp only [hyt, if_true]
          exact Or.inl (Or.inr (Set.mem_biUnion (x := p) hp ⟨x, hx, y, hy, hsx, hyt, rfl, hzp⟩))
        · simp only [hyt, if_false]
          exact Or.inr (Set.mem_biUnion (x := p) hp (Or.inr
            ⟨_, Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _)), rfl⟩))
      · simp only [hsx, if_false]
        exact Or.inr (Set.mem_biUnion (x := p) hp (Or.inl
          ⟨_, Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _)), rfl⟩))
    · simp only [H, h1, if_false]
      rcases hloc x hx y hy with h | ⟨p, hp, hzp⟩
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr ⟨p, hp, fun hpC => h1 ⟨p, hpC, hzp⟩, hzp⟩
  -- capture on the monotone extension
  obtain ⟨H', hH', hHH⟩ := Strip.extend_mono H hHm
  let TD : Finset α := insert ⊥ (hZ.toFinset.filter (· ∈ D) ∪ (P.image Prod.snd).filter (· ∈ D))
  let TU : Finset α := insert ⊤ (hZ.toFinset.filter (· ∉ D) ∪ (P.image Prod.fst).filter (· ∉ D))
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
  refine Localize.capture_contra hH' hD TD TU hTD hTU (Finset.insert_nonempty _ _) (Finset.insert_nonempty _ _)
    D {y | y ∉ D} hTD hTU (fun a ha b _ => hD _ _ inf_le_left ha) (fun a ha b _ h => ha (hD _ _ le_sup_left h))
    ?_ (fun x _ y _ hx hy => by rw [hHH x hx y hy]; exact nwH x hx y hy)
  intro x _ y _ hx hy
  rw [hHH x hx y hy]
  rcases hvalH x hx y hy with hz | ⟨p, hp, hpC, hzp⟩
  · exact ⟨fun h => ⟨H x y, Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_filter.2 ⟨hZ.mem_toFinset.2 hz, h⟩)), le_rfl⟩,
      fun h => ⟨H x y, Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_filter.2 ⟨hZ.mem_toFinset.2 hz, h⟩)), le_rfl⟩⟩
  · -- a non-crossing strip: captured by its top (`∈ D`) or its bottom (`∉ D`)
    have hnc : ¬ (p.1 ∈ D ∧ p.2 ∉ D) := fun h => hpC (Finset.mem_filter.2 ⟨hp, h⟩)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h2 : p.2 ∈ D := by
        by_contra h2; exact hnc ⟨hD _ _ hzp.1 h, h2⟩
      exact ⟨p.2, Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hp, h2⟩)), hzp.2⟩
    · have h1 : p.1 ∉ D := fun h1 => h (by
        by_contra h'; exact hnc ⟨h1, fun h2 => h' (hD _ _ hzp.2 h2)⟩)
      exact ⟨p.1, Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hp, h1⟩)), hzp.1⟩

end Mordor.Strips


namespace Mordor.Strips
open Finset Classical

variable {β K : Type*} [CompleteLattice β] [Nontrivial β] [CompleteLattice K] [Fintype K]

omit [CompleteLattice β] [Nontrivial β] [CompleteLattice K] in
private lemma prod_fin_left' [Preorder β] {S : Set β} (hS : S.Finite) {T : Set (β × K)}
    (h : ∀ z ∈ T, z.1 ∈ S) : T.Finite :=
  (hS.prod (Set.toFinite (Set.univ : Set K))).subset fun z hz => ⟨h z hz, trivial⟩

/-- **Cut on `L × K`** for every complete lattice `L` with finite proper principal ideals and filters and every finite
complete lattice `K` whose middle `K \ {⊥, ⊤}` is an antichain (`K = M_n`, e.g. `Ω × M₃`). One strip
`[(⊥, k), (⊤, k)]` per middle element `k`. -/
theorem cut_prod_antichain (hK : ∀ k k' : K, k ≠ ⊥ → k' ≠ ⊤ → k ≤ k' → k = k')
    (hI : ∀ g : β, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : β, g ≠ ⊥ → (Set.Ici g).Finite)
    {F : β × K → β × K → β × K} {D : Set (β × K)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) : ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  have hIci : ∀ g : β × K, g.1 ≠ ⊥ → (Set.Ici g).Finite := fun g hg =>
    prod_fin_left' (hJ _ hg) fun z hz => (Prod.le_def.1 hz).1
  have hIic : ∀ g : β × K, g.1 ≠ ⊤ → (Set.Iic g).Finite := fun g hg =>
    prod_fin_left' (hI _ hg) fun z hz => (Prod.le_def.1 hz).1
  have hH : {g : β × K | (Set.Ici g).Infinite}.Finite :=
    (Set.finite_range fun k : K => ((⊥ : β), k)).subset fun g hg =>
      ⟨g.2, Prod.ext (by_contra fun h => hg (hIci g fun h' => h h'.symm)) rfl⟩
  have hH' : {g : β × K | (Set.Iic g).Infinite}.Finite :=
    (Set.finite_range fun k : K => ((⊤ : β), k)).subset fun g hg =>
      ⟨g.2, Prod.ext (by_contra fun h => hg (hIic g fun h' => h h'.symm)) rfl⟩
  let P : Finset ((β × K) × (β × K)) :=
    (univ.filter fun k : K => k ≠ ⊥ ∧ k ≠ ⊤).image fun k => (((⊥ : β), k), ((⊤ : β), k))
  have memP : ∀ {p}, p ∈ P → ∃ k : K, k ≠ ⊥ ∧ k ≠ ⊤ ∧ p = (((⊥ : β), k), ((⊤ : β), k)) := by
    intro p hp
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
    exact ⟨k, (Finset.mem_filter.1 hk).2.1, (Finset.mem_filter.1 hk).2.2, rfl⟩
  -- a point of a strip has the strip's second coordinate
  have snd_eq : ∀ {k : K} {z : β × K}, ((⊥ : β), k) ≤ z → z ≤ ((⊤ : β), k) → z.2 = k := fun h1 h2 =>
    le_antisymm (Prod.le_def.1 h2).2 (Prod.le_def.1 h1).2
  refine cut_strips hF hD hbot htop hH hH' P ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp; obtain ⟨k, -, -, rfl⟩ := memP hp; exact Prod.mk_le_mk.2 ⟨bot_le, le_rfl⟩
  · intro w v hw hv hwv hinf
    have hw1 : w.1 = ⊥ := by
      by_contra h; exact hinf ((hIci w h).subset fun z hz => hz.1)
    have hv1 : v.1 = ⊤ := by
      by_contra h; exact hinf ((hIic v h).subset fun z hz => hz.2)
    have hw2 : w.2 ≠ ⊥ := fun h => hw (Prod.ext hw1 h)
    have hv2 : v.2 ≠ ⊤ := fun h => hv (Prod.ext hv1 h)
    have hk := hK _ _ hw2 hv2 (Prod.le_def.1 hwv).2
    refine ⟨(((⊥ : β), w.2), ((⊤ : β), w.2)), Finset.mem_image.2 ⟨w.2, Finset.mem_filter.2
      ⟨Finset.mem_univ _, hw2, hk ▸ hv2⟩, rfl⟩, Prod.mk_le_mk.2 ⟨bot_le, le_rfl⟩,
      Prod.mk_le_mk.2 ⟨le_top, hk ▸ le_rfl⟩⟩
  · intro p hp q hq z z' h1 h2 h3 h4 hzz
    obtain ⟨k, hk0, hk1, rfl⟩ := memP hp
    obtain ⟨k', hk0', hk1', rfl⟩ := memP hq
    have e : k = k' := hK _ _ hk0 hk1' ((snd_eq h1 h2).symm.trans_le ((Prod.le_def.1 hzz).2.trans
      (snd_eq h3 h4).le))
    rw [e]
  · intro p hp g h1 h2 hne
    obtain ⟨k, -, -, rfl⟩ := memP hp
    exact (hIic g fun h => hne (Prod.ext h (snd_eq h1 h2))).subset fun z hz => hz.2
  · intro p hp g h1 h2 hne
    obtain ⟨k, -, -, rfl⟩ := memP hp
    exact (hIci g fun h => hne (Prod.ext h (snd_eq h1 h2))).subset fun z hz => hz.1
  · intro p hp g h1 h2
    obtain ⟨k, -, -, rfl⟩ := memP hp
    have e1 := congrArg Prod.fst h1
    have e2 := congrArg Prod.fst h2
    simp only [Prod.fst_sup, Prod.fst_inf, inf_top_eq, sup_bot_eq] at e1 e2
    exact bot_ne_top (e1.symm.trans e2)

end Mordor.Strips

namespace Mordor
open Strips

/-- **CL on `L × K`**, `L` complete end-finite, `K` a finite complete lattice with an antichain middle. -/
theorem semi_of_prod_antichain {β K : Type*} [CompleteLattice β] [Nontrivial β] [CompleteLattice K] [Fintype K]
    (hK : ∀ k k' : K, k ≠ ⊥ → k' ≠ ⊤ → k ≤ k' → k = k')
    (hI : ∀ g : β, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : β, g ≠ ⊥ → (Set.Ici g).Finite)
    (F : β × K →o β × K →o β × K) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_prod_antichain hK hI hJ (F := fun x y => F x y)
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x y h hy => hD h hy) (hD bot_le hd)
    (fun ht => hu (hD le_top ht))

end Mordor

