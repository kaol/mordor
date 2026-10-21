import Mordor.Layers

/-!
# The plane: the Cut Lemma on `L₁ × L₂` for end-finite `L₁, L₂` (log §34.3z‴)

Scratch: zone lemmas.
-/

namespace Mordor.Plane
open Finset Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

section zone
variable {α : Type*} [CompleteLattice α] {D : Set α} {G : α → α → α}

/-- **Zone lemma (lowering form).** Values satisfying `Good` stay; every other value is lowered to `lo z` when some
cell above carries a non-`Good` value that is stuck for raising (`Sr`), and raised to `hi z` otherwise. The corner
hypothesis says a value stuck for lowering (`Sl`) below such a cell is `Good`. -/
theorem zone_lo (hG : ∀ x x' y y', x ≤ x' → y ≤ y' → G x y ≤ G x' y')
    (nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ G x y ≤ x ∧ ¬ y ≤ G x y)
    (Good : α → Prop) (lo hi : α → α) (Sl Sr : α → α → Prop)
    (lo_le : ∀ z, lo z ≤ z) (le_hi : ∀ z, z ≤ hi z)
    (hmono : ∀ x y x' y', x ∈ D → y ∉ D → x' ∈ D → y' ∉ D → x ≤ x' → y ≤ y' → ¬ Good (G x y) →
      ¬ Good (G x' y') → lo (G x y) ≤ lo (G x' y') ∧ hi (G x y) ≤ hi (G x' y'))
    (le_lo : ∀ z z', Good z → z ≤ z' → z ≤ lo z') (hi_le : ∀ z z', Good z' → z ≤ z' → hi z ≤ z')
    (hSl : ∀ x z, lo z ≤ x → Sl x z) (hSr : ∀ y z, y ≤ hi z → Sr y z)
    (corner : ∀ x y x' y', x ∈ D → y ∉ D → x' ∈ D → y' ∉ D → x ≤ x' → y ≤ y' → ¬ Good (G x' y') →
      Sl x (G x y) → Sr y' (G x' y') → Good (G x y)) :
    ∃ H : α → α → α,
      (∀ x x' y y', x ∈ D → x' ∈ D → y ∉ D → y' ∉ D → x ≤ x' → y ≤ y' → H x y ≤ H x' y') ∧
      (∀ x ∈ D, ∀ y, y ∉ D → ¬ H x y ≤ x ∧ ¬ y ≤ H x y) ∧
      (∀ x ∈ D, ∀ y, y ∉ D → (Good (G x y) ∧ H x y = G x y) ∨
        (¬ Good (G x y) ∧ (H x y = lo (G x y) ∨ H x y = hi (G x y)))) := by
  let Low : α → α → Prop := fun x y =>
    ∃ x' y', x ≤ x' ∧ x' ∈ D ∧ y ≤ y' ∧ y' ∉ D ∧ ¬ Good (G x' y') ∧ Sr y' (G x' y')
  let H : α → α → α := fun x y => if Good (G x y) then G x y else if Low x y then lo (G x y) else hi (G x y)
  have Low_down : ∀ x x' y y', x ≤ x' → y ≤ y' → Low x' y' → Low x y :=
    fun x x' y y' hxx hyy ⟨a, b, ha, haD, hb, hbD, hn, hk⟩ => ⟨a, b, hxx.trans ha, haD, hyy.trans hb, hbD, hn, hk⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x x' y y' hx hx' hy hy' hxx hyy
    have hzz := hG _ _ _ _ hxx hyy
    by_cases g1 : Good (G x y) <;> by_cases g2 : Good (G x' y')
    · simp only [H, g1, g2, if_true]; exact hzz
    · simp only [H, g1, g2, if_true, if_false]
      split_ifs
      · exact le_lo _ _ g1 hzz
      · exact hzz.trans (le_hi _)
    · simp only [H, g1, g2, if_true, if_false]
      split_ifs
      · exact (lo_le _).trans hzz
      · exact hi_le _ _ g2 hzz
    · have hm := hmono x y x' y' hx hy hx' hy' hxx hyy g1 g2
      simp only [H, g1, g2, if_false]
      by_cases l2 : Low x' y'
      · have l1 := Low_down _ _ _ _ hxx hyy l2
        simp only [l1, l2, if_true]; exact hm.1
      · simp only [l2, if_false]
        split_ifs
        · exact (lo_le _).trans (hzz.trans (le_hi _))
        · exact hm.2
  · intro x hx y hy
    have h0 := nw x hx y hy
    by_cases g : Good (G x y)
    · simp only [H, g, if_true]; exact h0
    · simp only [H, g, if_false]
      by_cases l : Low x y
      · simp only [l, if_true]
        obtain ⟨a, b, ha, haD, hb, hbD, hn, hk⟩ := l
        exact ⟨fun h => g (corner x y a b hx hy haD hbD ha hb hn (hSl _ _ h) hk),
          fun h => h0.2 (h.trans (lo_le _))⟩
      · simp only [l, if_false]
        exact ⟨fun h => h0.1 ((le_hi _).trans h), fun h => l ⟨x, y, le_rfl, hx, le_rfl, hy, g, hSr _ _ h⟩⟩
  · intro x hx y hy
    by_cases g : Good (G x y)
    · left; simp only [H, g, if_true, true_and]
    · right; refine ⟨g, ?_⟩; simp only [H, g, if_false]; split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- **Zone lemma (raising form)**, the order dual of `zone_lo`: raise exactly the cells above a non-`Good` value that
is stuck for lowering. The corner hypothesis now makes the *upper* value `Good`. -/
theorem zone_hi (hG : ∀ x x' y y', x ≤ x' → y ≤ y' → G x y ≤ G x' y')
    (nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ G x y ≤ x ∧ ¬ y ≤ G x y)
    (Good : α → Prop) (lo hi : α → α) (Sl Sr : α → α → Prop)
    (lo_le : ∀ z, lo z ≤ z) (le_hi : ∀ z, z ≤ hi z)
    (hmono : ∀ x y x' y', x ∈ D → y ∉ D → x' ∈ D → y' ∉ D → x ≤ x' → y ≤ y' → ¬ Good (G x y) →
      ¬ Good (G x' y') → lo (G x y) ≤ lo (G x' y') ∧ hi (G x y) ≤ hi (G x' y'))
    (le_lo : ∀ z z', Good z → z ≤ z' → z ≤ lo z') (hi_le : ∀ z z', Good z' → z ≤ z' → hi z ≤ z')
    (hSl : ∀ x z, lo z ≤ x → Sl x z) (hSr : ∀ y z, y ≤ hi z → Sr y z)
    (corner : ∀ x y x' y', x ∈ D → y ∉ D → x' ∈ D → y' ∉ D → x ≤ x' → y ≤ y' → ¬ Good (G x y) →
      Sl x (G x y) → Sr y' (G x' y') → Good (G x' y')) :
    ∃ H : α → α → α,
      (∀ x x' y y', x ∈ D → x' ∈ D → y ∉ D → y' ∉ D → x ≤ x' → y ≤ y' → H x y ≤ H x' y') ∧
      (∀ x ∈ D, ∀ y, y ∉ D → ¬ H x y ≤ x ∧ ¬ y ≤ H x y) ∧
      (∀ x ∈ D, ∀ y, y ∉ D → (Good (G x y) ∧ H x y = G x y) ∨
        (¬ Good (G x y) ∧ (H x y = lo (G x y) ∨ H x y = hi (G x y)))) := by
  let Up : α → α → Prop := fun x y =>
    ∃ x' y', x' ≤ x ∧ x' ∈ D ∧ y' ≤ y ∧ y' ∉ D ∧ ¬ Good (G x' y') ∧ Sl x' (G x' y')
  let H : α → α → α := fun x y => if Good (G x y) then G x y else if Up x y then hi (G x y) else lo (G x y)
  have Up_up : ∀ x x' y y', x ≤ x' → y ≤ y' → Up x y → Up x' y' :=
    fun x x' y y' hxx hyy ⟨a, b, ha, haD, hb, hbD, hn, hk⟩ => ⟨a, b, ha.trans hxx, haD, hb.trans hyy, hbD, hn, hk⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x x' y y' hx hx' hy hy' hxx hyy
    have hzz := hG _ _ _ _ hxx hyy
    by_cases g1 : Good (G x y) <;> by_cases g2 : Good (G x' y')
    · simp only [H, g1, g2, if_true]; exact hzz
    · simp only [H, g1, g2, if_true, if_false]
      split_ifs
      · exact hzz.trans (le_hi _)
      · exact le_lo _ _ g1 hzz
    · simp only [H, g1, g2, if_true, if_false]
      split_ifs
      · exact hi_le _ _ g2 hzz
      · exact (lo_le _).trans hzz
    · have hm := hmono x y x' y' hx hy hx' hy' hxx hyy g1 g2
      simp only [H, g1, g2, if_false]
      by_cases u1 : Up x y
      · have u2 := Up_up _ _ _ _ hxx hyy u1
        simp only [u1, u2, if_true]; exact hm.2
      · simp only [u1, if_false]
        split_ifs
        · exact (lo_le _).trans (hzz.trans (le_hi _))
        · exact hm.1
  · intro x hx y hy
    have h0 := nw x hx y hy
    by_cases g : Good (G x y)
    · simp only [H, g, if_true]; exact h0
    · simp only [H, g, if_false]
      by_cases u : Up x y
      · simp only [u, if_true]
        obtain ⟨a, b, ha, haD, hb, hbD, hn, hk⟩ := u
        exact ⟨fun h => h0.1 ((le_hi _).trans h),
          fun h => g (corner a b x y haD hbD hx hy ha hb hn hk (hSr _ _ h))⟩
      · simp only [u, if_false]
        exact ⟨fun h => u ⟨x, y, le_rfl, hx, le_rfl, hy, g, hSl _ _ h⟩, fun h => h0.2 (h.trans (lo_le _))⟩
  · intro x hx y hy
    by_cases g : Good (G x y)
    · left; simp only [H, g, if_true, true_and]
    · right; refine ⟨g, ?_⟩; simp only [H, g, if_false]; split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl

end zone

section swap
variable {β K : Type*} [CompleteLattice β] [CompleteLattice K]

/-- Cut transfers along the coordinate swap. -/
theorem cut_of_swap {F : β × K → β × K → β × K} {D : Set (β × K)}
    (h : ∃ x ∈ Prod.swap ⁻¹' D, ∃ y, y ∉ Prod.swap ⁻¹' D ∧
      ((F x.swap y.swap).swap ≤ x ∨ y ≤ (F x.swap y.swap).swap)) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  obtain ⟨x, hx, y, hy, h⟩ := h
  refine ⟨x.swap, hx, y.swap, hy, h.imp (fun h => ?_) (fun h => ?_)⟩
  · simpa using Prod.swap_le_swap.2 h
  · simpa using Prod.swap_le_swap.2 h

theorem swap_mono {F : β × K → β × K → β × K} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') :
    ∀ x x' y y' : K × β, x ≤ x' → y ≤ y' → (F x.swap y.swap).swap ≤ (F x'.swap y'.swap).swap :=
  fun x x' y y' hx hy => Prod.swap_le_swap.2 (hF _ _ _ _ (Prod.swap_le_swap.2 hx) (Prod.swap_le_swap.2 hy))

theorem swap_down {D : Set (β × K)} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) :
    ∀ x y : K × β, x ≤ y → y ∈ Prod.swap ⁻¹' D → x ∈ Prod.swap ⁻¹' D :=
  fun x y h hy => hD _ _ (Prod.swap_le_swap.2 h) hy

theorem swap_nw {F : β × K → β × K → β × K} {D : Set (β × K)}
    (nw : ∀ x ∈ Prod.swap ⁻¹' D, ∀ y, y ∉ Prod.swap ⁻¹' D →
      ¬ (F x.swap y.swap).swap ≤ x ∧ ¬ y ≤ (F x.swap y.swap).swap) :
    ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y := by
  intro x hx y hy
  have h := nw x.swap (by simpa using hx) y.swap (by simpa using hy)
  simp only [Prod.swap_swap] at h
  exact ⟨fun h' => h.1 (Prod.swap_le_swap.2 h'), fun h' => h.2 (Prod.swap_le_swap.2 h')⟩

/-- `Layers.cut_prod_layers` with the roles of the coordinates exchanged: `K` end-finite, finitely many *first*
coordinates among the cell values. -/
theorem cut_prod_layers_fst (hI : ∀ g : K, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : K, g ≠ ⊥ → (Set.Ici g).Finite)
    {F : β × K → β × K → β × K} {D : Set (β × K)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (T : Set β) (hT : T.Finite)
    (hTv : (∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) → ∀ x ∈ D, ∀ y, y ∉ D → (F x y).1 ∈ T) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) :=
  cut_of_swap (Layers.cut_prod_layers hI hJ (swap_mono hF) (swap_down hD) hbot htop T hT
    fun nw x hx y hy => hTv (swap_nw nw) _ hx _ hy)

end swap

section collapse
variable {β K : Type*} [CompleteLattice β] [CompleteLattice K]

/-- **Collapse, lowering form.** `L₁, L₂` end-finite. If every corner `F (⊥, k) (⊤, k')` has first coordinate below a
fixed `m ≠ ⊤`, the first coordinates of the cell values can be collapsed to a finite set: lower to
`(⌊z.1⌋, z.2)`, raise to `(⌈z.1⌉, z.2)` (floor and ceiling in a finite guide set), zones as in `zone_lo`. Then
`cut_prod_layers_fst` applies. -/
theorem collapse_lo (hI : ∀ g : β, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : β, g ≠ ⊥ → (Set.Ici g).Finite)
    (hI' : ∀ g : K, g ≠ ⊤ → (Set.Iic g).Finite) (hJ' : ∀ g : K, g ≠ ⊥ → (Set.Ici g).Finite)
    {F : β × K → β × K → β × K} {D : Set (β × K)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (m : β) (hm : m ≠ ⊤)
    (hcorner : ∀ k k' : K, ((⊥ : β), k) ∈ D → ((⊤ : β), k') ∉ D → (F (⊥, k) (⊤, k')).1 ≤ m) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  have nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y := hno
  let S : Set β := ⋃ e ∈ {e : β | e ≤ m ∧ e ≠ ⊥}, Set.Ici e
  have hS : S.Finite := ((hI m hm).subset fun e he => he.1).biUnion fun e he => hJ e he.2
  let N : Finset β := hS.toFinset
  let fl : β → β := fun a => (N.filter (· ≤ a)).sup id
  let cl : β → β := fun a => (N.filter (a ≤ ·)).inf id
  have fl_le : ∀ a, fl a ≤ a := fun a => Finset.sup_le fun f hf => (Finset.mem_filter.1 hf).2
  have le_cl : ∀ a, a ≤ cl a := fun a => Finset.le_inf fun f hf => (Finset.mem_filter.1 hf).2
  have fl_mono : ∀ a b, a ≤ b → fl a ≤ fl b := fun a b h => Finset.sup_mono fun f hf =>
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2.trans h⟩
  have cl_mono : ∀ a b, a ≤ b → cl a ≤ cl b := fun a b h => Finset.inf_mono fun f hf =>
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hf).1, h.trans (Finset.mem_filter.1 hf).2⟩
  let lo : β × K → β × K := fun z => (fl z.1, z.2)
  let hi : β × K → β × K := fun z => (cl z.1, z.2)
  have corner : ∀ x y x' y', x ∈ D → y ∉ D → x' ∈ D → y' ∉ D → x ≤ x' → y ≤ y' → (F x' y').1 ∉ S →
      (F x y).2 ≤ x.2 → y'.2 ≤ (F x' y').2 → (F x y).1 ∈ S := by
    intro x y x' y' hx hy hx' hy' hxx hyy _ hk hk'
    set k := (F x y).2
    set k' := (F x' y').2
    have hsx : ((⊥ : β), k) ≤ x := Prod.mk_le_mk.2 ⟨bot_le, hk⟩
    have hty : y' ≤ ((⊤ : β), k') := Prod.mk_le_mk.2 ⟨le_top, hk'⟩
    have hsD : ((⊥ : β), k) ∈ D := hD _ _ hsx hx
    have htD : ((⊤ : β), k') ∉ D := fun h => hy' (hD _ _ hty h)
    have he1 : (F (⊥, k) y).1 ≠ ⊥ := by
      intro h0
      have he2 : (F (⊥, k) y).2 ≤ k := (Prod.le_def.1 (hF _ _ _ _ hsx le_rfl)).2
      exact (nw _ hsD y hy).1 (Prod.mk_le_mk.2 ⟨h0.le, he2⟩)
    refine Set.mem_biUnion (x := (F (⊥, k) y).1) ⟨?_, he1⟩ ?_
    · exact ((Prod.le_def.1 (hF _ _ _ _ le_rfl (hyy.trans hty))).1).trans (hcorner k k' hsD htD)
    · exact (Prod.le_def.1 (hF _ _ _ _ hsx le_rfl)).1
  obtain ⟨H, hHm, nwH, hval⟩ := zone_lo hF nw (fun z => z.1 ∈ S) lo hi (fun x z => z.2 ≤ x.2) (fun y z => y.2 ≤ z.2)
    (fun z => Prod.mk_le_mk.2 ⟨fl_le _, le_rfl⟩) (fun z => Prod.mk_le_mk.2 ⟨le_cl _, le_rfl⟩)
    (fun x y x' y' _ _ _ _ hxx hyy _ _ => have h := Prod.le_def.1 (hF _ _ _ _ hxx hyy)
      ⟨Prod.mk_le_mk.2 ⟨fl_mono _ _ h.1, h.2⟩, Prod.mk_le_mk.2 ⟨cl_mono _ _ h.1, h.2⟩⟩)
    (fun z z' hz h => Prod.mk_le_mk.2 ⟨Finset.le_sup (f := id)
      (Finset.mem_filter.2 ⟨hS.mem_toFinset.2 hz, (Prod.le_def.1 h).1⟩), (Prod.le_def.1 h).2⟩)
    (fun z z' hz h => Prod.mk_le_mk.2 ⟨Finset.inf_le (f := id)
      (Finset.mem_filter.2 ⟨hS.mem_toFinset.2 hz, (Prod.le_def.1 h).1⟩), (Prod.le_def.1 h).2⟩)
    (fun x z h => (Prod.le_def.1 h).2) (fun y z h => (Prod.le_def.1 h).2) corner
  obtain ⟨H', hH', hHH⟩ := Strip.extend_mono H hHm
  let T : Set β := S ∪ (fun Q : Finset β => Q.sup id) '' (N.powerset : Set (Finset β)) ∪
    (fun Q : Finset β => Q.inf id) '' (N.powerset : Set (Finset β))
  have hT : T.Finite := (hS.union ((Finset.finite_toSet _).image _)).union ((Finset.finite_toSet _).image _)
  obtain ⟨x, hx, y, hy, hw⟩ := cut_prod_layers_fst hI' hJ' hH' hD hbot htop T hT fun _ x hx y hy => by
    rw [hHH x hx y hy]
    rcases hval x hx y hy with ⟨hg, e⟩ | ⟨-, e | e⟩ <;> rw [e]
    · exact Or.inl (Or.inl hg)
    · exact Or.inl (Or.inr ⟨_, Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _)), rfl⟩)
    · exact Or.inr ⟨_, Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _)), rfl⟩
  rw [hHH x hx y hy] at hw
  rcases hw with h | h
  exacts [(nwH x hx y hy).1 h, (nwH x hx y hy).2 h]

/-- **Collapse, raising form**, the dual of `collapse_lo`: every corner `F (⊥, k) (⊤, k')` has first coordinate above
a fixed `n ≠ ⊥`. -/
theorem collapse_hi (hI : ∀ g : β, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : β, g ≠ ⊥ → (Set.Ici g).Finite)
    (hI' : ∀ g : K, g ≠ ⊤ → (Set.Iic g).Finite) (hJ' : ∀ g : K, g ≠ ⊥ → (Set.Ici g).Finite)
    {F : β × K → β × K → β × K} {D : Set (β × K)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (n : β) (hn : n ≠ ⊥)
    (hcorner : ∀ k k' : K, ((⊥ : β), k) ∈ D → ((⊤ : β), k') ∉ D → n ≤ (F (⊥, k) (⊤, k')).1) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  have nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y := hno
  let S : Set β := ⋃ f ∈ {f : β | n ≤ f ∧ f ≠ ⊤}, Set.Iic f
  have hS : S.Finite := ((hJ n hn).subset fun f hf => hf.1).biUnion fun f hf => hI f hf.2
  let N : Finset β := hS.toFinset
  let fl : β → β := fun a => (N.filter (· ≤ a)).sup id
  let cl : β → β := fun a => (N.filter (a ≤ ·)).inf id
  have fl_le : ∀ a, fl a ≤ a := fun a => Finset.sup_le fun f hf => (Finset.mem_filter.1 hf).2
  have le_cl : ∀ a, a ≤ cl a := fun a => Finset.le_inf fun f hf => (Finset.mem_filter.1 hf).2
  have fl_mono : ∀ a b, a ≤ b → fl a ≤ fl b := fun a b h => Finset.sup_mono fun f hf =>
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2.trans h⟩
  have cl_mono : ∀ a b, a ≤ b → cl a ≤ cl b := fun a b h => Finset.inf_mono fun f hf =>
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hf).1, h.trans (Finset.mem_filter.1 hf).2⟩
  let lo : β × K → β × K := fun z => (fl z.1, z.2)
  let hi : β × K → β × K := fun z => (cl z.1, z.2)
  have corner : ∀ x y x' y', x ∈ D → y ∉ D → x' ∈ D → y' ∉ D → x ≤ x' → y ≤ y' → (F x y).1 ∉ S →
      (F x y).2 ≤ x.2 → y'.2 ≤ (F x' y').2 → (F x' y').1 ∈ S := by
    intro x y x' y' hx hy hx' hy' hxx hyy _ hk hk'
    set k := (F x y).2
    set k' := (F x' y').2
    have hsx : ((⊥ : β), k) ≤ x := Prod.mk_le_mk.2 ⟨bot_le, hk⟩
    have hty : y' ≤ ((⊤ : β), k') := Prod.mk_le_mk.2 ⟨le_top, hk'⟩
    have hsD : ((⊥ : β), k) ∈ D := hD _ _ hsx hx
    have htD : ((⊤ : β), k') ∉ D := fun h => hy' (hD _ _ hty h)
    have hr1 : (F x' (⊤, k')).1 ≠ ⊤ := by
      intro h1
      have hr2 : k' ≤ (F x' (⊤, k')).2 := (Prod.le_def.1 (hF _ _ _ _ le_rfl hty)).2
      exact (nw x' hx' _ htD).2 (Prod.mk_le_mk.2 ⟨h1.ge, hr2⟩)
    refine Set.mem_biUnion (x := (F x' (⊤, k')).1) ⟨?_, hr1⟩ ?_
    · exact (hcorner k k' hsD htD).trans (Prod.le_def.1 (hF _ _ _ _ (hsx.trans hxx) le_rfl)).1
    · exact (Prod.le_def.1 (hF _ _ _ _ le_rfl hty)).1

  obtain ⟨H, hHm, nwH, hval⟩ := zone_hi hF nw (fun z => z.1 ∈ S) lo hi (fun x z => z.2 ≤ x.2) (fun y z => y.2 ≤ z.2)
    (fun z => Prod.mk_le_mk.2 ⟨fl_le _, le_rfl⟩) (fun z => Prod.mk_le_mk.2 ⟨le_cl _, le_rfl⟩)
    (fun x y x' y' _ _ _ _ hxx hyy _ _ => have h := Prod.le_def.1 (hF _ _ _ _ hxx hyy)
      ⟨Prod.mk_le_mk.2 ⟨fl_mono _ _ h.1, h.2⟩, Prod.mk_le_mk.2 ⟨cl_mono _ _ h.1, h.2⟩⟩)
    (fun z z' hz h => Prod.mk_le_mk.2 ⟨Finset.le_sup (f := id)
      (Finset.mem_filter.2 ⟨hS.mem_toFinset.2 hz, (Prod.le_def.1 h).1⟩), (Prod.le_def.1 h).2⟩)
    (fun z z' hz h => Prod.mk_le_mk.2 ⟨Finset.inf_le (f := id)
      (Finset.mem_filter.2 ⟨hS.mem_toFinset.2 hz, (Prod.le_def.1 h).1⟩), (Prod.le_def.1 h).2⟩)
    (fun x z h => (Prod.le_def.1 h).2) (fun y z h => (Prod.le_def.1 h).2) corner
  obtain ⟨H', hH', hHH⟩ := Strip.extend_mono H hHm
  let T : Set β := S ∪ (fun Q : Finset β => Q.sup id) '' (N.powerset : Set (Finset β)) ∪
    (fun Q : Finset β => Q.inf id) '' (N.powerset : Set (Finset β))
  have hT : T.Finite := (hS.union ((Finset.finite_toSet _).image _)).union ((Finset.finite_toSet _).image _)
  obtain ⟨x, hx, y, hy, hw⟩ := cut_prod_layers_fst hI' hJ' hH' hD hbot htop T hT fun _ x hx y hy => by
    rw [hHH x hx y hy]
    rcases hval x hx y hy with ⟨hg, e⟩ | ⟨-, e | e⟩ <;> rw [e]
    · exact Or.inl (Or.inl hg)
    · exact Or.inl (Or.inr ⟨_, Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _)), rfl⟩)
    · exact Or.inr ⟨_, Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _)), rfl⟩
  rw [hHH x hx y hy] at hw
  rcases hw with h | h
  exacts [(nwH x hx y hy).1 h, (nwH x hx y hy).2 h]
end collapse

section cross
variable {β K : Type*} [CompleteLattice β] [CompleteLattice K]

/-- **Two orientations.** `L₁, L₂` end-finite. If (under no witness) every cell value lies in a finite set `Z₀`, or
has second coordinate in a finite set `T₂` of middle elements (a horizontal strip), or first coordinate in a finite
set `T₁` of middle elements (a vertical strip), there is a witness. Horizontal values are lowered and raised in the
second-coordinate layers, vertical ones in the first; a horizontal and a vertical value outside the guide set are never
comparable, so the two zone rules do not interact. -/
theorem cut_prod_cross (hI : ∀ g : β, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : β, g ≠ ⊥ → (Set.Ici g).Finite)
    (hI' : ∀ g : K, g ≠ ⊤ → (Set.Iic g).Finite) (hJ' : ∀ g : K, g ≠ ⊥ → (Set.Ici g).Finite)
    {F : β × K → β × K → β × K} {D : Set (β × K)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (Z₀ : Set (β × K)) (hZ₀ : Z₀.Finite)
    (T₁ : Set β) (hT₁ : T₁.Finite) (hT₁m : ∀ a ∈ T₁, a ≠ ⊥ ∧ a ≠ ⊤)
    (T₂ : Set K) (hT₂ : T₂.Finite) (hT₂m : ∀ a ∈ T₂, a ≠ ⊥ ∧ a ≠ ⊤)
    (hval : (∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) →
      ∀ x ∈ D, ∀ y, y ∉ D → F x y ∈ Z₀ ∨ (F x y).2 ∈ T₂ ∨ (F x y).1 ∈ T₁) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  have nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y := hno
  have hval := hval nw
  -- guide sets
  let A₁ : Set β := ⋃ t ∈ T₁, Set.Iic t ∪ Set.Ici t
  have hA₁ : A₁.Finite := hT₁.biUnion fun t ht => (hI t (hT₁m t ht).2).union (hJ t (hT₁m t ht).1)
  let X : Set (β × K) := A₁ ×ˢ T₂
  have hX : X.Finite := hA₁.prod hT₂
  let ZH : K → K → Set (β × K) := fun k k' =>
    {w | w.2 ∈ T₂ ∧ (F (⊥, k) (⊤, k')).1 ≠ ⊤ ∧ ∃ e : β, e ≠ ⊥ ∧ e ≤ (F (⊥, k) (⊤, k')).1 ∧ e ≤ w.1}
  have hZH : ∀ k k', (ZH k k').Finite := by
    intro k k'
    by_cases h : (F (⊥, k) (⊤, k')).1 = ⊤
    · exact Set.finite_empty.subset fun w hw => hw.2.1 h
    · refine ((((hI _ h).subset fun e (he : e ∈ {e : β | e ≤ (F (⊥, k) (⊤, k')).1 ∧ e ≠ ⊥}) => he.1).biUnion
        fun e he => hJ e he.2).prod hT₂).subset ?_
      rintro w ⟨hw, -, e, he, heh, hew⟩
      exact ⟨Set.mem_biUnion ⟨heh, he⟩ hew, hw⟩
  let ZV : β → β → Set (β × K) := fun k k' =>
    {w | w.1 ∈ T₁ ∧ (F (k, ⊥) (k', ⊤)).2 ≠ ⊤ ∧ ∃ e : K, e ≠ ⊥ ∧ e ≤ (F (k, ⊥) (k', ⊤)).2 ∧ e ≤ w.2}
  have hZV : ∀ k k', (ZV k k').Finite := by
    intro k k'
    by_cases h : (F (k, ⊥) (k', ⊤)).2 = ⊤
    · exact Set.finite_empty.subset fun w hw => hw.2.1 h
    · refine (hT₁.prod (((hI' _ h).subset fun e (he : e ∈ {e : K | e ≤ (F (k, ⊥) (k', ⊤)).2 ∧ e ≠ ⊥}) => he.1).biUnion
        fun e he => hJ' e he.2)).subset ?_
      rintro w ⟨hw, -, e, he, heh, hew⟩
      exact ⟨hw, Set.mem_biUnion ⟨heh, he⟩ hew⟩
  let Γ : Set (β × K) := Z₀ ∪ X ∪ (⋃ p ∈ T₂ ×ˢ T₂, ZH p.1 p.2) ∪ (⋃ p ∈ T₁ ×ˢ T₁, ZV p.1 p.2)
  have hΓ : Γ.Finite := ((hZ₀.union hX).union ((hT₂.prod hT₂).biUnion fun p _ => hZH p.1 p.2)).union
    ((hT₁.prod hT₁).biUnion fun p _ => hZV p.1 p.2)
  let N : Finset (β × K) := hΓ.toFinset
  let gl : β × K → β × K := fun z => (N.filter (· ≤ z)).sup id
  let gu : β × K → β × K := fun z => (N.filter (z ≤ ·)).inf id
  have gl_le : ∀ z, gl z ≤ z := fun z => Finset.sup_le fun f hf => (Finset.mem_filter.1 hf).2
  have le_gu : ∀ z, z ≤ gu z := fun z => Finset.le_inf fun f hf => (Finset.mem_filter.1 hf).2
  have gl_mono : ∀ z z', z ≤ z' → gl z ≤ gl z' := fun z z' h => Finset.sup_mono fun f hf =>
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2.trans h⟩
  have gu_mono : ∀ z z', z ≤ z' → gu z ≤ gu z' := fun z z' h => Finset.inf_mono fun f hf =>
    Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hf).1, h.trans (Finset.mem_filter.1 hf).2⟩
  have le_gl : ∀ z z', z ∈ Γ → z ≤ z' → z ≤ gl z' := fun z z' hz h =>
    Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hΓ.mem_toFinset.2 hz, h⟩)
  have gu_le : ∀ z z', z' ∈ Γ → z ≤ z' → gu z ≤ z' := fun z z' hz h =>
    Finset.inf_le (f := id) (Finset.mem_filter.2 ⟨hΓ.mem_toFinset.2 hz, h⟩)
  -- type: horizontal iff the second coordinate is in `T₂`
  let lo : β × K → β × K := fun z => if z.2 ∈ T₂ then ((⊥ : β), z.2) ⊔ gl z else (z.1, (⊥ : K)) ⊔ gl z
  let hi : β × K → β × K := fun z => if z.2 ∈ T₂ then ((⊤ : β), z.2) ⊓ gu z else (z.1, (⊤ : K)) ⊓ gu z
  let Sl : β × K → β × K → Prop := fun x z => if z.2 ∈ T₂ then z.2 ≤ x.2 else z.1 ≤ x.1
  let Sr : β × K → β × K → Prop := fun y z => if z.2 ∈ T₂ then y.2 ≤ z.2 else y.1 ≤ z.1
  -- a non-guide value outside the horizontal strips is vertical
  have vert : ∀ x ∈ D, ∀ y, y ∉ D → F x y ∉ Γ → (F x y).2 ∉ T₂ → (F x y).1 ∈ T₁ := by
    intro x hx y hy hg h2
    rcases hval x hx y hy with h | h | h
    · exact absurd (Or.inl (Or.inl (Or.inl h))) hg
    · exact absurd h h2
    · exact h
  -- comparable non-guide values have the same type
  have same : ∀ x y x' y', x ∈ D → y ∉ D → x' ∈ D → y' ∉ D → F x y ≤ F x' y' → F x y ∉ Γ → F x' y' ∉ Γ →
      ((F x y).2 ∈ T₂ ↔ (F x' y').2 ∈ T₂) := by
    intro x y x' y' hx hy hx' hy' hzz g1 g2
    constructor
    · intro h1; by_contra h2
      have hv := vert x' hx' y' hy' g2 h2
      exact g1 (Or.inl (Or.inl (Or.inr ⟨Set.mem_biUnion hv (Or.inl (Prod.le_def.1 hzz).1), h1⟩)))
    · intro h2; by_contra h1
      have hv := vert x hx y hy g1 h1
      exact g2 (Or.inl (Or.inl (Or.inr ⟨Set.mem_biUnion hv (Or.inr (Prod.le_def.1 hzz).1), h2⟩)))
  have lo_le : ∀ z, lo z ≤ z := by
    intro z; simp only [lo]; split_ifs
    · exact sup_le (Prod.mk_le_mk.2 ⟨bot_le, le_rfl⟩) (gl_le z)
    · exact sup_le (Prod.mk_le_mk.2 ⟨le_rfl, bot_le⟩) (gl_le z)
  have le_hi : ∀ z, z ≤ hi z := by
    intro z; simp only [hi]; split_ifs
    · exact le_inf (Prod.mk_le_mk.2 ⟨le_top, le_rfl⟩) (le_gu z)
    · exact le_inf (Prod.mk_le_mk.2 ⟨le_rfl, le_top⟩) (le_gu z)
  have corner : ∀ x y x' y', x ∈ D → y ∉ D → x' ∈ D → y' ∉ D → x ≤ x' → y ≤ y' → F x' y' ∉ Γ →
      Sl x (F x y) → Sr y' (F x' y') → F x y ∈ Γ := by
    intro x y x' y' hx hy hx' hy' hxx hyy g2 hk hk'
    by_contra g1
    have hs := same x y x' y' hx hy hx' hy' (hF _ _ _ _ hxx hyy) g1 g2
    by_cases h2 : (F x y).2 ∈ T₂
    · have h2' := hs.1 h2
      simp only [Sl, Sr, h2, h2', if_true] at hk hk'
      set k := (F x y).2
      set k' := (F x' y').2
      have hsx : ((⊥ : β), k) ≤ x := Prod.mk_le_mk.2 ⟨bot_le, hk⟩
      have hty : y' ≤ ((⊤ : β), k') := Prod.mk_le_mk.2 ⟨le_top, hk'⟩
      have hsD : ((⊥ : β), k) ∈ D := hD _ _ hsx hx
      have htD : ((⊤ : β), k') ∉ D := fun h => hy' (hD _ _ hty h)
      have hh1 : (F (⊥, k) (⊤, k')).1 ≠ ⊤ := by
        intro h1
        have hr : F (⊥, k) (⊤, k') ≤ F x' (⊤, k') := hF _ _ _ _ (hsx.trans hxx) le_rfl
        have hr1 : (F x' (⊤, k')).1 = ⊤ := top_le_iff.1 (by have := (Prod.le_def.1 hr).1; rwa [h1] at this)
        have hr2 : k' ≤ (F x' (⊤, k')).2 := (Prod.le_def.1 (hF _ _ _ _ le_rfl hty)).2
        exact (nw x' hx' _ htD).2 (Prod.mk_le_mk.2 ⟨hr1.ge, hr2⟩)
      have he1 : (F (⊥, k) y).1 ≠ ⊥ := by
        intro h0
        have he2 : (F (⊥, k) y).2 ≤ k := (Prod.le_def.1 (hF _ _ _ _ hsx le_rfl)).2
        exact (nw _ hsD y hy).1 (Prod.mk_le_mk.2 ⟨h0.le, he2⟩)
      exact g1 (Or.inl (Or.inr (Set.mem_biUnion (x := (k, k')) ⟨h2, h2'⟩ ⟨h2, hh1, (F (⊥, k) y).1, he1,
        (Prod.le_def.1 (hF _ _ _ _ le_rfl (hyy.trans hty))).1, (Prod.le_def.1 (hF _ _ _ _ hsx le_rfl)).1⟩)))
    · have h2' : (F x' y').2 ∉ T₂ := fun h => h2 (hs.2 h)
      simp only [Sl, Sr, h2, h2', if_false] at hk hk'
      have h1 := vert x hx y hy g1 h2
      have h1' := vert x' hx' y' hy' g2 h2'
      set k := (F x y).1
      set k' := (F x' y').1
      have hsx : (k, (⊥ : K)) ≤ x := Prod.mk_le_mk.2 ⟨hk, bot_le⟩
      have hty : y' ≤ (k', (⊤ : K)) := Prod.mk_le_mk.2 ⟨hk', le_top⟩
      have hsD : (k, (⊥ : K)) ∈ D := hD _ _ hsx hx
      have htD : (k', (⊤ : K)) ∉ D := fun h => hy' (hD _ _ hty h)
      have hh1 : (F (k, ⊥) (k', ⊤)).2 ≠ ⊤ := by
        intro h1
        have hr : F (k, ⊥) (k', ⊤) ≤ F x' (k', ⊤) := hF _ _ _ _ (hsx.trans hxx) le_rfl
        have hr1 : (F x' (k', ⊤)).2 = ⊤ := top_le_iff.1 (by have := (Prod.le_def.1 hr).2; rwa [h1] at this)
        have hr2 : k' ≤ (F x' (k', ⊤)).1 := (Prod.le_def.1 (hF _ _ _ _ le_rfl hty)).1
        exact (nw x' hx' _ htD).2 (Prod.mk_le_mk.2 ⟨hr2, hr1.ge⟩)
      have he1 : (F (k, ⊥) y).2 ≠ ⊥ := by
        intro h0
        have he2 : (F (k, ⊥) y).1 ≤ k := (Prod.le_def.1 (hF _ _ _ _ hsx le_rfl)).1
        exact (nw _ hsD y hy).1 (Prod.mk_le_mk.2 ⟨he2, h0.le⟩)
      exact g1 (Or.inr (Set.mem_biUnion (x := (k, k')) ⟨h1, h1'⟩ ⟨h1, hh1, (F (k, ⊥) y).2, he1,
        (Prod.le_def.1 (hF _ _ _ _ le_rfl (hyy.trans hty))).2, (Prod.le_def.1 (hF _ _ _ _ hsx le_rfl)).2⟩))
  obtain ⟨H, hHm, nwH, hvalH⟩ := zone_lo hF nw (· ∈ Γ) lo hi Sl Sr lo_le le_hi
    (by
      intro x y x' y' hx hy hx' hy' hxx hyy g1 g2
      have hzz := hF _ _ _ _ hxx hyy
      have hs := same x y x' y' hx hy hx' hy' hzz g1 g2
      have h := Prod.le_def.1 hzz
      by_cases h2 : (F x y).2 ∈ T₂
      · simp only [lo, hi, h2, hs.1 h2, if_true]
        exact ⟨sup_le_sup (Prod.mk_le_mk.2 ⟨le_rfl, h.2⟩) (gl_mono _ _ hzz),
          inf_le_inf (Prod.mk_le_mk.2 ⟨le_rfl, h.2⟩) (gu_mono _ _ hzz)⟩
      · have h2' : (F x' y').2 ∉ T₂ := fun h' => h2 (hs.2 h')
        simp only [lo, hi, h2, h2', if_false]
        exact ⟨sup_le_sup (Prod.mk_le_mk.2 ⟨h.1, le_rfl⟩) (gl_mono _ _ hzz),
          inf_le_inf (Prod.mk_le_mk.2 ⟨h.1, le_rfl⟩) (gu_mono _ _ hzz)⟩)
    (fun z z' hz h => by simp only [lo]; split_ifs <;> exact le_sup_of_le_right (le_gl _ _ hz h))
    (fun z z' hz h => by simp only [hi]; split_ifs <;> exact inf_le_of_right_le (gu_le _ _ hz h))
    (fun x z h => by
      simp only [Sl]; simp only [lo] at h; split_ifs at h ⊢
      · exact (Prod.le_def.1 (le_sup_left.trans h)).2
      · exact (Prod.le_def.1 (le_sup_left.trans h)).1)
    (fun y z h => by
      simp only [Sr]; simp only [hi] at h; split_ifs at h ⊢
      · exact (Prod.le_def.1 (h.trans inf_le_left)).2
      · exact (Prod.le_def.1 (h.trans inf_le_left)).1)
    corner
  -- finitely many values
  let Ψ : Set (β × K) :=
    (fun p : K × Finset (β × K) => ((⊥ : β), p.1) ⊔ p.2.sup id) '' (T₂ ×ˢ (N.powerset : Set _)) ∪
    (fun p : K × Finset (β × K) => ((⊤ : β), p.1) ⊓ p.2.inf id) '' (T₂ ×ˢ (N.powerset : Set _)) ∪
    (fun p : β × Finset (β × K) => (p.1, (⊥ : K)) ⊔ p.2.sup id) '' (T₁ ×ˢ (N.powerset : Set _)) ∪
    (fun p : β × Finset (β × K) => (p.1, (⊤ : K)) ⊓ p.2.inf id) '' (T₁ ×ˢ (N.powerset : Set _))
  have hΨ : Ψ.Finite :=
    ((((hT₂.prod (Finset.finite_toSet _)).image _).union ((hT₂.prod (Finset.finite_toSet _)).image _)).union
      ((hT₁.prod (Finset.finite_toSet _)).image _)).union ((hT₁.prod (Finset.finite_toSet _)).image _)
  have hpow : ∀ z, N.filter (· ≤ z) ∈ (N.powerset : Set (Finset (β × K))) ∧
      N.filter (z ≤ ·) ∈ (N.powerset : Set (Finset (β × K))) := fun z =>
    ⟨Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _)),
      Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _))⟩
  have hv : ∀ x ∈ D, ∀ y, y ∉ D → H x y ∈ Γ ∪ Ψ := by
    intro x hx y hy
    rcases hvalH x hx y hy with ⟨hg, e⟩ | ⟨hg, e | e⟩
    · rw [e]; exact Or.inl hg
    · rw [e]; simp only [lo]
      split_ifs with h2
      · exact Or.inr (Or.inl (Or.inl (Or.inl ⟨((F x y).2, _), ⟨h2, (hpow _).1⟩, rfl⟩)))
      · exact Or.inr (Or.inl (Or.inr ⟨((F x y).1, _), ⟨vert x hx y hy hg h2, (hpow _).1⟩, rfl⟩))
    · rw [e]; simp only [hi]
      split_ifs with h2
      · exact Or.inr (Or.inl (Or.inl (Or.inr ⟨((F x y).2, _), ⟨h2, (hpow _).2⟩, rfl⟩)))
      · exact Or.inr (Or.inr ⟨((F x y).1, _), ⟨vert x hx y hy hg h2, (hpow _).2⟩, rfl⟩)
  obtain ⟨H', hH', hHH⟩ := Strip.extend_mono H hHm
  obtain ⟨x, hx, y, hy, hw⟩ := Pin.cut_of_values_in_finite hH' hD hbot htop (Γ ∪ Ψ) (hΓ.union hΨ)
    fun _ x hx y hy => (hHH x hx y hy).symm ▸ hv x hx y hy
  rw [hHH x hx y hy] at hw
  rcases hw with h | h
  exacts [(nwH x hx y hy).1 h, (nwH x hx y hy).2 h]

end cross

section main
variable {β K : Type*} [CompleteLattice β] [CompleteLattice K]

omit [CompleteLattice β] [CompleteLattice K] in
private lemma prod_ne_bot [CompleteLattice β] [CompleteLattice K] {z : β × K} (h : z ≠ ⊥) : z.1 ≠ ⊥ ∨ z.2 ≠ ⊥ := by
  by_contra h'; push_neg at h'; exact h (Prod.ext h'.1 h'.2)

omit [CompleteLattice β] [CompleteLattice K] in
private lemma prod_ne_top [CompleteLattice β] [CompleteLattice K] {z : β × K} (h : z ≠ ⊤) : z.1 ≠ ⊤ ∨ z.2 ≠ ⊤ := by
  by_contra h'; push_neg at h'; exact h (Prod.ext h'.1 h'.2)

/-- Elements above some `e ≤ a`, `e ≠ ⊥` (finite when `a ≠ ⊤` in an end-finite lattice). -/
private def Lo {γ : Type*} [CompleteLattice γ] (a : γ) : Set γ := ⋃ e ∈ {e | e ≤ a ∧ e ≠ ⊥}, Set.Ici e
/-- Elements below some `f ≥ a`, `f ≠ ⊤`. -/
private def Hi {γ : Type*} [CompleteLattice γ] (a : γ) : Set γ := ⋃ f ∈ {f | a ≤ f ∧ f ≠ ⊤}, Set.Iic f

omit [CompleteLattice β] [CompleteLattice K] in
private lemma memLo {γ : Type*} [CompleteLattice γ] {a e z : γ} (h1 : e ≤ a) (h2 : e ≠ ⊥) (h3 : e ≤ z) : z ∈ Lo a :=
  Set.mem_biUnion (x := e) ⟨h1, h2⟩ h3

omit [CompleteLattice β] [CompleteLattice K] in
private lemma memHi {γ : Type*} [CompleteLattice γ] {a f z : γ} (h1 : a ≤ f) (h2 : f ≠ ⊤) (h3 : z ≤ f) : z ∈ Hi a :=
  Set.mem_biUnion (x := f) ⟨h1, h2⟩ h3

/-- **Cut on `L₁ × L₂`** for complete lattices `L₁, L₂` whose proper principal ideals and filters are finite (e.g.
`Ω × Ω`). Case analysis on the corner `c = F(⊥, ⊤)`:
* `c₁ = ⊥, c₂ ≠ ⊤` (or `c₁ = ⊤, c₂ ≠ ⊥`, or the same with the coordinates exchanged): the values have finitely many
  second (first) coordinates, through `F(⊥, y) ≤ c` (`c ≤ F(x, ⊤)`); `cut_prod_layers`;
* `c₁, c₂` both middle: every value is in a finite box or a horizontal or vertical strip; `cut_prod_cross`;
* `c = (⊥, ⊤)` or `(⊤, ⊥)`: the corners of one orientation are bounded through the anchor `(⊥, ⊤)` resp. `(⊤, ⊥)`,
  as a row if it is in `D` and as a column if not; `collapse_lo` / `collapse_hi`. -/
theorem cut_prod_end_finite (hI : ∀ g : β, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : β, g ≠ ⊥ → (Set.Ici g).Finite)
    (hI' : ∀ g : K, g ≠ ⊤ → (Set.Iic g).Finite) (hJ' : ∀ g : K, g ≠ ⊥ → (Set.Ici g).Finite)
    {F : β × K → β × K → β × K} {D : Set (β × K)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) : ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  have nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y := by push_neg at hno; exact hno
  apply hno
  set c := F ⊥ ⊤ with hc
  have hc0 : c ≠ ⊥ := fun h => (nw ⊥ hbot ⊤ htop).1 (h.le)
  have hc1 : c ≠ ⊤ := fun h => (nw ⊥ hbot ⊤ htop).2 (h.ge)
  have hw : ∀ y, y ∉ D → F ⊥ y ≤ c ∧ F ⊥ y ≠ ⊥ := fun y hy =>
    ⟨hF _ _ _ _ le_rfl le_top, fun h => (nw ⊥ hbot y hy).1 h.le⟩
  have hv : ∀ x, x ∈ D → c ≤ F x ⊤ ∧ F x ⊤ ≠ ⊤ := fun x hx =>
    ⟨hF _ _ _ _ bot_le le_rfl, fun h => (nw x hx ⊤ htop).2 h.ge⟩
  have hwz : ∀ x y, F ⊥ y ≤ F x y := fun x y => hF _ _ _ _ bot_le le_rfl
  have hzv : ∀ x y, F x y ≤ F x ⊤ := fun x y => hF _ _ _ _ le_rfl le_top
  -- finite "filter below" and "ideal above" sets
  have hLo₁ : ∀ a : β, a ≠ ⊤ → (Lo a).Finite := fun a ha =>
    ((hI a ha).subset fun e (he : e ≤ a ∧ e ≠ ⊥) => he.1).biUnion fun e he => hJ e he.2
  have hHi₁ : ∀ a : β, a ≠ ⊥ → (Hi a).Finite := fun a ha =>
    ((hJ a ha).subset fun e (he : a ≤ e ∧ e ≠ ⊤) => he.1).biUnion fun e he => hI e he.2
  have hLo₂ : ∀ a : K, a ≠ ⊤ → (Lo a).Finite := fun a ha =>
    ((hI' a ha).subset fun e (he : e ≤ a ∧ e ≠ ⊥) => he.1).biUnion fun e he => hJ' e he.2
  have hHi₂ : ∀ a : K, a ≠ ⊥ → (Hi a).Finite := fun a ha =>
    ((hJ' a ha).subset fun e (he : a ≤ e ∧ e ≠ ⊤) => he.1).biUnion fun e he => hI' e he.2
  by_cases c1b : c.1 = ⊥
  · by_cases c2t : c.2 = ⊤
    · -- c = (⊥, ⊤)
      by_cases hm : ((⊥ : β), (⊤ : K)) ∈ D
      · have hM := hv _ hm
        have hM2 : (F ((⊥ : β), (⊤ : K)) ⊤).2 = ⊤ := top_le_iff.1 (c2t ▸ (Prod.le_def.1 hM.1).2)
        have hM1 : (F ((⊥ : β), (⊤ : K)) ⊤).1 ≠ ⊤ := fun h => hM.2 (Prod.ext h hM2)
        exact collapse_lo hI hJ hI' hJ' hF hD hbot htop _ hM1 fun k k' hk hk' =>
          (Prod.le_def.1 (hF _ _ _ _ (Prod.mk_le_mk.2 ⟨le_rfl, le_top⟩) le_top)).1
      · have hN := hw _ hm
        have hN1 : (F ⊥ ((⊥ : β), (⊤ : K))).1 = ⊥ := le_bot_iff.1 (c1b ▸ (Prod.le_def.1 hN.1).1)
        have hN2 : (F ⊥ ((⊥ : β), (⊤ : K))).2 ≠ ⊥ := fun h => hN.2 (Prod.ext hN1 h)
        refine cut_of_swap (collapse_hi hI' hJ' hI hJ (swap_mono hF) (swap_down hD) hbot htop _ hN2 ?_)
        intro k k' hk hk'
        simp only [Prod.swap_prod_mk, Prod.fst_swap]
        exact (Prod.le_def.1 (hF _ _ _ _ bot_le (Prod.mk_le_mk.2 ⟨bot_le, le_rfl⟩))).2
    · -- c₁ = ⊥, c₂ ≠ ⊤: second coordinates in `Lo c₂`
      exact Layers.cut_prod_layers hI hJ hF hD hbot htop (Lo c.2) (hLo₂ _ c2t) fun _ x hx y hy => by
        obtain ⟨h1, h2⟩ := hw y hy
        have e1 : (F ⊥ y).1 = ⊥ := le_bot_iff.1 (c1b ▸ (Prod.le_def.1 h1).1)
        exact memLo (Prod.le_def.1 h1).2 (fun h => h2 (Prod.ext e1 h)) (Prod.le_def.1 (hwz x y)).2
  by_cases c1t : c.1 = ⊤
  · by_cases c2b : c.2 = ⊥
    · -- c = (⊤, ⊥)
      by_cases hm : ((⊤ : β), (⊥ : K)) ∈ D
      · have hM := hv _ hm
        have hM1 : (F ((⊤ : β), (⊥ : K)) ⊤).1 = ⊤ := top_le_iff.1 (c1t ▸ (Prod.le_def.1 hM.1).1)
        have hM2 : (F ((⊤ : β), (⊥ : K)) ⊤).2 ≠ ⊤ := fun h => hM.2 (Prod.ext hM1 h)
        refine cut_of_swap (collapse_lo hI' hJ' hI hJ (swap_mono hF) (swap_down hD) hbot htop _ hM2 ?_)
        intro k k' hk hk'
        simp only [Prod.swap_prod_mk, Prod.fst_swap]
        exact (Prod.le_def.1 (hF _ _ _ _ (Prod.mk_le_mk.2 ⟨le_top, le_rfl⟩) le_top)).2
      · have hN := hw _ hm
        have hN2 : (F ⊥ ((⊤ : β), (⊥ : K))).2 = ⊥ := le_bot_iff.1 (c2b ▸ (Prod.le_def.1 hN.1).2)
        have hN1 : (F ⊥ ((⊤ : β), (⊥ : K))).1 ≠ ⊥ := fun h => hN.2 (Prod.ext h hN2)
        exact collapse_hi hI hJ hI' hJ' hF hD hbot htop _ hN1 fun k k' hk hk' =>
          (Prod.le_def.1 (hF _ _ _ _ bot_le (Prod.mk_le_mk.2 ⟨le_rfl, bot_le⟩))).1
    · -- c₁ = ⊤, c₂ ≠ ⊥: second coordinates in `Hi c₂`
      exact Layers.cut_prod_layers hI hJ hF hD hbot htop (Hi c.2) (hHi₂ _ c2b) fun _ x hx y hy => by
        obtain ⟨h1, h2⟩ := hv x hx
        have e1 : (F x ⊤).1 = ⊤ := top_le_iff.1 (c1t ▸ (Prod.le_def.1 h1).1)
        exact memHi (Prod.le_def.1 h1).2 (fun h => h2 (Prod.ext e1 h)) (Prod.le_def.1 (hzv x y)).2
  by_cases c2b : c.2 = ⊥
  · -- first coordinates in `Lo c₁`
    exact cut_prod_layers_fst hI' hJ' hF hD hbot htop (Lo c.1) (hLo₁ _ c1t) fun _ x hx y hy => by
      obtain ⟨h1, h2⟩ := hw y hy
      have e2 : (F ⊥ y).2 = ⊥ := le_bot_iff.1 (c2b ▸ (Prod.le_def.1 h1).2)
      exact memLo (Prod.le_def.1 h1).1 (fun h => h2 (Prod.ext h e2)) (Prod.le_def.1 (hwz x y)).1
  by_cases c2t : c.2 = ⊤
  · -- first coordinates in `Hi c₁`
    exact cut_prod_layers_fst hI' hJ' hF hD hbot htop (Hi c.1) (hHi₁ _ c1b) fun _ x hx y hy => by
      obtain ⟨h1, h2⟩ := hv x hx
      have e2 : (F x ⊤).2 = ⊤ := top_le_iff.1 (c2t ▸ (Prod.le_def.1 h1).2)
      exact memHi (Prod.le_def.1 h1).1 (fun h => h2 (Prod.ext h e2)) (Prod.le_def.1 (hzv x y)).1
  -- both coordinates of the corner in the middle: boxes and strips
  refine cut_prod_cross hI hJ hI' hJ' hF hD hbot htop ((Lo c.1 ∪ Hi c.1) ×ˢ (Lo c.2 ∪ Hi c.2))
    (((hLo₁ _ c1t).union (hHi₁ _ c1b)).prod ((hLo₂ _ c2t).union (hHi₂ _ c2b)))
    (Lo c.1 ∩ Hi c.1) ((hLo₁ _ c1t).inter_of_left _) ?_ (Lo c.2 ∩ Hi c.2) ((hLo₂ _ c2t).inter_of_left _) ?_ ?_
  · rintro a ⟨ha1, ha2⟩
    obtain ⟨e, ⟨-, he⟩, hea⟩ := Set.mem_iUnion₂.1 ha1
    obtain ⟨f, ⟨-, hf⟩, haf⟩ := Set.mem_iUnion₂.1 ha2
    exact ⟨fun h => he (le_bot_iff.1 (h ▸ hea)), fun h => hf (top_le_iff.1 (h ▸ haf))⟩
  · rintro a ⟨ha1, ha2⟩
    obtain ⟨e, ⟨-, he⟩, hea⟩ := Set.mem_iUnion₂.1 ha1
    obtain ⟨f, ⟨-, hf⟩, haf⟩ := Set.mem_iUnion₂.1 ha2
    exact ⟨fun h => he (le_bot_iff.1 (h ▸ hea)), fun h => hf (top_le_iff.1 (h ▸ haf))⟩
  · intro _ x hx y hy
    obtain ⟨w1, w2⟩ := hw y hy
    obtain ⟨v1, v2⟩ := hv x hx
    have hw' := Prod.le_def.1 w1
    have hv' := Prod.le_def.1 v1
    have hwz' := Prod.le_def.1 (hwz x y)
    have hzv' := Prod.le_def.1 (hzv x y)
    by_cases e1 : (F ⊥ y).1 = ⊥
    · have e2 : (F ⊥ y).2 ≠ ⊥ := fun h => w2 (Prod.ext e1 h)
      have z2 : (F x y).2 ∈ Lo c.2 := memLo hw'.2 e2 hwz'.2
      by_cases f2 : (F x ⊤).2 = ⊤
      · have f1 : (F x ⊤).1 ≠ ⊤ := fun h => v2 (Prod.ext h f2)
        exact Or.inl ⟨Or.inr (memHi hv'.1 f1 hzv'.1), Or.inl z2⟩
      · exact Or.inr (Or.inl ⟨z2, memHi hv'.2 f2 hzv'.2⟩)
    · have z1 : (F x y).1 ∈ Lo c.1 := memLo hw'.1 e1 hwz'.1
      by_cases f1 : (F x ⊤).1 = ⊤
      · have f2 : (F x ⊤).2 ≠ ⊤ := fun h => v2 (Prod.ext f1 h)
        exact Or.inl ⟨Or.inl z1, Or.inr (memHi hv'.2 f2 hzv'.2)⟩
      · exact Or.inr (Or.inr ⟨z1, memHi hv'.1 f1 hzv'.1⟩)

end main

end Mordor.Plane

namespace Mordor
open Plane

/-- **CL on `L₁ × L₂`** for complete lattices with finite proper principal ideals and filters, e.g. `Ω × Ω`. -/
theorem semi_of_prod_end_finite {β K : Type*} [CompleteLattice β] [CompleteLattice K]
    (hI : ∀ g : β, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : β, g ≠ ⊥ → (Set.Ici g).Finite)
    (hI' : ∀ g : K, g ≠ ⊤ → (Set.Iic g).Finite) (hJ' : ∀ g : K, g ≠ ⊥ → (Set.Ici g).Finite)
    (F : β × K →o β × K →o β × K) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_prod_end_finite hI hJ hI' hJ' (F := fun x y => F x y)
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x y h hy => hD h hy) (hD bot_le hd)
    (fun ht => hu (hD le_top ht))

end Mordor
