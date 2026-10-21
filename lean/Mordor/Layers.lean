import Mordor.Strip

/-!
# Layers: the Cut Lemma on `L × K` for every finite `K` (log §34.3z″)

`L` is a complete lattice whose proper principal ideals and filters are finite (end-finite, e.g. `Ω`), `K` is any
finite complete lattice. No reset, no strips. Write `s k = (⊥, k)` and `t k = (⊤, k)`.

* **Corner lemma** (`corner`). Let `(x, y) ≤ (x', y')` be cells, `z = F x y` with `z.2 ≤ x.2` (so `s z.2 ≤ x`) and
  `z' = F x' y'` with `y'.2 ≤ z'.2` (so `y' ≤ t z'.2`). Put `h = F (s z.2) (t z'.2)`. Then `h.1 ≠ ⊤`, and
  `e = F (s z.2) y` has `e.1 ≠ ⊥`; since `e ≤ h` and `e ≤ z`, `z.1 ∈ ↑e.1` with `e.1 ∈ ↓h.1`. So `z` lies in a finite
  set `Γ` fixed in advance: the union over the finitely many pairs `(k, k')` of `{w | ∃ e ≠ ⊥, e ≤ h(k,k').1, e ≤ w.1}`.
* **Modification.** A value `z ∉ Γ` at a cell is *lowered* to `(⊥, z.2) ⊔ ⋁{γ ∈ Γ | γ ≤ z}` when some cell above it
  carries a value `z' ∉ Γ` with `y'.2 ≤ z'.2`, and *raised* to `(⊤, z.2) ⊓ ⋀{γ ∈ Γ | z ≤ γ}` otherwise. Lowered cells
  form a down-set, so a raised value never sits below a lowered one. A lowered value is witness-free because
  `z.2 ≰ x.2` (corner lemma); a raised value is witness-free because `y.2 ≰ z.2` (else the cell lowers itself).
* The result has finitely many values; `Strip.extend_mono` and `Pin.cut_of_values_in_finite` finish.

The proof only needs finitely many *layers in use*: `cut_prod_layers` takes any complete `K` and assumes that the cell
values have second coordinates in a finite set. `cut_prod_finite` is the case `K` finite.

With `K` trivial this is `Pin.cut_of_end_finite`. It subsumes `Strip.cut_prod_three` and `Strips.cut_prod_antichain`,
and settles `Ω × C₄`, the nested-strip case left open in §34.3z′.
-/

namespace Mordor.Layers
open Finset Classical

variable {β K : Type*} [CompleteLattice β] [CompleteLattice K]

omit [CompleteLattice β] [CompleteLattice K] in
private lemma fin_of_fst [Preorder β] {S : Set β} (hS : S.Finite) {T : Set K} (hT : T.Finite) {X : Set (β × K)}
    (h : ∀ z ∈ X, z.1 ∈ S ∧ z.2 ∈ T) : X.Finite :=
  (hS.prod hT).subset fun z hz => h z hz

/-- **Cut on `L × K` with finitely many layers in use.** `L` complete with finite proper principal ideals and filters,
`K` any complete lattice; if (under no witness) the cell values have second coordinates in a finite set `T`, there is
a witness. -/
theorem cut_prod_layers (hI : ∀ g : β, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : β, g ≠ ⊥ → (Set.Ici g).Finite)
    {F : β × K → β × K → β × K} {D : Set (β × K)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (T : Set K) (hT : T.Finite)
    (hTv : (∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) → ∀ x ∈ D, ∀ y, y ∉ D → (F x y).2 ∈ T) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  have nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y := hno
  have hTv := hTv nw
  let s : K → β × K := fun k => (⊥, k)
  let t : K → β × K := fun k => (⊤, k)
  -- the guide set
  let Zc : K → K → Set (β × K) := fun k k' =>
    {w | w.2 ∈ T ∧ (F (s k) (t k')).1 ≠ ⊤ ∧ ∃ e : β, e ≠ ⊥ ∧ e ≤ (F (s k) (t k')).1 ∧ e ≤ w.1}
  have hZc : ∀ k k', (Zc k k').Finite := by
    intro k k'
    by_cases h : (F (s k) (t k')).1 = ⊤
    · exact Set.finite_empty.subset fun w hw => hw.2.1 h
    · refine fin_of_fst (S := ⋃ e ∈ {e : β | e ≤ (F (s k) (t k')).1 ∧ e ≠ ⊥}, Set.Ici e)
        (((hI _ h).subset fun e he => he.1).biUnion fun e he => hJ e he.2) hT ?_
      rintro w ⟨hw, -, e, he, heh, hew⟩
      exact ⟨Set.mem_biUnion ⟨heh, he⟩ hew, hw⟩
  let Γ : Set (β × K) := ⋃ p ∈ T ×ˢ T, Zc p.1 p.2
  have hΓ : Γ.Finite := (hT.prod hT).biUnion fun p _ => hZc p.1 p.2
  -- corner lemma
  have corner : ∀ x y x' y', x ∈ D → y ∉ D → x' ∈ D → y' ∉ D → x ≤ x' → y ≤ y' →
      (F x y).2 ≤ x.2 → y'.2 ≤ (F x' y').2 → F x y ∈ Γ := by
    intro x y x' y' hx hy hx' hy' hxx hyy hk hk'
    set k := (F x y).2
    set k' := (F x' y').2
    have hsx : s k ≤ x := Prod.mk_le_mk.2 ⟨bot_le, hk⟩
    have hty : y' ≤ t k' := Prod.mk_le_mk.2 ⟨le_top, hk'⟩
    have hsD : s k ∈ D := hD _ _ hsx hx
    have htD : t k' ∉ D := fun h => hy' (hD _ _ hty h)
    have hh1 : (F (s k) (t k')).1 ≠ ⊤ := by
      intro h1
      have hr : F (s k) (t k') ≤ F x' (t k') := hF _ _ _ _ (hsx.trans hxx) le_rfl
      have hr1 : (F x' (t k')).1 = ⊤ := top_le_iff.1 (h1 ▸ (Prod.le_def.1 hr).1)
      have hr2 : k' ≤ (F x' (t k')).2 := (Prod.le_def.1 (hF _ _ _ _ le_rfl hty)).2
      exact (nw x' hx' (t k') htD).2 (Prod.mk_le_mk.2 ⟨hr1.ge, hr2⟩)
    have he1 : (F (s k) y).1 ≠ ⊥ := by
      intro h0
      have he2 : (F (s k) y).2 ≤ k := (Prod.le_def.1 (hF _ _ _ _ hsx le_rfl)).2
      exact (nw (s k) hsD y hy).1 (Prod.mk_le_mk.2 ⟨h0.le, he2⟩)
    refine Set.mem_biUnion (x := (k, k')) ⟨hTv x hx y hy, hTv x' hx' y' hy'⟩
      ⟨hTv x hx y hy, hh1, (F (s k) y).1, he1, ?_, ?_⟩
    · exact (Prod.le_def.1 (hF _ _ _ _ le_rfl (hyy.trans hty))).1
    · exact (Prod.le_def.1 (hF _ _ _ _ hsx le_rfl)).1
  -- lowering and raising
  let N : Finset (β × K) := hΓ.toFinset
  let lo : β × K → β × K := fun z => s z.2 ⊔ (N.filter (· ≤ z)).sup id
  let hi : β × K → β × K := fun z => t z.2 ⊓ (N.filter (z ≤ ·)).inf id
  have lo_le : ∀ z, lo z ≤ z := fun z =>
    sup_le (Prod.mk_le_mk.2 ⟨bot_le, le_rfl⟩) (Finset.sup_le fun f hf => (Finset.mem_filter.1 hf).2)
  have le_hi : ∀ z, z ≤ hi z := fun z =>
    le_inf (Prod.mk_le_mk.2 ⟨le_top, le_rfl⟩) (Finset.le_inf fun f hf => (Finset.mem_filter.1 hf).2)
  have lo_mono : ∀ z z', z ≤ z' → lo z ≤ lo z' := fun z z' h =>
    sup_le_sup (Prod.mk_le_mk.2 ⟨le_rfl, (Prod.le_def.1 h).2⟩) (Finset.sup_mono fun f hf =>
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hf).1, (Finset.mem_filter.1 hf).2.trans h⟩)
  have hi_mono : ∀ z z', z ≤ z' → hi z ≤ hi z' := fun z z' h =>
    inf_le_inf (Prod.mk_le_mk.2 ⟨le_rfl, (Prod.le_def.1 h).2⟩) (Finset.inf_mono fun f hf =>
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hf).1, h.trans (Finset.mem_filter.1 hf).2⟩)
  have le_lo : ∀ z z', z ∈ Γ → z ≤ z' → z ≤ lo z' := fun z z' hz h =>
    le_sup_of_le_right (Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hΓ.mem_toFinset.2 hz, h⟩))
  have hi_le : ∀ z z', z' ∈ Γ → z ≤ z' → hi z ≤ z' := fun z z' hz h =>
    inf_le_of_right_le (Finset.inf_le (f := id) (Finset.mem_filter.2 ⟨hΓ.mem_toFinset.2 hz, h⟩))
  let Low : β × K → β × K → Prop := fun x y =>
    ∃ x' y', x ≤ x' ∧ x' ∈ D ∧ y ≤ y' ∧ y' ∉ D ∧ F x' y' ∉ Γ ∧ y'.2 ≤ (F x' y').2
  let H : β × K → β × K → β × K := fun x y =>
    if F x y ∈ Γ then F x y else if Low x y then lo (F x y) else hi (F x y)
  have Low_down : ∀ x x' y y', x ≤ x' → y ≤ y' → Low x' y' → Low x y :=
    fun x x' y y' hxx hyy ⟨a, b, ha, haD, hb, hbD, hn, hk⟩ => ⟨a, b, hxx.trans ha, haD, hyy.trans hb, hbD, hn, hk⟩
  -- monotone on cells
  have hHm : ∀ x x' y y', x ∈ D → x' ∈ D → y ∉ D → y' ∉ D → x ≤ x' → y ≤ y' → H x y ≤ H x' y' := by
    intro x x' y y' hx hx' hy hy' hxx hyy
    have hzz := hF _ _ _ _ hxx hyy
    by_cases g1 : F x y ∈ Γ <;> by_cases g2 : F x' y' ∈ Γ
    · simp only [H, g1, g2, if_true]; exact hzz
    · simp only [H, g1, g2, if_true, if_false]
      split_ifs
      · exact le_lo _ _ g1 hzz
      · exact hzz.trans (le_hi _)
    · simp only [H, g1, g2, if_true, if_false]
      split_ifs
      · exact (lo_le _).trans hzz
      · exact hi_le _ _ g2 hzz
    · simp only [H, g1, g2, if_false]
      by_cases l2 : Low x' y'
      · have l1 := Low_down _ _ _ _ hxx hyy l2
        simp only [l1, l2, if_true]; exact lo_mono _ _ hzz
      · simp only [l2, if_false]
        split_ifs
        · exact (lo_le _).trans (hzz.trans (le_hi _))
        · exact hi_mono _ _ hzz
  -- witness-free on cells
  have nwH : ∀ x ∈ D, ∀ y, y ∉ D → ¬ H x y ≤ x ∧ ¬ y ≤ H x y := by
    intro x hx y hy
    have h0 := nw x hx y hy
    by_cases g : F x y ∈ Γ
    · simp only [H, g, if_true]; exact h0
    · simp only [H, g, if_false]
      by_cases l : Low x y
      · simp only [l, if_true]
        obtain ⟨a, b, ha, haD, hb, hbD, hn, hk⟩ := l
        have hk2 : ¬ (F x y).2 ≤ x.2 := fun h => g (corner x y a b hx hy haD hbD ha hb h hk)
        exact ⟨fun h => hk2 (Prod.le_def.1 (le_sup_left.trans h)).2, fun h => h0.2 (h.trans (lo_le _))⟩
      · simp only [l, if_false]
        have hk2 : ¬ y.2 ≤ (F x y).2 := fun h => l ⟨x, y, le_rfl, hx, le_rfl, hy, g, h⟩
        exact ⟨fun h => h0.1 ((le_hi _).trans h), fun h => hk2 (Prod.le_def.1 (h.trans inf_le_left)).2⟩
  -- finitely many values
  let Ψ : Set (β × K) := (fun p : K × Finset (β × K) => s p.1 ⊔ p.2.sup id) '' (T ×ˢ (N.powerset : Set _)) ∪
    (fun p : K × Finset (β × K) => t p.1 ⊓ p.2.inf id) '' (T ×ˢ (N.powerset : Set _))
  have hΨ : Ψ.Finite :=
    ((hT.prod (Finset.finite_toSet _)).image _).union ((hT.prod (Finset.finite_toSet _)).image _)
  have hval : ∀ x ∈ D, ∀ y, y ∉ D → H x y ∈ Γ ∪ Ψ := by
    intro x hx y hy
    by_cases g : F x y ∈ Γ
    · simp only [H, g, if_true]; exact Or.inl g
    · simp only [H, g, if_false]
      split_ifs
      · exact Or.inr (Or.inl ⟨((F x y).2, N.filter (· ≤ F x y)),
          ⟨hTv x hx y hy, Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _))⟩, rfl⟩)
      · exact Or.inr (Or.inr ⟨((F x y).2, N.filter (F x y ≤ ·)),
          ⟨hTv x hx y hy, Finset.mem_coe.2 (Finset.mem_powerset.2 (Finset.filter_subset _ _))⟩, rfl⟩)
  obtain ⟨H', hH', hHH⟩ := Strip.extend_mono H hHm
  obtain ⟨x, hx, y, hy, hw⟩ := Pin.cut_of_values_in_finite hH' hD hbot htop (Γ ∪ Ψ) (hΓ.union hΨ)
    fun _ x hx y hy => (hHH x hx y hy).symm ▸ hval x hx y hy
  rw [hHH x hx y hy] at hw
  rcases hw with h | h
  exacts [(nwH x hx y hy).1 h, (nwH x hx y hy).2 h]

/-- **Cut on `L × K`**, `L` complete with finite proper principal ideals and filters, `K` a finite complete lattice. -/
theorem cut_prod_finite [Finite K] (hI : ∀ g : β, g ≠ ⊤ → (Set.Iic g).Finite)
    (hJ : ∀ g : β, g ≠ ⊥ → (Set.Ici g).Finite) {F : β × K → β × K → β × K} {D : Set (β × K)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) : ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) :=
  cut_prod_layers hI hJ hF hD hbot htop Set.univ Set.finite_univ fun _ _ _ _ _ => trivial

end Mordor.Layers

namespace Mordor
open Layers

/-- **CL on `L × K`** for every complete `L` with finite proper principal ideals and filters (e.g. `Ω`) and every
finite complete lattice `K` (e.g. `C₄`). -/
theorem semi_of_prod_finite {β K : Type*} [CompleteLattice β] [CompleteLattice K] [Finite K]
    (hI : ∀ g : β, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : β, g ≠ ⊥ → (Set.Ici g).Finite)
    (F : β × K →o β × K →o β × K) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_prod_finite hI hJ (F := fun x y => F x y)
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x y h hy => hD h hy) (hD bot_le hd)
    (fun ht => hu (hD le_top ht))

end Mordor
