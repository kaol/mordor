import Mordor.Cut
import Mordor.Duality
import Mordor.RelativeCut
import Mordor.FinGenAll
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.Zorn

/-!
# Duality transport, straddling subalgebras, commuting retractions (round 26, §34.3z⁵⁶–⁵⁷)

Response to an outside strategy brief (S4, S5).

* **`cutCells_dual`, `cutCells_of_dual`, `cutCells_dual_iff`.** `CutCells F ↔ CutCells Fᵈ` on any complete lattice,
  `Fᵈ x y = F y x` read in `αᵒᵈ` (`Duality.dualF`). The cut is complemented and the two witness disjuncts swap.
  Any one-sided Cut theorem therefore yields its order dual by one application (S4).
* **`cut_of_straddle`.** In any partial order, a finite set `K` closed under `F`, with a least element in `D` and a
  greatest element outside `D`, contains a witness for `D` (`cut_finite` on `K`). No lattice structure, and `⊥, ⊤`
  need not lie in `K`; `Stable.cutCells_of_finite_Fclosure` is the case `⊥, ⊤ ∈ K`.
* **`commuting_retraction`.** Every monotone `F` on a complete lattice admits an idempotent monotone `r` with finite
  (one-point) image and `r (F x y) = F (r x) (r y)`: the constant map at a fixed point of `x ↦ F x x`. So "a
  commuting retraction onto a finite subposet forces Cut" (the brief's S5) would imply Cut for every `F`; it is the
  whole conjecture, not a reduction.
* **`cut_of_retraction`.** What a commuting retraction does give: a witness for every cut separating `r ⊥` from
  `r ⊤` (`cut_of_straddle` on the image). Idempotence is not needed.
-/

namespace Mordor
open OrderDual

section Dual
variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

theorem cutCells_dual (h : CutCells F) : CutCells (dualF F) := by
  intro D' hD' ⟨d, hd⟩ ⟨u, hu⟩
  obtain ⟨x, hx, y, hy, hw⟩ := h {z | toDual z ∉ D'}
    (fun a b hab hb ha => hb (hD' (show toDual b ≤ toDual a from hab) ha)) ⟨ofDual u, hu⟩
    ⟨ofDual d, fun h' => h' hd⟩
  refine ⟨toDual y, not_not.mp hy, toDual x, hx, ?_⟩
  rcases hw with hw | hw
  · exact Or.inr (show toDual x ≤ toDual (F x y) from hw)
  · exact Or.inl (show toDual (F x y) ≤ toDual y from hw)

theorem cutCells_of_dual (h : CutCells (dualF F)) : CutCells F := by
  intro D hD ⟨d, hd⟩ ⟨u, hu⟩
  obtain ⟨x, hx, y, hy, hw⟩ := h {z : αᵒᵈ | ofDual z ∉ D}
    (fun a b hab hb ha => hb (hD (show ofDual b ≤ ofDual a from hab) ha)) ⟨toDual u, hu⟩
    ⟨toDual d, fun h' => h' hd⟩
  refine ⟨ofDual y, not_not.mp hy, ofDual x, hx, ?_⟩
  rcases hw with hw | hw
  · exact Or.inr (show ofDual x ≤ F (ofDual y) (ofDual x) from hw)
  · exact Or.inl (show F (ofDual y) (ofDual x) ≤ ofDual y from hw)

theorem cutCells_dual_iff : CutCells (dualF F) ↔ CutCells F := ⟨cutCells_of_dual, cutCells_dual⟩

end Dual

/-- **A finite `F`-subalgebra with bounds that straddles a cut contains a witness.** -/
theorem cut_of_straddle {α : Type*} [PartialOrder α] (F : α → α → α) (D : Set α)
    (hD : ∀ a b, a ≤ b → b ∈ D → a ∈ D) (K : Set α) (hK : K.Finite)
    (hFK : ∀ x ∈ K, ∀ y ∈ K, F x y ∈ K) (hF : ∀ x ∈ K, ∀ x' ∈ K, ∀ y ∈ K, ∀ y' ∈ K, x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {k₀ k₁ : α} (h₀ : k₀ ∈ K) (h₁ : k₁ ∈ K) (hl : ∀ x ∈ K, k₀ ≤ x) (hu : ∀ x ∈ K, x ≤ k₁)
    (hk₀ : k₀ ∈ D) (hk₁ : k₁ ∉ D) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  haveI : Finite K := hK.to_subtype
  letI : Fintype K := Fintype.ofFinite K
  letI : BoundedOrder K :=
    { top := ⟨k₁, h₁⟩, le_top := fun a => hu a.1 a.2, bot := ⟨k₀, h₀⟩, bot_le := fun a => hl a.1 a.2 }
  obtain ⟨x, hx, y, hy, hw⟩ := RelativeCut.cut_finite (α := K) {z | z.1 ∈ D}
    (fun a b hab hb => hD a.1 b.1 hab hb) hk₁ hk₀ (fun x y => ⟨F x y, hFK x.1 x.2 y.1 y.2⟩)
    (fun a a' b b' ha hb => hF a.1 a.2 a'.1 a'.2 b.1 b.2 b'.1 b'.2 ha hb)
  exact ⟨x.1, hx, y.1, hy, hw⟩

section Retraction
variable {α : Type*} [CompleteLattice α] (F : α →o α →o α)

/-- The diagonal `x ↦ F x x`. -/
def diagMap : α →o α := ⟨fun x => F x x, fun _ _ h => (F.mono h _).trans ((F _).mono h)⟩

/-- **Every `F` has a commuting retraction with finite image.** -/
theorem commuting_retraction :
    ∃ r : α →o α, (∀ x, r (r x) = r x) ∧ (Set.range r).Finite ∧ ∀ x y, r (F x y) = F (r x) (r y) := by
  let c := OrderHom.lfp (diagMap F)
  have hc : F c c = c := OrderHom.map_lfp (diagMap F)
  refine ⟨OrderHom.const α c, fun _ => rfl, ?_, fun _ _ => hc.symm⟩
  exact (Set.finite_singleton c).subset (by rintro _ ⟨_, rfl⟩; rfl)

/-- **What a commuting retraction gives**: a witness for every cut separating `r ⊥` from `r ⊤`. -/
theorem cut_of_retraction (r : α →o α) (hr : (Set.range r).Finite) (hrF : ∀ x y, r (F x y) = F (r x) (r y))
    (D : Set α) (hD : IsDown D) (h₀ : r ⊥ ∈ D) (h₁ : r ⊤ ∉ D) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y :=
  cut_of_straddle (fun x y => F x y) D (fun a b h hb => hD h hb) (Set.range r) hr
    (by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨F a b, hrF a b⟩)
    (fun x _ x' _ y _ y' _ hx hy => (F.mono hx _).trans ((F x').mono hy))
    ⟨⊥, rfl⟩ ⟨⊤, rfl⟩ (by rintro _ ⟨a, rfl⟩; exact r.mono bot_le) (by rintro _ ⟨a, rfl⟩; exact r.mono le_top) h₀ h₁

end Retraction
end Mordor

/-! ### Round 26, §34.3z⁵⁷: the skeleton-grid witness, and chain-finite + finite width ⟹ finite -/

namespace Mordor

/-- **Every finitely generated cut has a witness on the skeleton grid**: a cell `(⋀ p_A, ⋁ u_B)` for nonempty sets
of generators `A` of `D` and `B` of its complement, with `F` below the meet or above the join. This is what
`FinGen.captured` proves; `cut_fingen` forgets the location. So "every witness set meets the skeleton grid" is a
theorem on every finite lattice. -/
theorem grid_witness {α : Type*} [Lattice α] [BoundedOrder α] {k l : ℕ} {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set α}
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) {p : Fin k → α} {u : Fin l → α}
    (hpD : ∀ i, p i ∈ D) (huD : ∀ j, u j ∉ D) (hgD : ∀ x ∈ D, ∃ i, x ≤ p i) (hgU : ∀ y, y ∉ D → ∃ j, u j ≤ y)
    (hk : 0 < k) (hl : 0 < l) :
    ∃ A : Finset (Fin k), ∃ B : Finset (Fin l), A.Nonempty ∧ B.Nonempty ∧ A.inf p ∈ D ∧ B.sup u ∉ D ∧
      (F (A.inf p) (B.sup u) ≤ A.inf p ∨ B.sup u ≤ F (A.inf p) (B.sup u)) := by
  by_contra hno
  push_neg at hno
  have hA : ∀ A : Finset (Fin k), A.Nonempty → A.inf p ∈ D := fun A ⟨i, hi⟩ => hD _ _ (Finset.inf_le hi) (hpD i)
  have hB : ∀ B : Finset (Fin l), B.Nonempty → B.sup u ∉ D := fun B ⟨j, hj⟩ h =>
    huD j (hD _ _ (Finset.le_sup hj) h)
  exact FinGen.captured hk hl hF (fun A B _ _ h => hgD _ h) (fun A B _ _ h => hgU _ h)
    (fun A B hA' hB' h => (hno A B hA' hB' (hA A hA') (hB B hB')).1 (Finset.le_inf h))
    (fun A B hA' hB' h => (hno A B hA' hB' (hA A hA') (hB B hB')).2 (Finset.sup_le h))

/-- **Chain-finite and of finite width ⟹ finite** (Ramsey for sequences: an infinite poset has an infinite chain or an
infinite antichain). So a hypothesis "chain-finite + finite width" only describes finite lattices, where Cut is
`cut_finite`. -/
theorem finite_of_chainFinite_finite_width {α : Type*} [PartialOrder α] [WellFoundedLT α] [WellFoundedGT α]
    (hw : ∀ s : Set α, IsAntichain (· ≤ ·) s → s.Finite) : Finite α := by
  by_contra hfin
  rw [not_finite_iff_infinite] at hfin
  haveI : IsTrans α (· < ·) := ⟨fun _ _ _ => lt_trans⟩
  haveI : IsTrans α (· > ·) := ⟨fun _ _ _ h h' => lt_trans h' h⟩
  let f : ℕ → α := Infinite.natEmbedding α
  have hf : Function.Injective f := (Infinite.natEmbedding α).injective
  obtain ⟨g₁, h₁ | h₁⟩ := exists_increasing_or_nonincreasing_subseq (· < ·) f
  · obtain ⟨x, ⟨n, rfl⟩, hmax⟩ := (wellFounded_gt (α := α)).has_min (Set.range fun n => f (g₁ n)) ⟨_, ⟨0, rfl⟩⟩
    exact hmax _ ⟨n + 1, rfl⟩ (h₁ n (n + 1) (Nat.lt_succ_self n))
  obtain ⟨g₂, h₂ | h₂⟩ := exists_increasing_or_nonincreasing_subseq (· > ·) fun n => f (g₁ n)
  · obtain ⟨x, ⟨n, rfl⟩, hmin⟩ := (wellFounded_lt (α := α)).has_min (Set.range fun n => f (g₁ (g₂ n))) ⟨_, ⟨0, rfl⟩⟩
    exact hmin _ ⟨n + 1, rfl⟩ (h₂ n (n + 1) (Nat.lt_succ_self n))
  let h : ℕ → α := fun n => f (g₁ (g₂ n))
  have hinj : Function.Injective h := hf.comp (g₁.injective.comp g₂.injective)
  refine Set.infinite_range_of_injective hinj (hw _ ?_)
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ hne hle
  have hmn : m ≠ n := fun e => hne (congrArg h e)
  have hlt : h m < h n := lt_of_le_of_ne hle hne
  rcases lt_or_gt_of_ne hmn with hmn | hmn
  · exact h₁ _ _ (g₂.strictMono hmn) hlt
  · exact h₂ _ _ hmn hlt

end Mordor

/-! ### Maximal witness-free cuts (the brief's Zorn route) -/

namespace Mordor
variable {α : Type*} [PartialOrder α] [BoundedOrder α]

/-- A witness-free cut: a down-set containing `⊥`, missing `⊤`, with no witness cell. -/
def WFCut (F : α → α → α) (D : Set α) : Prop :=
  (∀ x y, x ≤ y → y ∈ D → x ∈ D) ∧ ⊥ ∈ D ∧ ⊤ ∉ D ∧ ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y

/-- **Every witness-free cut extends to a maximal one** (unions of chains of witness-free cuts are witness-free). -/
theorem exists_maximal_WFCut {F : α → α → α} {D : Set α} (h : WFCut F D) :
    ∃ M, D ⊆ M ∧ Maximal (WFCut F) M := by
  obtain ⟨M, hDM, hM⟩ := zorn_subset_nonempty {M | WFCut F M} (fun c hc _ ⟨M₀, hM₀⟩ => by
    refine ⟨⋃₀ c, ⟨?_, ⟨M₀, hM₀, (hc hM₀).2.1⟩, ?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro x y hxy ⟨M, hM, hy⟩; exact ⟨M, hM, (hc hM).1 x y hxy hy⟩
    · rintro ⟨M, hM, ht⟩; exact (hc hM).2.2.1 ht
    · rintro x ⟨M, hM, hx⟩ y hy
      exact (hc hM).2.2.2 x hx y fun h' => hy ⟨M, hM, h'⟩) D h
  exact ⟨M, hDM, hM⟩

/-- **The growth obstruction at a maximal cut lives on the complement.** If `M` is a maximal witness-free cut and
`u ∉ M` is minimal outside `M` (and `M ∪ {u} ≠ L`), then some `y ∉ M`, `y ≠ u`, has `F u y ≤ u` or `y ≤ F u y`.
Both cells `(u, y)` lie in `Mᶜ × Mᶜ`, where the cut condition never looks: the normal form of §34.3z⁴² sets `F` to
`⊤` there without changing witness-freeness, and then `y ≤ F u y` holds for every `y`. So maximality yields no
constraint on cross values. -/
theorem maximal_WFCut_row {F : α → α → α} {M : Set α} (hM : Maximal (WFCut F) M) {u : α} (hu : u ∉ M)
    (hmin : ∀ v, v < u → v ∈ M) (hne : ∃ w, w ∉ M ∧ w ≠ u) :
    ∃ y, y ∉ M ∧ y ≠ u ∧ (F u y ≤ u ∨ y ≤ F u y) := by
  obtain ⟨hD, hb, ht, hnw⟩ := hM.1
  by_contra hno
  push_neg at hno
  have hdown : ∀ x y, x ≤ y → y ∈ insert u M → x ∈ insert u M := by
    rintro x y hxy (rfl | hy)
    · rcases eq_or_lt_of_le hxy with rfl | hlt
      · exact Set.mem_insert _ _
      · exact Or.inr (hmin x hlt)
    · exact Or.inr (hD x y hxy hy)
  have htop : ⊤ ∉ insert u M := by
    rintro (htu | htM)
    · obtain ⟨w, hw, hwu⟩ := hne
      subst htu
      exact hw (hmin w (lt_of_le_of_ne le_top hwu))
    · exact ht htM
  have hwf : WFCut F (insert u M) := by
    refine ⟨hdown, Or.inr hb, htop, ?_⟩
    rintro x (rfl | hx) y hy
    · have hyM : y ∉ M := fun h => hy (Or.inr h)
      have hyu : y ≠ x := fun h => hy (h ▸ Set.mem_insert _ _)
      exact ⟨fun h => (hno y hyM hyu).1 h, fun h => (hno y hyM hyu).2 h⟩
    · exact hnw x hx y fun h => hy (Or.inr h)
  exact hu (hM.2 hwf (Set.subset_insert u M) (Set.mem_insert u M))

end Mordor

/-! ### The "paired normal form": the block `Dᶜ × D` is free -/

namespace Mordor
variable {α : Type*} [PartialOrder α] [BoundedOrder α]

open Classical in
/-- The other normal form: `⊥` on `L × D`, `F` on `D × Dᶜ`, `⊤` on `Dᶜ × Dᶜ`. `Stable.normalize` instead puts `⊤` on
all of `Dᶜ × L`. The two differ exactly on the block `Dᶜ × D`, which contains `(⊤, ⊥)`. -/
noncomputable def normalizeLow (F : α → α → α) (D : Set α) (x y : α) : α :=
  if y ∈ D then ⊥ else if x ∈ D then F x y else ⊤

theorem normalizeLow_mono {F : α → α → α} {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') :
    ∀ x x' y y', x ≤ x' → y ≤ y' → normalizeLow F D x y ≤ normalizeLow F D x' y' := by
  intro x x' y y' hx hy
  unfold normalizeLow
  by_cases hy0 : y ∈ D
  · rw [if_pos hy0]; exact bot_le
  have hy1 : y' ∉ D := fun h => hy0 (hD y y' hy h)
  rw [if_neg hy0, if_neg hy1]
  by_cases hx1 : x' ∈ D
  · rw [if_pos (hD x x' hx hx1), if_pos hx1]; exact hF _ _ _ _ hx hy
  · rw [if_neg hx1]; exact le_top

/-- Cross values are unchanged, so witness-freeness is too; the value at `(⊤, ⊥)` is `⊥` here and `⊤` in
`Stable.normalize`. No constraint on `F (⊤, ⊥)` can follow from the cut problem. -/
theorem normalizeLow_cross {F : α → α → α} {D : Set α} {x y : α} (hx : x ∈ D) (hy : y ∉ D) :
    normalizeLow F D x y = F x y := by
  simp [normalizeLow, hx, hy]

theorem normalizeLow_top_bot {F : α → α → α} {D : Set α} (hb : ⊥ ∈ D) : normalizeLow F D ⊤ ⊥ = ⊥ := by
  simp [normalizeLow, hb]

end Mordor
