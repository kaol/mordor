import Mordor.Cut
import Mordor.Duality
import Mordor.RelativeCut

/-!
# Duality transport, straddling subalgebras, commuting retractions (round 26, §34.3z⁵⁶)

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
