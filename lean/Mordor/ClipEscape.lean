import Mathlib.Order.Lattice
import Mathlib.Order.WellFounded

/-!
# Clipped-map escape (Lemma A1 of the nineteenth brief, log §34.3z¹⁴)

For a self-map `g` and an interval `[ℓ, u]`, put `T x = (x ⊔ g x) ⊓ u`. Under ACC a fixed point of `T` above `ℓ`
exists (`exists_fixed`), and at any fixed point `t`, either `g t ≤ t` or `g t ≰ u` (`escape`). So if no element of
`[ℓ, u]` satisfies `g x ≤ x`, the canonical fixed point escapes the interval: `g t ≰ u`. This is pure lattice theory;
it carries no information about `F` beyond the choice of `g`.
-/

namespace Mordor.ClipEscape

variable {α : Type*} [Lattice α]

/-- At a fixed point of the clipped map, `g t ≤ u` forces `g t ≤ t`. -/
theorem escape {g : α → α} {u t : α} (ht : (t ⊔ g t) ⊓ u = t) (hg : g t ≤ u) : g t ≤ t := by
  have htu : t ≤ u := ht ▸ inf_le_right
  calc g t ≤ t ⊔ g t := le_sup_right
    _ = (t ⊔ g t) ⊓ u := (inf_eq_left.mpr (sup_le htu hg)).symm
    _ = t := ht

/-- **Lemma A1.** If no element of `[ℓ, u]` satisfies `g x ≤ x`, a fixed point `t ∈ [ℓ, u]` of the clipped map has
`g t ≰ u`. -/
theorem escape_of_empty {g : α → α} {ℓ u t : α} (hlt : ℓ ≤ t) (ht : (t ⊔ g t) ⊓ u = t)
    (hempty : ∀ x, ℓ ≤ x → x ≤ u → ¬ g x ≤ x) : ¬ g t ≤ u :=
  fun hg => hempty t hlt (ht ▸ inf_le_right) (escape ht hg)

/-- Under ACC, if `g` is monotone and `ℓ ≤ u`, the clipped map has a fixed point in `[ℓ, u]`: a maximal element of
`{x ∈ [ℓ, u] | x ≤ T x}` (which contains `ℓ`). -/
theorem exists_fixed [WellFoundedGT α] {g : α → α} (hg : Monotone g) {ℓ u : α} (hlu : ℓ ≤ u) :
    ∃ t, ℓ ≤ t ∧ t ≤ u ∧ (t ⊔ g t) ⊓ u = t := by
  let T : α → α := fun x => (x ⊔ g x) ⊓ u
  have Tmono : Monotone T := fun x y h => inf_le_inf_right u (sup_le_sup h (hg h))
  obtain ⟨t, ⟨hlt, htu, htT⟩, hmax⟩ := (wellFounded_gt (α := α)).has_min
    {x | ℓ ≤ x ∧ x ≤ u ∧ x ≤ T x} ⟨ℓ, le_rfl, hlu, le_inf le_sup_left hlu⟩
  have hT : T t ∈ {x | ℓ ≤ x ∧ x ≤ u ∧ x ≤ T x} := ⟨hlt.trans htT, inf_le_right, Tmono htT⟩
  exact ⟨t, hlt, htu, (eq_of_le_of_not_lt htT (hmax _ hT)).symm⟩

end Mordor.ClipEscape
