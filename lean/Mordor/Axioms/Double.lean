import Mordor.Orbit
import Mordor.Stable
import Mordor.Axioms.Source

/-!
# The equipment reading of the Cut Lemma (foundations-double §7–§8, round 26 §34.3z⁶¹)

The double-categorical framework of `docs/00-foundations-double.md` is checked here in its one model that carries
the research problem: the **equipment of a complete lattice `L`**. Horizontal arrows are monotone maps; vertical
arrows are down-set relations (profunctors into `Prop`); squares are inclusions. A monotone `f` has a *companion*
`f_* D = ↓ f(D)` and a *conjoint* `f^* D = f⁻¹(D)` on down-sets.

* `companion_conjoint`: `f_* ⊣ f^*` on down-sets (the companion–conjoint adjunction, I3).
* `step_eq`: the closure step of the Cut Lemma is `D ∪ a_* D ∪ b^* D` on down-sets, so `R(F)` is the initial algebra
  of the endo-proarrow `↓⊥ ∪ a_* ∪ b^*` (Hμ4 in the equipment).
* `yoneda_adj`: `sup ⊣ ↓` (`sSup D ≤ x ↔ D ⊆ ↓x`), the Yoneda companion pair between `L` and its down-sets.
* `mate_companion`, `mate_conjoint`: the two mates of the identity square under `sup ⊣ ↓`, i.e. the comparison
  cells between the down-set layer and the join layer, are lax (`⋁ f_* D ≤ f (⋁ D)`,
  `⋁ b^* D ≤ ⋁ {y | b y ≤ ⋁ D}`). Their sum is `Orbit.step_lax`.
* `cut_iff_representable` (DCC): **Cut for `F` iff the initial algebra `R(F) = μΘ` is representable**, i.e. a
  principal down-set `↓r`, a Yoneda image. This is the framework's representability condition, read in the
  equipment, and it is exactly the open bridge.
* `double_commutation_thin`: the draft's "double-categorical commutation theorem" in the thin model. Its Cut guard
  is the whole content, and the statement is `Source.guard`.
-/

namespace Mordor.Axioms.Double
open Set

variable {L : Type*} [CompleteLattice L]

/-- The companion of a monotone map on down-sets: the down-closure of the image. -/
def comp (f : L → L) (D : Set L) : Set L := {x | ∃ y ∈ D, x ≤ f y}

/-- The conjoint: the preimage. -/
def conj (f : L → L) (D : Set L) : Set L := {x | f x ∈ D}

theorem comp_down (f : L → L) (D : Set L) : IsDown (comp f D) :=
  fun _ _ hxy ⟨z, hz, hy⟩ => ⟨z, hz, hxy.trans hy⟩

theorem conj_down {f : L → L} (hf : Monotone f) {D : Set L} (hD : IsDown D) : IsDown (conj f D) :=
  fun _ _ hxy hy => hD (hf hxy) hy

/-- **Companion ⊣ conjoint** on down-sets. -/
theorem companion_conjoint (f : L → L) {D E : Set L} (hE : IsDown E) : comp f D ⊆ E ↔ D ⊆ conj f E :=
  ⟨fun h y hy => h ⟨y, hy, le_rfl⟩, fun h _ ⟨_, hy, hxy⟩ => hE hxy (h hy)⟩

/-- **Yoneda: `sup ⊣ ↓`.** -/
theorem yoneda_adj (D : Set L) (x : L) : sSup D ≤ x ↔ D ⊆ Iic x :=
  ⟨fun h _ hy => (le_sSup hy).trans h, fun h => sSup_le fun _ hy => h hy⟩

variable (F : L →o L →o L)

/-- **The Cut closure step is `D ∪ a_* D ∪ b^* D`** on down-sets. -/
theorem step_eq {D : Set L} (hD : IsDown D) : Mordor.step F D = D ∪ comp (a F) D ∪ conj (b F) D := by
  ext x
  constructor
  · rintro ⟨y, hxy, hy | ⟨z, hz, rfl⟩ | hb⟩
    · exact Or.inl (Or.inl (hD hxy hy))
    · exact Or.inl (Or.inr ⟨z, hz, hxy⟩)
    · exact Or.inr (conj_down (b F).monotone hD hxy hb)
  · rintro ((hx | ⟨z, hz, hxz⟩) | hb)
    · exact ⟨x, le_rfl, Or.inl hx⟩
    · exact ⟨_, hxz, Or.inr (Or.inl ⟨z, hz, rfl⟩)⟩
    · exact ⟨x, le_rfl, Or.inr (Or.inr hb)⟩

/-- **Mate of the companion square** under `sup ⊣ ↓`: lax. -/
theorem mate_companion {f : L → L} (hf : Monotone f) (D : Set L) : sSup (comp f D) ≤ f (sSup D) :=
  sSup_le fun _ ⟨_, hy, hxy⟩ => hxy.trans (hf (le_sSup hy))

/-- **Mate of the conjoint square** under `sup ⊣ ↓`: lax. -/
theorem mate_conjoint (D : Set L) : sSup (conj (b F) D) ≤ sSup {y | b F y ≤ sSup D} :=
  sSup_le_sSup fun _ hy => le_sSup hy

/-- **The bridge is a representability condition.** Under DCC, Cut for `F` holds iff `R(F)` is representable
(principal): `↓⋁R(F)` contains `R(F)` always, and equality forces `⋁R(F) ∈ R(F)`, hence `R(F) = L`
(`Stable.sSup_R_mem_iff`). -/
theorem cut_iff_representable [WellFoundedLT L] : CutMaps F ↔ ∃ r : L, R F = Iic r := by
  rw [cutMaps_iff_R]
  constructor
  · intro h; exact ⟨⊤, by rw [h]; exact (Set.Iic_top).symm⟩
  · rintro ⟨r, hr⟩
    have hmem : sSup (R F) ∈ R F := by
      rw [hr, csSup_Iic]; exact Set.self_mem_Iic
    exact (sSup_R_mem_iff (F := F)).1 hmem

/-- The draft's double-categorical commutation theorem, read in the thin model: the Cut guard and the derived law
give `m = n`. All its other hypotheses (monads, comonads, representability, tabulators) hold or are vacuous here. -/
theorem double_commutation_thin (hcut : CutMaps F) (hlaw : Source.DerivedLaw F) : m F = n F :=
  Source.guard F hcut hlaw

end Mordor.Axioms.Double
