import Mordor.Reach
import Mordor.TheoremA

/-!
# The frontier, stated formally

For a complete lattice `L` (log §23.4–§23.5, §31.1, §34.2):
* `chainFinite_of_CL` (Theorem A): if CL holds on `L` then every chain of `L` is finite.
* `semi_of_joinClosed`: if every chain of `L` is finite and `R(F)` is closed under binary joins, then
  `b ∘ a ≤ a ∘ b` forces `m = n` for that `F`; in particular commutation does.

So the standing conjecture "CL holds on every chain-finite complete lattice" follows from, and in the presence of
chain-finiteness its semi-commutation form is reduced to, one statement: **`R(F)` is join-closed for every monotone
`F` on a chain-finite complete lattice**. Everything else on both sides of the frontier is machine-checked.
-/

namespace Mordor
variable {α : Type*} [CompleteLattice α]

/-- Chain-finite ⟹ no infinite descending chain. -/
theorem wellFoundedLT_of_chainFinite (h : ∀ K : Set α, IsChain (· ≤ ·) K → K.Finite) : WellFoundedLT α := by
  rw [WellFoundedLT, isWellFounded_iff, RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun f => ?_⟩
  have hanti : StrictAnti f := fun i j hij => (f.map_rel_iff (a := j) (b := i)).2 hij
  have hchain : IsChain (· ≤ ·) (Set.range f) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    rcases le_total i j with hij | hij
    · exact Or.inr (hanti.antitone hij)
    · exact Or.inl (hanti.antitone hij)
  exact Set.infinite_range_of_injective hanti.injective (h _ hchain)

/-- Chain-finite ⟹ no infinite ascending chain. -/
theorem wellFoundedGT_of_chainFinite (h : ∀ K : Set α, IsChain (· ≤ ·) K → K.Finite) : WellFoundedGT α := by
  rw [WellFoundedGT, isWellFounded_iff, RelEmbedding.wellFounded_iff_isEmpty]
  refine ⟨fun f => ?_⟩
  have hmono : StrictMono f := fun i j hij => (f.map_rel_iff (a := j) (b := i)).2 hij
  have hchain : IsChain (· ≤ ·) (Set.range f) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ _
    rcases le_total i j with hij | hij
    · exact Or.inl (hmono.monotone hij)
    · exact Or.inr (hmono.monotone hij)
  exact Set.infinite_range_of_injective hmono.injective (h _ hchain)

/-- **The open direction, reduced.** On a chain-finite complete lattice, join-closure of `R(F)` gives semi-CL. -/
theorem semi_of_joinClosed (hfin : ∀ K : Set α, IsChain (· ≤ ·) K → K.Finite) (F : α →o α →o α)
    (hj : ∀ x ∈ R F, ∀ y ∈ R F, x ⊔ y ∈ R F) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  haveI := wellFoundedGT_of_chainFinite hfin
  haveI := wellFoundedLT_of_chainFinite hfin
  exact semi_of_cut ((cutMaps_iff_joinClosed (F := F)).mpr hj) hsemi

/-- **The frontier.** CL on `L` forces chain-finiteness (Theorem A); conversely, on a chain-finite `L`,
join-closure of every `R(F)` gives CL. -/
theorem frontier :
    ((∀ F : α →o α →o α, (∀ x, a F (b F x) = b F (a F x)) → m F = n F) →
        ∀ K : Set α, IsChain (· ≤ ·) K → K.Finite) ∧
    ((∀ K : Set α, IsChain (· ≤ ·) K → K.Finite) →
        (∀ F : α →o α →o α, ∀ x ∈ R F, ∀ y ∈ R F, x ⊔ y ∈ R F) →
        ∀ F : α →o α →o α, (∀ x, a F (b F x) = b F (a F x)) → m F = n F) :=
  ⟨fun hCL => chainFinite_of_CL hCL,
   fun hfin hj F hc => semi_of_joinClosed hfin F (hj F) fun x => (hc x).ge⟩

end Mordor
