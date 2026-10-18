import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal

/-!
# Distributive laws and bialgebras (foundations v3.8: B2, B3, I6, I7)

Two functors on one category: the **syntax** `S` (the μ-side, "the Ring") and the **behaviour** `B` (the ν-side,
"the Eye"). A (plain) distributive law is a natural transformation `λ : S ∘ B ⇒ B ∘ S`, i.e. `B ⋙ S ⟶ S ⋙ B`.
A λ-bialgebra is `S X →α X →β B X` with `α ≫ β = S β ≫ λ ≫ B α`.

This is the core of Turi–Plotkin's bialgebraic semantics, for laws of a functor over a functor (no free monad or
cofree comonad needed):
* **B3 (lifting).** The initial `S`-algebra carries a `B`-coalgebra making it a λ-bialgebra (`initBialg`); the final
  `B`-coalgebra carries an `S`-algebra making it a λ-bialgebra (`finBialg`).
* **I6 (fusion).** The comparison `c : μS → νB` is at once the anamorphism of the lifted coalgebra and the fold of
  the lifted algebra (`comparison_is_fold`), so fold and ana fuse into one arrow.
* **I7 (congruence).** `c` is an algebra map: `in ≫ c = S c ≫ α_ν` (`comparison_alg`). Behavioural equivalence
  (the kernel of `c`) is respected by every operation of the syntax: "bisimilarity is a congruence".
-/

namespace Mordor.Axioms.Law
open CategoryTheory Limits Endofunctor

universe v u
variable {C : Type u} [Category.{v} C] {S B : C ⥤ C} (law : B ⋙ S ⟶ S ⋙ B)

/-- A λ-bialgebra. -/
structure Bialg where
  X : C
  alg : S.obj X ⟶ X
  coalg : X ⟶ B.obj X
  law_eq : alg ≫ coalg = S.map coalg ≫ law.app X ≫ B.map alg

section Initial
variable {I : Algebra S} (hI : IsInitial I)

/-- The `S`-algebra on `B (μS)` whose fold lifts `μS` to a `B`-coalgebra. -/
def liftAlg (I : Algebra S) : Algebra S := ⟨B.obj I.a, law.app I.a ≫ B.map I.str⟩

/-- The lifted coalgebra on the initial algebra. -/
def initCoalg : I.a ⟶ B.obj I.a := (hI.to (liftAlg law I)).f

/-- **B3, μ-side.** The initial algebra is a λ-bialgebra. -/
def initBialg : Bialg law where
  X := I.a
  alg := I.str
  coalg := initCoalg law hI
  law_eq := by
    exact (hI.to (liftAlg law I)).h.symm

end Initial

section Final
variable {T : Coalgebra B} (hT : IsTerminal T)

/-- The `B`-coalgebra on `S (νB)` whose anamorphism lifts `νB` to an `S`-algebra. -/
def liftCoalg (T : Coalgebra B) : Coalgebra B := ⟨S.obj T.V, S.map T.str ≫ law.app T.V⟩

/-- The lifted algebra on the final coalgebra. -/
def finAlg : S.obj T.V ⟶ T.V := (hT.from (liftCoalg law T)).f

/-- **B3, ν-side.** The final coalgebra is a λ-bialgebra. -/
def finBialg : Bialg law where
  X := T.V
  alg := finAlg law hT
  coalg := T.str
  law_eq := by
    exact (hT.from (liftCoalg law T)).h.symm.trans (Category.assoc _ _ _)

end Final

section Comparison
variable {I : Algebra S} (hI : IsInitial I) {T : Coalgebra B} (hT : IsTerminal T)

/-- The initial algebra as a `B`-coalgebra. -/
def initAsCoalg : Coalgebra B := ⟨I.a, initCoalg law hI⟩

/-- The comparison `μS → νB`: the anamorphism of the lifted coalgebra. -/
def comparison : I.a ⟶ T.V := (hT.from (initAsCoalg law hI)).f

theorem comparison_coalg : initCoalg law hI ≫ B.map (comparison law hI hT) = comparison law hI hT ≫ T.str :=
  (hT.from (initAsCoalg law hI)).h

/-- **I7 (congruence).** The comparison is also an algebra map. -/
theorem comparison_alg : I.str ≫ comparison law hI hT = S.map (comparison law hI hT) ≫ finAlg law hT := by
  -- both sides are coalgebra maps from `(S μS, S β ≫ λ)` to the final coalgebra
  let src : Coalgebra B := ⟨S.obj I.a, S.map (initCoalg law hI) ≫ law.app I.a⟩
  have hin : src.str ≫ B.map I.str = I.str ≫ initCoalg law hI := by
    simpa [src, Category.assoc] using ((initBialg law hI).law_eq).symm
  let u : src ⟶ T := ⟨I.str ≫ comparison law hI hT, by
    rw [Functor.map_comp, ← Category.assoc, hin, Category.assoc, comparison_coalg, Category.assoc]⟩
  let w : src ⟶ T := ⟨S.map (comparison law hI hT) ≫ finAlg law hT, by
    have hfin := (hT.from (liftCoalg law T)).h
    have hnat := law.naturality (comparison law hI hT)
    simp only [Functor.comp_map] at hnat
    calc src.str ≫ B.map (S.map (comparison law hI hT) ≫ finAlg law hT)
        = S.map (initCoalg law hI) ≫ (law.app I.a ≫ B.map (S.map (comparison law hI hT))) ≫ B.map (finAlg law hT) := by
          simp [src, Category.assoc]
      _ = S.map (initCoalg law hI ≫ B.map (comparison law hI hT)) ≫ law.app T.V ≫ B.map (finAlg law hT) := by
          rw [← hnat]; simp [Category.assoc]
      _ = S.map (comparison law hI hT) ≫ (S.map T.str ≫ law.app T.V) ≫ B.map (finAlg law hT) := by
          rw [comparison_coalg]; simp [Category.assoc]
      _ = (S.map (comparison law hI hT) ≫ finAlg law hT) ≫ T.str := by
          exact (congrArg (S.map (comparison law hI hT) ≫ ·) hfin).trans (Category.assoc _ _ _).symm⟩
  exact congrArg Coalgebra.Hom.f (hT.hom_ext u w)

/-- **I6 (fusion).** The comparison is the fold of the lifted algebra: ana and fold agree. -/
theorem comparison_is_fold :
    comparison law hI hT = (hI.to ⟨T.V, finAlg law hT⟩).f := by
  have := hI.hom_ext (⟨comparison law hI hT, (comparison_alg law hI hT).symm⟩ : I ⟶ ⟨T.V, finAlg law hT⟩)
    (hI.to ⟨T.V, finAlg law hT⟩)
  exact congrArg Algebra.Hom.f this

end Comparison
end Mordor.Axioms.Law
