import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.CategoryTheory.Types.Basic

/-!
# The axioms in an arbitrary category (foundations v3.7, §2–§3)

The categorical rows that Mathlib's `Endofunctor.Algebra` / `Coalgebra` support, derived for any category `C` and
endofunctor `F` (no M0, no cartesian closure: these rows need only an initial algebra or a terminal coalgebra to
exist). Dialgebras are defined here (`Dialg F G`), with the reduction Bd9 and the degeneracy D6.

* μ1 / ν1: Lambek. μ2 / ν2: fold / ana (existence and uniqueness). μ3: a sub-algebra of the initial algebra is
  all of it. ν3: coalgebra maps into the final coalgebra agree on any span, so bisimilar states are equal.
* B1 is **false** in general: `b1_false` (in `Type`, `F X = X ⊕ X`, `X = 1`).
* D3: dialgebraic induction. D6, Bd9.
-/

namespace Mordor.Axioms.Cat
open CategoryTheory Limits Endofunctor

universe v u
variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

/-! ## μ-axioms -/

/-- **μ1 (Lambek).** -/
theorem mu1 {I : Algebra F} (h : IsInitial I) : IsIso I.str := Algebra.Initial.str_isIso h

/-- **μ2 (Fold).** -/
theorem mu2 {I : Algebra F} (h : IsInitial I) (A : Algebra F) :
    ∃! g : I.a ⟶ A.a, F.map g ≫ A.str = I.str ≫ g :=
  ⟨(h.to A).f, (h.to A).h, fun g hg => congrArg Algebra.Hom.f (h.hom_ext ⟨g, hg⟩ (h.to A))⟩

/-- **μ3 (Induction).** A sub-algebra `U ↣ μF` (an algebra map whose carrier map is mono) is an isomorphism. -/
theorem mu3 {I U : Algebra F} (h : IsInitial I) (m : U ⟶ I) [Mono m.f] : IsIso m := by
  haveI : Mono m := Algebra.mono_of_mono m
  have h1 : h.to U ≫ m = 𝟙 I := h.hom_ext _ _
  refine ⟨⟨h.to U, ?_, h1⟩⟩
  rw [← cancel_mono m, Category.assoc, h1, Category.comp_id, Category.id_comp]

/-! ## ν-axioms -/

/-- **ν1 (Lambek).** -/
theorem nu1 {T : Coalgebra F} (h : IsTerminal T) : IsIso T.str := Coalgebra.Terminal.str_isIso h

/-- **ν2 (Ana).** -/
theorem nu2 {T : Coalgebra F} (h : IsTerminal T) (V : Coalgebra F) :
    ∃! g : V.V ⟶ T.V, V.str ≫ F.map g = g ≫ T.str :=
  ⟨(h.from V).f, (h.from V).h, fun g hg => congrArg Coalgebra.Hom.f (h.hom_ext ⟨g, hg⟩ (h.from V))⟩

/-- **ν3 (Coinduction).** For a bisimulation `R` (a coalgebra with coalgebra-map projections `p q` into `X`),
the two composites into the final coalgebra agree: bisimilar ⇒ equal. -/
theorem nu3 {T R X : Coalgebra F} (h : IsTerminal T) (p q : R ⟶ X) (k : X ⟶ T) : p ≫ k = q ≫ k :=
  h.hom_ext _ _

/-! ## B1 is false in general -/

/-- `X ↦ X ⊕ X` on `Type`. -/
def dbl : Type u ⥤ Type u where
  obj X := X ⊕ X
  map f := Sum.map f f
  map_id _ := by funext x; cases x <;> rfl
  map_comp _ _ := by funext x; cases x <;> rfl

/-- **B1 is false.** On `X = 1` with `F X = X ⊕ X`, the coalgebra `c = inl` and the algebra `a = !` satisfy
`a ∘ c = id`, but `c` is not an isomorphism. -/
theorem b1_false : ∃ (X : Type u) (a : dbl.obj X ⟶ X) (c : X ⟶ dbl.obj X), c ≫ a = 𝟙 X ∧ ¬ IsIso c := by
  refine ⟨PUnit, fun _ => PUnit.unit, Sum.inl, rfl, fun hc => ?_⟩
  obtain ⟨x, hx⟩ := ((isIso_iff_bijective _).mp hc).2 (Sum.inr PUnit.unit)
  cases hx

/-! ## Dialgebras -/

/-- An `(F, G)`-dialgebra: a carrier with a structure map `F X ⟶ G X`. -/
structure Dialg (F G : C ⥤ C) where
  carrier : C
  str : F.obj carrier ⟶ G.obj carrier

namespace Dialg
variable {G : C ⥤ C}

/-- Dialgebra morphisms. -/
@[ext] structure Hom (A B : Dialg F G) where
  f : A.carrier ⟶ B.carrier
  h : F.map f ≫ B.str = A.str ≫ G.map f := by cat_disch

attribute [reassoc (attr := simp)] Hom.h

instance : Category (Dialg F G) where
  Hom := Hom
  id A := ⟨𝟙 _, by simp⟩
  comp u w := ⟨u.f ≫ w.f, by simp⟩

@[ext] theorem hom_ext {A B : Dialg F G} {u w : A ⟶ B} (h : u.f = w.f) : u = w := Hom.ext h
@[simp] theorem id_f (A : Dialg F G) : (𝟙 A : A ⟶ A).f = 𝟙 _ := rfl
@[simp] theorem comp_f {A B D : Dialg F G} (u : A ⟶ B) (w : B ⟶ D) : (u ≫ w).f = u.f ≫ w.f := rfl

/-- **D3 (Dialgebraic induction).** A sub-dialgebra of the initial dialgebra is all of it. -/
theorem d3 {I U : Dialg F G} (h : IsInitial I) (m : U ⟶ I) [Mono m] : IsIso m := by
  have h1 : h.to U ≫ m = 𝟙 I := h.hom_ext _ _
  refine ⟨⟨h.to U, ?_, h1⟩⟩
  rw [← cancel_mono m, Category.assoc, h1, Category.comp_id, Category.id_comp]

/-- **Bd9 (Reduction).** `(F, Id)`-dialgebras are `F`-algebras. -/
def toAlgebra : Dialg F (𝟭 C) ⥤ Algebra F where
  obj A := ⟨A.carrier, A.str⟩
  map u := ⟨u.f, u.h⟩

def ofAlgebra : Algebra F ⥤ Dialg F (𝟭 C) where
  obj A := ⟨A.a, A.str⟩
  map u := ⟨u.f, u.h⟩

/-- **Bd9.** The two categories are isomorphic, so `μ^{F,Id} = μF` (initial objects correspond). -/
def bd9 : Dialg F (𝟭 C) ≌ Algebra F where
  functor := toAlgebra
  inverse := ofAlgebra
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext; simp [toAlgebra, ofAlgebra])
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; ext; simp [toAlgebra, ofAlgebra])

/-- An initial `(F, Id)`-dialgebra is an initial `F`-algebra. -/
def bd9_initial {I : Dialg F (𝟭 C)} (h : IsInitial I) : IsInitial (toAlgebra.obj I) :=
  IsInitial.ofUniqueHom (fun B => toAlgebra.map (h.to (ofAlgebra.obj B)))
    (fun B u => Algebra.Hom.ext (congrArg Hom.f
      (h.hom_ext (⟨u.f, u.h⟩ : I ⟶ ofAlgebra.obj B) (h.to (ofAlgebra.obj B)))))

/-- **D6 (Degeneracy).** If `C` has an initial object `⊥`, then `(⊥, 𝟙)` is the initial `(Id, Id)`-dialgebra. -/
def d6 {Z : C} (hZ : IsInitial Z) : IsInitial (⟨Z, 𝟙 Z⟩ : Dialg (𝟭 C) (𝟭 C)) :=
  IsInitial.ofUniqueHom (fun B => ⟨hZ.to B.carrier, hZ.hom_ext _ _⟩) (fun _ _ => hom_ext (hZ.hom_ext _ _))

/-- **D6, dual.** A terminal object `⊤` gives the final `(Id, Id)`-dialgebra `(⊤, 𝟙)`. -/
def d6' {Z : C} (hZ : IsTerminal Z) : IsTerminal (⟨Z, 𝟙 Z⟩ : Dialg (𝟭 C) (𝟭 C)) :=
  IsTerminal.ofUniqueHom (fun B => ⟨hZ.from B.carrier, hZ.hom_ext _ _⟩) (fun _ _ => hom_ext (hZ.hom_ext _ _))

/-- **D5 (Duality), the object part.** The initial `(F, G)`-dialgebra on `C` is the final `(Gᵒᵖ, Fᵒᵖ)`-dialgebra
on `Cᵒᵖ`: `μ^{F,G}` on `C` is `ν^{G,F}` on `Cᵒᵖ`. -/
def d5 {I : Dialg F G} (h : IsInitial I) : IsTerminal (⟨Opposite.op I.carrier, I.str.op⟩ : Dialg G.op F.op) :=
  IsTerminal.ofUniqueHom
    (fun B => ⟨(h.to ⟨B.carrier.unop, B.str.unop⟩).f.op, Quiver.Hom.unop_inj (by
      simpa using ((h.to ⟨B.carrier.unop, B.str.unop⟩).h).symm)⟩)
    (fun B u => by
      have hu : F.map u.f.unop ≫ (⟨B.carrier.unop, B.str.unop⟩ : Dialg F G).str = I.str ≫ G.map u.f.unop :=
        Quiver.Hom.op_inj (by simpa using u.h.symm)
      exact hom_ext (Quiver.Hom.unop_inj (congrArg Hom.f
        (h.hom_ext (⟨u.f.unop, hu⟩ : I ⟶ ⟨B.carrier.unop, B.str.unop⟩) (h.to _)))))

/-- **D1, transposition (Cond).** If `G` has a left adjoint `L`, an `(F, G)`-dialgebra is an `(F ⋙ L)`-algebra:
`F X ⟶ G X` corresponds to `L (F X) ⟶ X`. Hence initial objects correspond and `μ^{F,G} = μ(L ∘ F)`. -/
def transpose {L : C ⥤ C} (adj : L ⊣ G) : Dialg F G ⥤ Algebra (F ⋙ L) where
  obj A := ⟨A.carrier, (adj.homEquiv _ _).symm A.str⟩
  map {A B} u := ⟨u.f, by
    change L.map (F.map u.f) ≫ (adj.homEquiv _ _).symm B.str = (adj.homEquiv _ _).symm A.str ≫ u.f
    rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm, u.h]⟩

def untranspose {L : C ⥤ C} (adj : L ⊣ G) : Algebra (F ⋙ L) ⥤ Dialg F G where
  obj A := ⟨A.a, adj.homEquiv _ _ A.str⟩
  map {A B} u := ⟨u.f, by
    rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
    exact congrArg _ u.h⟩

def d1 {L : C ⥤ C} (adj : L ⊣ G) : Dialg F G ≌ Algebra (F ⋙ L) where
  functor := transpose adj
  inverse := untranspose adj
  unitIso := NatIso.ofComponents (fun A => ⟨⟨𝟙 _, by simp [untranspose, transpose]⟩, ⟨𝟙 _, by simp [untranspose, transpose]⟩,
    by ext; simp, by ext; simp⟩) (by intros; ext; simp [untranspose, transpose])
  counitIso := NatIso.ofComponents (fun A => Algebra.isoMk (Iso.refl _) (by simp [untranspose, transpose]))
    (by intros; ext; simp [untranspose, transpose])

end Dialg
end Mordor.Axioms.Cat
