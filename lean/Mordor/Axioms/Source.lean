import Mordor.Cut
import Mordor.Continuous

/-!
# Sharpened axioms from the source (foundations v3.8, `docs/02-the-source.md`)

Thin model throughout (a complete lattice). Each block makes one vague row of the foundations precise.

* **B2 (one functor).** The free monad of `f` is the closure `T x = μY. x ⊔ f Y`, the cofree comonad the interior
  `D x = νY. x ⊓ f Y`. A distributive law `T ∘ D ⇒ D ∘ T` always exists (`dist_law`), and its bialgebras are exactly
  the fixed points of `f` (`bialg_iff`), with initial one `μf` and final one `νf`. So for a single functor B2 is
  automatic and carries no content: the content of the framework lives in the bifunctor.
* **B2 / I11 (bifunctor).** The derived distributive law is `λ : b ∘ a ⇒ a ∘ b` (pointwise `b (a x) ≤ a (b x)`).
  I11 ("an invertible law collapses the layers") is then exactly CL, and "a law collapses the layers" is semi-CL.
  The **guard** that makes the collapse sound is the Cut Lemma (`guard`); without it the collapse fails, even under
  M0 (`i11_false`).
* **The One Ring.** An object initial and final at once among the bi-fixed points `Fix a ∩ Fix b` exists iff
  `m = n` (`one_ring`).
* **I3 (μ inside ν).** For `g ≤ f`, `μg ≤ ν(a ⊔ f)` (`i3`).
-/

namespace Mordor.Axioms.Source

/-! ## B2 for one functor: the canonical law between closure and interior -/

section One
variable {L : Type*} [CompleteLattice L] (f : L →o L)

/-- The step `Y ↦ x ⊔ f Y` of the free monad. -/
def tStep (x : L) : L →o L := ⟨fun Y => x ⊔ f Y, fun _ _ h => sup_le_sup_left (f.mono h) x⟩
/-- The step `Y ↦ x ⊓ f Y` of the cofree comonad. -/
def dStep (x : L) : L →o L := ⟨fun Y => x ⊓ f Y, fun _ _ h => inf_le_inf_left x (f.mono h)⟩

/-- The free monad of `f` (thin): the least `f`-algebra above `x`. -/
def T (x : L) : L := (tStep f x).lfp
/-- The cofree comonad of `f` (thin): the greatest `f`-coalgebra below `x`. -/
def D (x : L) : L := (dStep f x).gfp

theorem T_eq (x : L) : x ⊔ f (T f x) = T f x := (tStep f x).map_lfp
theorem D_eq (x : L) : x ⊓ f (D f x) = D f x := (dStep f x).map_gfp
theorem le_T (x : L) : x ≤ T f x := le_sup_left.trans (T_eq f x).le
theorem f_T_le (x : L) : f (T f x) ≤ T f x := le_sup_right.trans (T_eq f x).le
theorem D_le (x : L) : D f x ≤ x := (D_eq f x).ge.trans inf_le_left
theorem D_le_f (x : L) : D f x ≤ f (D f x) := (D_eq f x).ge.trans inf_le_right
/-- Freeness: `T x` lies below every algebra above `x`. -/
theorem T_le {x y : L} (hx : x ≤ y) (hy : f y ≤ y) : T f x ≤ y := (tStep f x).lfp_le (sup_le hx hy)
/-- Cofreeness: `D x` lies above every coalgebra below `x`. -/
theorem le_D {x y : L} (hx : y ≤ x) (hy : y ≤ f y) : y ≤ D f x := (dStep f x).le_gfp (le_inf hx hy)

/-- **B2, thin, one functor: the distributive law `T ∘ D ⇒ D ∘ T` exists.** -/
theorem dist_law (x : L) : T f (D f x) ≤ D f (T f x) := by
  refine le_D f (T_le f ((D_le f x).trans (le_T f x)) (f_T_le f x)) ?_
  calc T f (D f x) = D f x ⊔ f (T f (D f x)) := (T_eq f _).symm
    _ ≤ f (T f (D f x)) := sup_le ((D_le_f f x).trans (f.mono (le_T f _))) le_rfl

/-- **The λ-bialgebras are the fixed points** (B1's "balanced" objects). -/
theorem bialg_iff (x : L) : (T f x ≤ x ∧ x ≤ D f x) ↔ f x = x := by
  constructor
  · rintro ⟨h1, h2⟩
    exact le_antisymm ((f.mono (le_T f x)).trans ((f_T_le f x).trans h1))
      (h2.trans ((D_le_f f x).trans (f.mono (D_le f x))))
  · intro h; exact ⟨T_le f le_rfl h.le, le_D f le_rfl h.ge⟩

theorem T_bot : T f ⊥ = f.lfp := by
  have : tStep f ⊥ = f := by ext; simp [tStep]
  simp [T, this]
theorem D_top : D f ⊤ = f.gfp := by
  have : dStep f ⊤ = f := by ext; simp [dStep]
  simp [D, this]

/-- **The One Ring, one functor.** The initial bialgebra `μf` is also final iff `f` has one fixed point. -/
theorem one_ring_one : f.lfp = f.gfp ↔ ∃! x, f x = x := by
  constructor
  · intro h; refine ⟨f.lfp, f.map_lfp, fun y hy => le_antisymm (h ▸ f.le_gfp hy.ge) (f.lfp_le hy.le)⟩
  · rintro ⟨x, _, hu⟩; rw [hu _ f.map_lfp, hu _ f.map_gfp]

/-- **I3 (μ inside ν), thin.** For a sub-functor `g ≤ f`, `μg ≤ νY. a ⊔ f Y`. -/
theorem i3 (g : L →o L) (hg : ∀ x, g x ≤ f x) (a : L) : g.lfp ≤ (tStep f a).gfp := by
  have h1 : g.lfp ≤ f.lfp := g.lfp_le ((hg _).trans f.map_lfp.le)
  have h2 : f.gfp ≤ (tStep f a).gfp := (tStep f a).le_gfp (f.map_gfp.ge.trans le_sup_right)
  exact h1.trans (f.lfp_le_gfp.trans h2)

end One

/-! ## B2 and I11 for the bifunctor: the derived law, the guard, the One Ring -/

section Bi
variable {L : Type*} [CompleteLattice L] (F : L →o L →o L)

/-- The derived distributive law `λ : b ∘ a ⇒ a ∘ b` (thin: pointwise `≤`). -/
def DerivedLaw : Prop := ∀ x, b F (a F x) ≤ a F (b F x)

/-- An invertible law (in the thin model: equality, i.e. commutation) is a law. -/
theorem law_of_comm (h : ∀ x, a F (b F x) = b F (a F x)) : DerivedLaw F := fun x => (h x).ge

/-- **I11, guarded.** Under the Cut Lemma for `F`, a derived law collapses the layers: `μX.νY.F = νY.μX.F`. -/
theorem guard (hcut : CutMaps F) (hlaw : DerivedLaw F) : m F = n F := semi_of_cut hcut hlaw

/-- **I11, unguarded, is false**, even for an invertible law and an M0-continuous `F` (on `ω + 1`). -/
theorem i11_false : DerivedLaw Continuous.F ∧ m Continuous.F ≠ n Continuous.F :=
  ⟨law_of_comm _ Continuous.comm, Continuous.cl_fails_continuous.2.2.2⟩

/-- **The One Ring.** Among the bi-fixed points `Fix a ∩ Fix b`, `m` is initial and `n` is final (L1, L2, I1); one
object is both iff `m = n` iff there is exactly one bi-fixed point. -/
theorem one_ring : m F = n F ↔ ∃! z, a F z = z ∧ b F z = z := by
  rw [m_eq_n_iff]
  constructor
  · intro h; exact ⟨m F, ⟨a_m, b_m⟩, fun z hz => h z hz.1 hz.2⟩
  · rintro ⟨z, _, hu⟩ w ha hb; rw [hu w ⟨ha, hb⟩, hu _ ⟨a_m, b_m⟩]

end Bi
end Mordor.Axioms.Source
