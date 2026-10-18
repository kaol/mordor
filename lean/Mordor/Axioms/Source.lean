import Mordor.Cut
import Mordor.Continuous
import Mathlib.Data.Fintype.Order

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

/-- **Turi–Plotkin, thin.** A law `S ∘ B ≤ B ∘ S` lifts `μS` to a `B`-coalgebra and `νB` to an `S`-algebra, and
gives the comparison `μS ≤ νB`. -/
theorem tp_thin (S B : L →o L) (hlaw : ∀ x, S (B x) ≤ B (S x)) :
    S.lfp ≤ B S.lfp ∧ S B.gfp ≤ B.gfp ∧ S.lfp ≤ B.gfp := by
  have h1 : S.lfp ≤ B S.lfp := S.lfp_le ((hlaw _).trans (B.mono S.map_lfp.le))
  refine ⟨h1, B.le_gfp ?_, B.le_gfp h1⟩
  calc S B.gfp = S (B B.gfp) := by rw [B.map_gfp]
    _ ≤ B (S B.gfp) := hlaw _

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

/-- **What Turi–Plotkin gives for the derived law: only the outer sandwich, which holds anyway.** With syntax `b`
and behaviour `a`, the law `b ∘ a ≤ a ∘ b` yields `μb ≤ νa` (`tp_thin`); but `μb ≤ m ≤ n ≤ νa` holds for every
`F` (L1, L2, I1). The inner collapse `m = n` is not a bialgebra fact: it is I11, guarded by the Cut Lemma. -/
theorem outer_sandwich : (b F).lfp ≤ m F ∧ m F ≤ n F ∧ n F ≤ (a F).gfp :=
  ⟨(b F).lfp_le b_m.le, m_le_n, (a F).le_gfp a_n.ge⟩

theorem tp_derived (hlaw : DerivedLaw F) : (b F).lfp ≤ (a F).gfp := (tp_thin (b F) (a F) hlaw).2.2

/-! ### The automatic laws (log §34.3j)

The exhaustive search found two laws between the powers that hold for every `F`. Both follow from one lemma. -/

/-- **Cross lemma.** `y ≤ a z` and `b y ≤ z` give `b y ≤ a z`. -/
theorem cross {y z : L} (hy : y ≤ a F z) (hb : b F y ≤ z) : b F y ≤ a F z := by
  have hs : b F y ⊔ a F z ≤ F z (b F y ⊔ a F z) := sup_le
    ((col_b (F := F) y).ge.trans ((F.mono hb _).trans ((F z).mono (hy.trans le_sup_right))))
    ((row_a (F := F) z).ge.trans ((F z).mono le_sup_right))
  exact le_sup_left.trans (le_a hs)

/-- **The GSOS-style law is automatic**: `b (x ⊓ a x) ≤ a (T_b x)`. -/
theorem gsos_law (x : L) : b F (x ⊓ a F x) ≤ a F (T (b F) x) :=
  cross F (inf_le_right.trans ((a F).mono (le_T _ x)))
    (((b F).mono (inf_le_left.trans (le_T _ x))).trans (f_T_le _ x))

/-- **The closure/interior law is automatic**: `T_b (D_a x) ≤ D_a (T_b x)`. -/
theorem clint_law (x : L) : T (b F) (D (a F) x) ≤ D (a F) (T (b F) x) := by
  set t := T (b F) (D (a F) x)
  have ht : t ≤ a F t := by
    have hc : t ≤ t ⊓ a F t := T_le _ (le_inf (le_T _ _) ((D_le_f _ x).trans ((a F).mono (le_T _ _))))
      (le_inf (((b F).mono inf_le_left).trans (f_T_le _ _)) (cross F inf_le_right
        (((b F).mono inf_le_left).trans (f_T_le _ _))))
    exact hc.trans inf_le_right
  exact le_D _ (T_le _ ((D_le _ x).trans (le_T _ x)) (f_T_le _ x)) ht

/-! ### I5 in the thin model

Dinaturality is automatic in a thin category, so I5's content is its "acyclicity" hypothesis. The one reading that
makes I5 true is that `F` depends on one variable only (`i5_left`, `i5_right`). Separating the variables, which is
the natural weaker reading (`F x y = g x ⊔ h y`, no interaction between X and Y), does **not** suffice (`i5_sep_false`). -/

theorem i5_left {g : L →o L} (hF : ∀ x y, F x y = g x) : m F = n F := by
  have hb : ∀ y, b F y = g.lfp := fun y => le_antisymm (b_le (by rw [hF]; exact g.map_lfp.le))
    (g.lfp_le (by have := col_b (F := F) y; rw [hF] at this; exact this.le))
  rw [m_eq_n_iff]; intro z _ hzb
  rw [← hzb, hb, ← hb (m F), b_m]

theorem i5_right {h : L →o L} (hF : ∀ x y, F x y = h y) : m F = n F := by
  have ha : ∀ x, a F x = h.gfp := fun x => le_antisymm
    (h.le_gfp (by have := row_a (F := F) x; rw [hF] at this; exact this.ge))
    (le_a (by rw [hF]; exact h.map_gfp.ge))
  rw [m_eq_n_iff]; intro z hza _
  rw [← hza, ha, ← ha (m F), a_m]

end Bi

/-- The separable bifunction `F x y = max (g x) (h y)` on the 3-chain, `g = (0, 2, 2)`, `h = (0, 0, 1)`. -/
def sepF : Fin 3 →o Fin 3 →o Fin 3 :=
  ⟨fun x => ⟨fun y => max (if x = 0 then 0 else 2) (if y = 2 then 1 else 0), by
      intro y y' hy; dsimp only; apply max_le_max le_rfl; revert y y'; decide⟩,
   by intro x x' hx y; dsimp only; apply max_le_max _ le_rfl; revert x x'; decide⟩

/-- **I5 with separated variables is false**: `μX.νY.F = 0 ≠ 2 = νY.μX.F` for `sepF`. -/
theorem i5_sep_false : m sepF = (0 : Fin 3) ∧ n sepF = (2 : Fin 3) := by
  have ha : a sepF 0 = 0 := by
    have h := row_a (F := sepF) 0
    revert h; generalize a sepF 0 = y; revert y; decide
  have hb : b sepF 2 = 2 := by
    have h := col_b (F := sepF) 2
    revert h; generalize b sepF 2 = x; revert x; decide
  exact ⟨le_antisymm ((a sepF).lfp_le ha.le) bot_le, le_antisymm le_top ((b sepF).le_gfp hb.ge)⟩

end Mordor.Axioms.Source
