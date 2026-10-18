import Mordor.Derived
import Mordor.Dialgebra
import Mordor.Continuous
import Mordor.Duality

/-!
# The axioms in the thin model (foundations v3.7, §0, §1.1)

Every row of `docs/00-foundations.md` that has a reading in a complete lattice `L` (objects: elements; one arrow
`x → y` iff `x ≤ y`; functors: monotone maps; natural transformations: pointwise `≤`), derived as a theorem, or
refuted where the foundations tag it **False**. Names follow the row labels (`mu1`, `bd8_false`, …).

Arrows are proofs of `≤`, so every diagram commutes and "unique" is automatic (`nu3`); a row's content is the
existence of the arrows it asserts.
-/

namespace Mordor.Axioms.Thin
variable {L : Type*} [CompleteLattice L] (f g : L →o L)

/-! ## §2.1 μ-axioms -/

/-- **μ1 (Unfold / Lambek).** -/
theorem mu1 : f f.lfp = f.lfp := f.map_lfp
/-- **μ2 (Fold).** Every algebra `f A ≤ A` receives the arrow `μf → A` (unique, as all arrows are). -/
theorem mu2 {A : L} (h : f A ≤ A) : f.lfp ≤ A := f.lfp_le h
/-- **μ3 (Induction).** A sub-algebra of `μf` is all of it. -/
theorem mu3 {U : L} (hU : U ≤ f.lfp) (h : f U ≤ U) : U = f.lfp := le_antisymm hU (f.lfp_le h)
/-- **μ4 (μ-Intro).** `μf` is the meet of the pre-fixed points. -/
theorem mu4 : f.lfp = sInf {U | f U ≤ U} := rfl
/-- **μ5 (μ-Elim).** -/
theorem mu5 {U : L} (h : f U ≤ U) : f.lfp ≤ U := f.lfp_le h

/-! ## §2.2 ν-axioms -/

theorem nu1 : f f.gfp = f.gfp := f.map_gfp
theorem nu2 {C : L} (h : C ≤ f C) : C ≤ f.gfp := f.le_gfp h
/-- **ν3 (Coinduction).** In a thin category any two parallel arrows are equal. -/
theorem nu3 {x y : L} (p q : x ≤ y) : p = q := rfl
theorem nu4 : f.gfp = sSup {U | U ≤ f U} := rfl
theorem nu5 {U : L} (h : U ≤ f U) : U ≤ f.gfp := f.le_gfp h

/-! ## §2.3 Harmony -/

/-- **B1 (thin).** An algebra and a coalgebra on one carrier (`f x ≤ x ≤ f x`; `a ∘ c = id` is automatic) are
mutually inverse: the carrier is a fixed point. (False in general: `Axioms.Cat.b1_false`.) -/
theorem b1 {x : L} (a : f x ≤ x) (c : x ≤ f x) : f x = x := le_antisymm a c

/-! ## §3 Dialgebras (thin: `x` with `f x ≤ g x`) -/

/-- The `(f, g)`-dialgebras. -/
def Dial : Set L := {x | f x ≤ g x}

/-- **D1 (Cond).** Initial dialgebra when `g` has a left adjoint `l`: `μ^{f,g} = μ(l ∘ f)`. -/
theorem d1 (l : L →o L) (gc : GaloisConnection l g) : IsLeast (Dial f g) (l.comp f).lfp :=
  Dial.isLeast_dial f g l gc
/-- **D2 (Cond).** Final dialgebra when `f` has a right adjoint `r`: `ν^{f,g} = ν(r ∘ g)`. -/
theorem d2 (r : L →o L) (gc : GaloisConnection f r) : IsGreatest (Dial f g) (r.comp g).gfp :=
  Dial.isGreatest_dial f g r gc
/-- **D3 (Dialgebraic induction).** A sub-dialgebra of the initial one is all of it. -/
theorem d3 {A U : L} (hA : IsLeast (Dial f g) A) (hU : U ≤ A) (h : U ∈ Dial f g) : U = A :=
  le_antisymm hU (hA.2 h)
/-- **D4 (Dialgebraic coinduction).** -/
theorem d4 {A U : L} (hA : IsGreatest (Dial f g) A) (hU : A ≤ U) (h : U ∈ Dial f g) : U = A :=
  le_antisymm (hA.2 h) hU
/-- **D5 (Duality).** `μ^{f,g}` on `L` is `ν^{g,f}` on `Lᵒᵖ`. -/
theorem d5 (A : L) :
    IsLeast (Dial f g) A ↔
      IsGreatest {y : Lᵒᵈ | OrderDual.toDual (g (OrderDual.ofDual y)) ≤ OrderDual.toDual (f (OrderDual.ofDual y))}
        (OrderDual.toDual A) :=
  Dial.d5 f g A
/-- **D6 (Degeneracy).** `μ^{Id,Id} = ⊥`, `ν^{Id,Id} = ⊤`. -/
theorem d6 : IsLeast (Dial (OrderHom.id : L →o L) OrderHom.id) ⊥ ∧
    IsGreatest (Dial (OrderHom.id : L →o L) OrderHom.id) ⊤ :=
  ⟨⟨le_rfl, fun _ _ => bot_le⟩, ⟨le_rfl, fun _ _ => le_top⟩⟩

/-! ## §4 Bounds -/

/-- **Bd1 (Sandwich).** -/
theorem bd1 : f.lfp ≤ f.gfp := f.lfp_le_gfp
/-- **Bd1, equality case.** `μf = νf` iff `f` has exactly one fixed point (balance). -/
theorem bd1_eq : f.lfp = f.gfp ↔ ∀ x, f x = x → x = f.lfp := by
  constructor
  · intro h x hx; exact le_antisymm (h ▸ f.le_gfp hx.ge) (f.lfp_le hx.le)
  · intro h; exact (h _ f.map_gfp).symm
theorem bd2 {X : L} (h : f X ≤ X) : f.lfp ≤ X := f.lfp_le h
theorem bd3 {X : L} (h : X ≤ f X) : X ≤ f.gfp := f.le_gfp h
/-- **Bd4 (Ordinal approximation), finite stages.** `fⁿ ⊥ ≤ μf ≤ νf ≤ fⁿ ⊤`. -/
theorem bd4 (n : ℕ) : f^[n] ⊥ ≤ f.lfp ∧ f.lfp ≤ f.gfp ∧ f.gfp ≤ f^[n] ⊤ := by
  refine ⟨?_, f.lfp_le_gfp, ?_⟩
  · induction n with
    | zero => exact bot_le
    | succ n ih => rw [Function.iterate_succ_apply']; exact (f.mono ih).trans f.map_lfp.le
  · induction n with
    | zero => exact le_top
    | succ n ih => rw [Function.iterate_succ_apply']; exact f.map_gfp.ge.trans (f.mono ih)
/-- **Bd5 (Monotone convergence), ascending side.** The Kleene chain is monotone. -/
theorem bd5 : Monotone (fun n => f^[n] ⊥) :=
  monotone_nat_of_le_succ fun n => by
    rw [Function.iterate_succ_apply']
    induction n with
    | zero => exact bot_le
    | succ n ih => rw [Function.iterate_succ_apply']; exact f.mono ih
/-- **Bd6 (Continuity bound).** For ω-Scott-continuous `f`, `μf = ⋁ₙ fⁿ ⊥`. -/
theorem bd6 (h : OmegaCompletePartialOrder.ωScottContinuous f) : f.lfp = ⨆ n, f^[n] ⊥ :=
  fixedPoints.lfp_eq_sSup_iterate f h
/-- **Bd7 (Dialgebraic sandwich).** -/
theorem bd7 {A B : L} (hA : IsLeast (Dial f g) A) (hB : IsGreatest (Dial f g) B) : A ≤ B :=
  hA.2 hB.1
/-- **Bd8 (Cross bound) is false.** -/
theorem bd8_false :
    ¬ ∀ (f g : Fin 3 → Fin 3) (A B : Fin 3), IsLeast {x | f x ≤ g x} A → IsGreatest {x | g x ≤ f x} B → A ≤ B := by
  intro h
  obtain ⟨h1, h2, h3⟩ := Dial.bd8_fails
  exact h3 (h _ _ 1 0 h1 h2)
/-- **Bd9 (Reduction).** `μ^{f,Id} = μf`, `ν^{Id,f} = νf`. -/
theorem bd9 : IsLeast (Dial f OrderHom.id) f.lfp ∧ IsGreatest (Dial OrderHom.id f) f.gfp :=
  ⟨⟨f.map_lfp.le, fun _ hx => f.lfp_le hx⟩, ⟨f.map_gfp.ge, fun _ hx => f.le_gfp hx⟩⟩

/-! ## §5 μ–ν interaction, for a bifunctor `F` -/

variable (F : L →o L →o L)

/-- **I1 (lower Beck–Chevalley).** `μX.νY.F ≤ νY.μX.F`. -/
theorem i1 : m F ≤ n F := m_le_n (F := F)
/-- **I2, characterization.** `m = n` iff `a` and `b` have one common fixed point. -/
theorem i2_iff : m F = n F ↔ ∀ z, a F z = z → b F z = z → z = m F := m_eq_n_iff (F := F)
/-- **I2 is not a rule**, not even under M0 and one-step commutation: on `ω + 1`, `F x y = min (x + 1) (y ∸ 1)`. -/
theorem i2_false : ¬ (n Continuous.F ≤ m Continuous.F) := by
  rw [Continuous.m_F, Continuous.n_F]; exact fun h => ENat.top_ne_zero (le_bot_iff.mp h)
/-- **I10 (μ → ν by duality), fibrewise.** Under order reversal, the derived maps swap: `aᵈ = b`. -/
theorem i10 (x : Lᵒᵈ) : a (dualF F) x = OrderDual.toDual (b F (OrderDual.ofDual x)) := a_dual (F := F) x

end Mordor.Axioms.Thin
