import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.WellFounded

/-!
# The boundary skeleton of a cut (log §34.3z¹¹)

A witness-free `F` on a cut `D` stays witness-free after pushing rows *up inside `D`* and columns *down inside the
complement* (`compress`), and stays monotone if the two pushes are monotone (`compress_mono`).  On a complete lattice
with ACC and DCC there are canonical pushes (`rho`, `kappa`):

* `rho x = ⋀ {p maximal in D, x ≤ p}`, a meet of maximal elements of `D`;
* `kappa y = ⋁ {u minimal in Dᶜ, u ≤ y}`, a join of minimal elements of `Dᶜ`.

So every cut counterexample on a chain-finite lattice can be assumed to have its rows among meets of `Max D` and
its columns among joins of `Min Dᶜ` (finite meets and joins, by DCC and ACC).  When both `Max D` and `Min Dᶜ` are
finite this is the finitely generated case (`FinGenAll`); the open case is the one where one of them is infinite.
When only `Max D` is finite, the rows take finitely many values (the k × ∞ case of §34.3z¹¹).
-/

namespace Mordor.Skeleton

variable {L : Type*}

section
variable [PartialOrder L]

/-- No cut witness: for `x ∈ D` and `y ∉ D`, `F x y` is neither below `x` nor above `y`. -/
def NoWit (F : L → L → L) (D : Set L) : Prop := ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y

/-- **Compression preserves witness-freeness.** -/
theorem compress {F : L → L → L} {D : Set L} (h : NoWit F D) {ρ κ : L → L}
    (hρ : ∀ x ∈ D, x ≤ ρ x ∧ ρ x ∈ D) (hκ : ∀ y, y ∉ D → κ y ≤ y ∧ κ y ∉ D) :
    NoWit (fun x y => F (ρ x) (κ y)) D := by
  intro x hx y hy
  obtain ⟨h1, h2⟩ := h (ρ x) (hρ x hx).2 (κ y) (hκ y hy).2
  exact ⟨fun c => h1 (c.trans (hρ x hx).1), fun c => h2 ((hκ y hy).1.trans c)⟩

/-- **Compression preserves monotonicity.** -/
theorem compress_mono {F : L → L → L} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {ρ κ : L → L}
    (hρ : Monotone ρ) (hκ : Monotone κ) {x x' y y' : L} (hx : x ≤ x') (hy : y ≤ y') :
    F (ρ x) (κ y) ≤ F (ρ x') (κ y') :=
  hF _ _ _ _ (hρ hx) (hκ hy)

end

section
variable [CompleteLattice L] (D : Set L)

/-- Meet of the maximal elements of `D` above `x`. -/
def rho (x : L) : L := sInf {p | p ∈ D ∧ (∀ q ∈ D, ¬ p < q) ∧ x ≤ p}

/-- Join of the minimal elements of `Dᶜ` below `y`. -/
def kappa (y : L) : L := sSup {u | u ∉ D ∧ (∀ v, v ∉ D → ¬ v < u) ∧ u ≤ y}

variable {D}

theorem rho_mono : Monotone (rho D) := fun _ _ h => sInf_le_sInf fun _ ⟨hp, hm, hx⟩ => ⟨hp, hm, h.trans hx⟩

theorem kappa_mono : Monotone (kappa D) := fun _ _ h => sSup_le_sSup fun _ ⟨hu, hm, hy⟩ => ⟨hu, hm, hy.trans h⟩

/-- Under ACC, `rho` pushes each element of a down-set `D` up inside `D`. -/
theorem rho_spec [WellFoundedGT L] (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) {x : L} (hx : x ∈ D) :
    x ≤ rho D x ∧ rho D x ∈ D := by
  refine ⟨le_sInf fun _ hp => hp.2.2, ?_⟩
  obtain ⟨p, ⟨hpD, hxp⟩, hmax⟩ := (wellFounded_gt (α := L)).has_min {p | p ∈ D ∧ x ≤ p} ⟨x, hx, le_rfl⟩
  exact hD _ _ (sInf_le ⟨hpD, fun q hq hpq => hmax q ⟨hq, hxp.trans hpq.le⟩ hpq, hxp⟩) hpD

/-- Under DCC, `kappa` pushes each element outside a down-set `D` down outside `D`. -/
theorem kappa_spec [WellFoundedLT L] (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) {y : L} (hy : y ∉ D) :
    kappa D y ≤ y ∧ kappa D y ∉ D := by
  refine ⟨sSup_le fun _ hu => hu.2.2, ?_⟩
  obtain ⟨u, ⟨huD, huy⟩, hmin⟩ := (wellFounded_lt (α := L)).has_min {u | u ∉ D ∧ u ≤ y} ⟨y, hy, le_rfl⟩
  have hm : u ∈ {u | u ∉ D ∧ (∀ v, v ∉ D → ¬ v < u) ∧ u ≤ y} :=
    ⟨huD, fun v hv hvu => hmin v ⟨hv, hvu.le.trans huy⟩ hvu, huy⟩
  have hle : u ≤ kappa D y := le_sSup hm
  exact fun h => huD (hD _ _ hle h)

/-- **The skeleton reduction.** On a complete lattice with ACC and DCC, a witness-free monotone `F` on a cut `D`
yields a witness-free monotone `F (rho x) (kappa y)`, whose rows are meets of maximal elements of `D` and whose
columns are joins of minimal elements of `Dᶜ`. -/
theorem skeleton [WellFoundedGT L] [WellFoundedLT L] (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    {F : L → L → L} (h : NoWit F D) : NoWit (fun x y => F (rho D x) (kappa D y)) D :=
  compress h (fun _ hx => rho_spec hD hx) (fun _ hy => kappa_spec hD hy)

end

end Mordor.Skeleton
