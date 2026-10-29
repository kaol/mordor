import Mordor.Crossing

/-!
# Join saturation for finitely generated cuts (log §34.3z²⁰)

`D = ⋃ᵢ ↓pᵢ` (finite index set), `F` monotone and witness-free, `gᵢ = F pᵢ`. Put `J y = y ⊔ ⨆ᵢ gᵢ y`.

* `sat_le_iff`: `J y ≤ y` iff every generator row contracts at `y`; the fixed points of `J` outside `D` are the common
  contracting columns `𝒮 = {y ∉ D : ∀ i, gᵢ y ≤ y}` (`⊤ ∈ 𝒮`).
* `corridor`: if `gᵢ c ≤ c`, row `i` contracts strictly at every column of `[gᵢ c, c]` outside `D`.
* `amalgam`: joining a column with some of its escaping row values keeps those rows escaping.
* `exists_min_common`, `min_common_join` (DCC only, no ACC): a minimal element `c` of `𝒮` exists, and it is the join of
  its own row values, `c = ⨆ᵢ gᵢ c`. The join is outside `D` by the column lemma and every row contracts on it, so
  minimality forces equality. This subsumes the "saturation ascent returns to `c`" of the brief without ACC.
-/

namespace Mordor.Saturation
open Mordor.Crossing

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : α → α → α} {p : ι → α}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

/-- The saturation map `J y = y ⊔ ⨆ᵢ F (pᵢ) y`. -/
def sat (F : α → α → α) (p : ι → α) (y : α) : α := y ⊔ Finset.univ.sup fun i => F (p i) y

theorem sat_le_iff {y : α} : sat F p y ≤ y ↔ ∀ i, F (p i) y ≤ y := by
  simp [sat, Finset.sup_le_iff]

theorem le_sat (y : α) : y ≤ sat F p y := le_sup_left

include hF in
theorem sat_mono : Monotone (sat F p) := fun _ _ h =>
  sup_le_sup h (Finset.sup_mono_fun fun _ _ => hF _ _ _ _ le_rfl h)

include hF nw in
/-- **Contracting corridor.** If row `i` contracts at `c`, it contracts strictly at every column `x ∉ D` with
`gᵢ c ≤ x ≤ c`. -/
theorem corridor {i : ι} {c x : α} (hlo : F (p i) c ≤ x) (hxc : x ≤ c) (hx : ¬ ∃ j, x ≤ p j) :
    F (p i) x < x :=
  lt_of_le_of_ne ((hF _ _ _ _ le_rfl hxc).trans hlo) fun heq => (nw (p i) ⟨i, le_rfl⟩ x hx).2 heq.ge

include hF in
/-- **Amalgamation.** If the rows in `I` escape at `y ∉ D`, they still escape at `z = y ⊔ ⨆_{i∈I} gᵢ y`, which is outside
`D` and above `y`. -/
theorem amalgam {y : α} (hy : ¬ ∃ j, y ≤ p j) (I : Finset ι) (hI : ∀ i ∈ I, ¬ ∃ j, F (p i) y ≤ p j) :
    (¬ ∃ j, y ⊔ I.sup (fun i => F (p i) y) ≤ p j) ∧
      ∀ i ∈ I, ¬ ∃ j, F (p i) (y ⊔ I.sup (fun i => F (p i) y)) ≤ p j := by
  refine ⟨fun ⟨j, hj⟩ => hy ⟨j, le_sup_left.trans hj⟩, fun i hi ⟨j, hj⟩ => hI i hi ⟨j, ?_⟩⟩
  exact (hF _ _ _ _ le_rfl le_sup_left).trans hj

/-- The common contracting columns. -/
def Common (F : α → α → α) (p : ι → α) (y : α) : Prop := (¬ ∃ j, y ≤ p j) ∧ ∀ i, F (p i) y ≤ y

theorem exists_min_common [WellFoundedLT α] (htop : ¬ ∃ j, ⊤ ≤ p j) :
    ∃ c, Common F p c ∧ ∀ x, Common F p x → x ≤ c → x = c := by
  obtain ⟨c, hc, hmin⟩ := (wellFounded_lt (α := α)).has_min {x | Common F p x} ⟨⊤, htop, fun _ => le_top⟩
  exact ⟨c, hc, fun x hx hxc => eq_of_le_of_not_lt hxc (hmin x hx)⟩

include hF nw in
/-- **A minimal common contracting column is the join of its generator-row values.** -/
theorem min_common_join [Nonempty ι] {c : α} (hc : Common F p c) (hmin : ∀ x, Common F p x → x ≤ c → x = c) :
    Finset.univ.sup (fun i => F (p i) c) = c := by
  set y := Finset.univ.sup fun i => F (p i) c
  have hyc : y ≤ c := Finset.sup_le fun i _ => hc.2 i
  obtain ⟨i, hi⟩ := column_lemma hF p hc.1 nw
  have hy : ¬ ∃ j, y ≤ p j := fun ⟨j, hj⟩ => hi ⟨j, (Finset.le_sup (f := fun i => F (p i) c) (Finset.mem_univ i)).trans hj⟩
  refine hmin y ⟨hy, fun l => ?_⟩ hyc
  exact (hF _ _ _ _ le_rfl hyc).trans (Finset.le_sup (f := fun i => F (p i) c) (Finset.mem_univ l))

end Mordor.Saturation
