import Mathlib.Order.Basic
import Mathlib.Data.Set.Prod

/-!
# Exact retractions: the restriction step behind the depth/closure SAT checks (log §34.3z⁶–¹⁰)

A map `π : L → V` is *exact on* a set `S ⊆ L` of kept coordinates if it compares every element with every kept
coordinate exactly as `L` does: `π v ≤ π s ↔ v ≤ s` and `π s ≤ π v ↔ s ≤ v` for `s ∈ S`.

* `nw` / `mono`: composing a witness-free monotone `F` with an exact monotone `π` and restricting to cells
  over `S` gives a witness-free monotone partial map with values in `V`.  This is the soundness of every finite
  instance in §34.3z⁶–¹⁰: a counterexample maps to a model of the instance.
* `prod`: exactness is coordinatewise, so retractions of the factors of `L₁ × L₂ × C` combine.
* `id_exact`: the identity is exact on everything (the layer coordinate).
* `flat_exact`: the M_ω retraction (kept atoms fixed, every other atom to one fresh atom) is exact; more generally any
  map between flat bounded orders that reflects `⊥`, `⊤` and identifies nothing with a kept coordinate.
* `exact_of_fix`: for the Ω gap retraction it suffices to check comparisons of non-kept elements with kept ones.

What remains informal in those sections is only the SAT encoding of the resulting finite instances.
-/

namespace Mordor.Exact

variable {L V : Type*} [PartialOrder L] [PartialOrder V]

/-- `π` compares every element with every kept coordinate exactly as `L` does. -/
def IsExact (π : L → V) (S : Set L) : Prop :=
  ∀ s ∈ S, ∀ v : L, (π v ≤ π s ↔ v ≤ s) ∧ (π s ≤ π v ↔ s ≤ v)

/-- **Witness-freeness transfers.** For kept `x ∈ D` and kept `y ∉ D`, `π (F x y)` is neither below `π x` nor above
`π y`.  (Only exactness at `x` and `y` is used, not monotonicity of `π`.) -/
theorem nw {π : L → V} {S : Set L} (hπ : IsExact π S) {F : L → L → L} {D : Set L}
    (nwF : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {x y : L} (hxS : x ∈ S) (hyS : y ∈ S) (hx : x ∈ D) (hy : y ∉ D) :
    ¬ π (F x y) ≤ π x ∧ ¬ π y ≤ π (F x y) :=
  ⟨fun h => (nwF x hx y hy).1 ((hπ x hxS (F x y)).1.1 h),
   fun h => (nwF x hx y hy).2 ((hπ y hyS (F x y)).2.1 h)⟩

/-- **Monotonicity transfers** for any monotone `π`. -/
theorem mono {π : L → V} (hπm : Monotone π) {F : L → L → L}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {x x' y y' : L} (hx : x ≤ x') (hy : y ≤ y') :
    π (F x y) ≤ π (F x' y') :=
  hπm (hF _ _ _ _ hx hy)

/-- The identity is exact on every set. -/
theorem id_exact (S : Set L) : IsExact (id : L → L) S := fun _ _ _ => ⟨Iff.rfl, Iff.rfl⟩

variable {L₂ V₂ : Type*} [PartialOrder L₂] [PartialOrder V₂]

/-- **Exactness is coordinatewise.** -/
theorem prod {π₁ : L → V} {π₂ : L₂ → V₂} {S₁ : Set L} {S₂ : Set L₂} (h₁ : IsExact π₁ S₁) (h₂ : IsExact π₂ S₂) :
    IsExact (Prod.map π₁ π₂) (S₁ ×ˢ S₂) := by
  rintro ⟨s₁, s₂⟩ ⟨hs₁, hs₂⟩ ⟨v₁, v₂⟩
  simp only [Prod.map, Prod.mk_le_mk]
  exact ⟨and_congr (h₁ s₁ hs₁ v₁).1 (h₂ s₂ hs₂ v₂).1, and_congr (h₁ s₁ hs₁ v₁).2 (h₂ s₂ hs₂ v₂).2⟩

/-- Exactness on `S` gives exactness on every subset. -/
theorem mono_set {π : L → V} {S S' : Set L} (h : IsExact π S) (hS : S' ⊆ S) : IsExact π S' :=
  fun s hs v => h s (hS hs) v

/-! ## The fresh-symbol retraction (M_ω and Ω)

The concrete retractions of §34.3z⁶–⁹ fix the kept coordinates and send every other element to a symbol that is
related to each kept coordinate exactly as the element was (for M_ω: one fresh atom `o`, related only to `⊥`, `⊤`;
for Ω: the gap symbol between the kept neighbours on the element's chain).  The following lemma isolates what has to
be checked: exactness reduces to the two comparison conditions at non-kept elements, because kept elements are
fixed. -/

theorem exact_of_fix {π : L → V} {S : Set L} (hfix : ∀ s ∈ S, ∀ t ∈ S, (π s ≤ π t ↔ s ≤ t))
    (hout : ∀ s ∈ S, ∀ v, v ∉ S → (π v ≤ π s ↔ v ≤ s) ∧ (π s ≤ π v ↔ s ≤ v)) : IsExact π S := by
  intro s hs v
  by_cases hv : v ∈ S
  · exact ⟨hfix v hv s hs, hfix s hs v hv⟩
  · exact hout s hs v hv

/-- **The M_ω retraction is exact.**  In a *flat* bounded order (two elements are comparable only if equal or one
of them is `⊥` or `⊤`, as in M_ω and in the value types of the instances), any map that reflects `⊥` and `⊤` and never
identifies an element with a kept coordinate other than itself is exact.  For M_ω: fix the kept atoms and send every
other atom to one fresh atom `o`. -/
theorem flat_exact [BoundedOrder L] [BoundedOrder V]
    (flatL : ∀ a b : L, a ≤ b → a = ⊥ ∨ b = ⊤ ∨ a = b) (flatV : ∀ a b : V, a ≤ b → a = ⊥ ∨ b = ⊤ ∨ a = b)
    {π : L → V} {S : Set L} (hb : ∀ v, π v = ⊥ ↔ v = ⊥) (ht : ∀ v, π v = ⊤ ↔ v = ⊤)
    (hinj : ∀ s ∈ S, ∀ v, π v = π s → v = s) : IsExact π S := by
  intro s hs v
  constructor
  · constructor
    · intro h
      rcases flatV _ _ h with h | h | h
      · rw [(hb v).1 h]; exact bot_le
      · rw [(ht s).1 h]; exact le_top
      · rw [hinj s hs v h]
    · intro h
      rcases flatL _ _ h with h | h | h
      · rw [(hb v).2 h]; exact bot_le
      · rw [(ht s).2 h]; exact le_top
      · rw [h]
  · constructor
    · intro h
      rcases flatV _ _ h with h | h | h
      · rw [(hb s).1 h]; exact bot_le
      · rw [(ht v).1 h]; exact le_top
      · rw [hinj s hs v h.symm]
    · intro h
      rcases flatL _ _ h with h | h | h
      · rw [(hb s).2 h]; exact bot_le
      · rw [(ht v).2 h]; exact le_top
      · rw [h]

end Mordor.Exact
