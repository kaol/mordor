import Mordor.IntervalRefinement

/-!
# Interface traces of a confinement region (round 26, §34.3z¹²⁵)

ChatGPT brief "interface preservation and separator ancestry", Programme A.

`G : α × α → α` monotone in the product order, `S` any set of cells (the brief's `S_I = G⁻¹[w, v]`).
* `lowTrace S G p = ⨆_{q ∉ S, q ≤ p} G q`, `highTrace S G p = ⨅_{q ∉ S, p ≤ q} G q`.
* `lowTrace_mono`, `highTrace_mono`; `lowTrace_le_highTrace` (G monotone); `lowTrace_outside`, `highTrace_outside`
  (both recover `G` off `S`); `between_traces`: every monotone `G'` agreeing with `G` off `S` satisfies
  `lowTrace ≤ G' ≤ highTrace` — the external order obligations of a modification supported on `S`.
* §34.3z¹²⁶: `patch_mono`, `patch_no_witness` (patching a selection between the traces into `G`);
  `external_pin_top`, `external_pin_bot`; `internal_pin` (two rows over a shared column force the endpoint `v`);
  `general_pin`, `general_pin_dual` (any cells `p ≤ q₁, q₂`, resp. `q₁, q₂ ≤ p`, with admissibility predicates);
  `atom_family_block` (the infinite-antichain obstruction).
-/

namespace Mordor.InterfaceTrace

set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] (S : Set (α × α)) (G : α × α → α)

noncomputable def lowTrace (p : α × α) : α := ⨆ q ∈ {q | q ∉ S ∧ q ≤ p}, G q
noncomputable def highTrace (p : α × α) : α := ⨅ q ∈ {q | q ∉ S ∧ p ≤ q}, G q

theorem lowTrace_mono : Monotone (lowTrace S G) := fun _ _ h =>
  iSup₂_le fun q hq => le_iSup₂_of_le q ⟨hq.1, hq.2.trans h⟩ le_rfl

theorem highTrace_mono : Monotone (highTrace S G) := fun _ _ h =>
  le_iInf₂ fun q hq => iInf₂_le q ⟨hq.1, h.trans hq.2⟩

variable {S G}

theorem lowTrace_le_highTrace (hG : Monotone G) (p : α × α) : lowTrace S G p ≤ highTrace S G p :=
  iSup₂_le fun _ hq => le_iInf₂ fun _ hq' => hG (hq.2.trans hq'.2)

theorem lowTrace_outside (hG : Monotone G) {p : α × α} (hp : p ∉ S) : lowTrace S G p = G p :=
  le_antisymm (iSup₂_le fun _ hq => hG hq.2) (le_iSup₂_of_le p ⟨hp, le_rfl⟩ le_rfl)

theorem highTrace_outside (hG : Monotone G) {p : α × α} (hp : p ∉ S) : highTrace S G p = G p :=
  le_antisymm (iInf₂_le p ⟨hp, le_rfl⟩) (le_iInf₂ fun _ hq => hG hq.2)

/-- **External obligations.** -/
theorem between_traces {G' : α × α → α} (hG' : Monotone G') (hagree : ∀ q, q ∉ S → G' q = G q) (p : α × α) :
    lowTrace S G p ≤ G' p ∧ G' p ≤ highTrace S G p :=
  ⟨iSup₂_le fun q hq => (hagree q hq.1) ▸ hG' hq.2, le_iInf₂ fun q hq => (hagree q hq.1) ▸ hG' hq.2⟩

/-- **Patching** (monotonicity). A selection `g` on `S`, monotone on `S` and between the traces, patched into `G`,
is globally monotone. -/
theorem patch_mono [DecidablePred (· ∈ S)] (hG : Monotone G) {g : α × α → α}
    (hg : ∀ p q, p ∈ S → q ∈ S → p ≤ q → g p ≤ g q)
    (hb : ∀ p ∈ S, lowTrace S G p ≤ g p ∧ g p ≤ highTrace S G p) :
    Monotone fun p => if p ∈ S then g p else G p := by
  intro p q hpq
  by_cases hp : p ∈ S <;> by_cases hq : q ∈ S <;> simp only [hp, hq, if_true, if_false]
  · exact hg p q hp hq hpq
  · exact (hb p hp).2.trans (iInf₂_le q ⟨hq, hpq⟩)
  · exact (le_iSup₂_of_le p ⟨hp, hpq⟩ le_rfl).trans (hb q hq).1
  · exact hG hpq

/-- **Patching** (no witness). If `G` has no witness off `S` and `g` is safe on the cross cells of `S`, the patched
map has no witness. -/
theorem patch_no_witness [DecidablePred (· ∈ S)] {g : α × α → α} {D : Set α}
    (hGs : ∀ x ∈ D, ∀ y ∉ D, (x, y) ∉ S → ¬ G (x, y) ≤ x ∧ ¬ y ≤ G (x, y))
    (hgs : ∀ x ∈ D, ∀ y ∉ D, (x, y) ∈ S → ¬ g (x, y) ≤ x ∧ ¬ y ≤ g (x, y)) :
    ∀ x ∈ D, ∀ y ∉ D, ¬ (if (x, y) ∈ S then g (x, y) else G (x, y)) ≤ x ∧
      ¬ y ≤ (if (x, y) ∈ S then g (x, y) else G (x, y)) := by
  intro x hx y hy
  by_cases h : (x, y) ∈ S
  · simp only [h, if_true]; exact hgs x hx y hy h
  · simp only [h, if_false]; exact hGs x hx y hy h

/-- **External pinning.** A value between the traces and inside `[w, v]` is forced to `v` when the lower trace is `v`
(dually to `w` when the upper trace is `w`). -/
theorem external_pin_top {G' : α × α → α} {p : α × α} {v : α} (hl : lowTrace S G p = v)
    (hb : lowTrace S G p ≤ G' p) (hv : G' p ≤ v) : G' p = v :=
  le_antisymm hv (hl ▸ hb)

theorem external_pin_bot {G' : α × α → α} {p : α × α} {w : α} (hu : highTrace S G p = w)
    (hb : G' p ≤ highTrace S G p) (hw : w ≤ G' p) : G' p = w :=
  le_antisymm (hu ▸ hb) hw

/-- **Internal pinning.** Rows `a₁, a₂` with a shared column `y` above a safe cross cell `(x, y)`. If any two
admissible values of the upper cells other than `v` meet below `x`, a monotone `G'` with admissible upper values must
put `v` on one of them. -/
theorem internal_pin {G' : α × α → α} (hG' : Monotone G') {x a₁ a₂ y v : α} (h₁ : x ≤ a₁) (h₂ : x ≤ a₂)
    (hsafe : ¬ G' (x, y) ≤ x) (A₁ A₂ : α → Prop) (hA₁ : A₁ (G' (a₁, y))) (hA₂ : A₂ (G' (a₂, y)))
    (hpat : ∀ z₁ z₂, A₁ z₁ → A₂ z₂ → z₁ ≠ v → z₂ ≠ v → z₁ ⊓ z₂ ≤ x) :
    G' (a₁, y) = v ∨ G' (a₂, y) = v := by
  by_contra h
  push_neg at h
  have hm : G' (x, y) ≤ G' (a₁, y) ⊓ G' (a₂, y) :=
    le_inf (hG' (show (x, y) ≤ (a₁, y) from ⟨h₁, le_rfl⟩)) (hG' (show (x, y) ≤ (a₂, y) from ⟨h₂, le_rfl⟩))
  exact hsafe (hm.trans (hpat _ _ hA₁ hA₂ h.1 h.2))

/-- **General pin.** Cells `p ≤ q₁, q₂` with admissibility predicates `A₀, A₁, A₂`. If no admissible lower value lies
below the meet of two admissible upper values other than `v`, a monotone `G'` with admissible values puts `v` on
`q₁` or `q₂`. (`internal_pin` is the case `A₀ t := ¬ t ≤ x`.) -/
theorem general_pin {G' : α × α → α} (hG' : Monotone G') {p q₁ q₂ : α × α} (h₁ : p ≤ q₁) (h₂ : p ≤ q₂) {v : α}
    (A₀ A₁ A₂ : α → Prop) (hA₀ : A₀ (G' p)) (hA₁ : A₁ (G' q₁)) (hA₂ : A₂ (G' q₂))
    (hpat : ∀ t z₁ z₂, A₀ t → A₁ z₁ → A₂ z₂ → z₁ ≠ v → z₂ ≠ v → ¬ t ≤ z₁ ⊓ z₂) :
    G' q₁ = v ∨ G' q₂ = v := by
  by_contra h
  push_neg at h
  exact hpat _ _ _ hA₀ hA₁ hA₂ h.1 h.2 (le_inf (hG' h₁) (hG' h₂))

/-- **General dual pin.** Cells `q₁, q₂ ≤ p`: if no admissible upper value lies above the join of two admissible lower
values other than `w`, a monotone `G'` puts `w` on `q₁` or `q₂`. -/
theorem general_pin_dual {G' : α × α → α} (hG' : Monotone G') {p q₁ q₂ : α × α} (h₁ : q₁ ≤ p) (h₂ : q₂ ≤ p)
    {w : α} (A₀ A₁ A₂ : α → Prop) (hA₀ : A₀ (G' p)) (hA₁ : A₁ (G' q₁)) (hA₂ : A₂ (G' q₂))
    (hpat : ∀ t z₁ z₂, A₀ t → A₁ z₁ → A₂ z₂ → z₁ ≠ w → z₂ ≠ w → ¬ z₁ ⊔ z₂ ≤ t) :
    G' q₁ = w ∨ G' q₂ = w := by
  by_contra h
  push_neg at h
  exact hpat _ _ _ hA₀ hA₁ hA₂ h.1 h.2 (sup_le (hG' h₁) (hG' h₂))

/-- **Infinite-antichain obstruction** (the core of the `M_ω` example of §34.3z¹²⁶). Rows `a i` with pairwise meets
below `x`; every row's value `g i` is the atom `a j` of a *different* row; a lower value `g₀` below all of them is
safe (`g₀ ≰ x`). This is impossible. Every finite subfamily of the `M_ω` rows escapes (by a value whose row is
absent), so the obstruction has no certificate of bounded arity. -/
theorem atom_family_block {ι : Type*} (a : ι → α) {x g₀ : α} (g : ι → α)
    (hmeet : ∀ i j, i ≠ j → a i ⊓ a j ≤ x) (hval : ∀ i, ∃ j, j ≠ i ∧ g i = a j) (hlow : ∀ i, g₀ ≤ g i)
    (hsafe : ¬ g₀ ≤ x) (i₀ : ι) : False := by
  obtain ⟨j, -, hj⟩ := hval i₀
  obtain ⟨l, hlj, hl⟩ := hval j
  exact hsafe ((le_inf (hj ▸ hlow i₀) (hl ▸ hlow j)).trans (hmeet j l (Ne.symm hlj)))

end Mordor.InterfaceTrace
