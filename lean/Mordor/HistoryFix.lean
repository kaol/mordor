import Mordor.Crossing

/-!
# The history-meet terminal state, sharpened (log §34.3z²⁶)

`D = ⋃ᵢ ↓pᵢ` (finite index set), `F` monotone and witness-free, `gᵢ = F pᵢ`.

* `contract_bot`, `min_contract_eq_bot`: the rows contracting at a column form a down-set, so the minimal contracting
  row is `⊥`. Minimizing the contracting row carries no information.
* `min_terminal` (DCC): for any row `r` below every generator (`⊥`, or `⋀ᵢ pᵢ`), a *minimal* column `y ∉ D` with
  `F r y ≤ y` satisfies the history-meet terminal condition `y ⊓ gⱼ y ∈ D` for every `j`. This is `theta_terminal`
  with the extra minimality: no smaller column outside `D` is contracted by `r`.
* `phi_mem`: under that condition `z ↦ y ⊓ F z y` maps `D` into `D`.
* `label_fixed`, `label_fixed_proper`: under it, there is a nonempty label set `K` whose history meet
  `z_K = y ⊓ F (⋀_K p) y` has labels exactly `K`, i.e. `z_K ≤ pᵢ ↔ i ∈ K`. If the triple-meet row contracts at `y`,
  then `K` is not everything. No chain condition is needed: the labels only shrink.
* `fixed_sideways`: at such `K` the row `⋀_K p` does not contract at `y` (W1 at that row).
-/

namespace Mordor.HistoryFix

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : α → α → α} {p : ι → α}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
include hF

theorem contract_bot {a y : α} (h : F a y ≤ y) : F ⊥ y ≤ y := (hF _ _ _ _ bot_le le_rfl).trans h

theorem min_contract_eq_bot {a y : α} (ha : F a y ≤ y) (hmin : ∀ a', F a' y ≤ y → a' ≤ a → a' = a) : a = ⊥ :=
  (hmin ⊥ (contract_bot hF ha) bot_le).symm

include nw

theorem min_terminal [WellFoundedLT α] (htop : ¬ ∃ j, ⊤ ≤ p j) {r : α} (hr : ∀ j, r ≤ p j) :
    ∃ y, (¬ ∃ j, y ≤ p j) ∧ F r y ≤ y ∧
      (∀ y', y' < y → (¬ ∃ j, y' ≤ p j) → ¬ F r y' ≤ y') ∧ ∀ j, ∃ k, y ⊓ F (p j) y ≤ p k := by
  obtain ⟨y, ⟨hy, hry⟩, hmin⟩ := (wellFounded_lt (α := α)).has_min {y | (¬ ∃ j, y ≤ p j) ∧ F r y ≤ y}
    ⟨⊤, htop, le_top⟩
  refine ⟨y, hy, hry, fun y' hlt hy' hc => hmin y' ⟨hy', hc⟩ hlt, fun j => ?_⟩
  by_contra hj
  have hlt : y ⊓ F (p j) y < y :=
    lt_of_le_of_ne inf_le_left fun heq => (nw (p j) ⟨j, le_rfl⟩ y hy).2 (heq.symm.le.trans inf_le_right)
  exact hmin _ ⟨hj, le_inf ((hF _ _ _ _ le_rfl inf_le_left).trans hry) (hF _ _ _ _ (hr j) inf_le_left)⟩ hlt

omit nw in
theorem phi_mem {y z : α} (ht : ∀ j, ∃ k, y ⊓ F (p j) y ≤ p k) {i : ι} (hz : z ≤ p i) :
    ∃ k, y ⊓ F z y ≤ p k :=
  (ht i).imp fun _ hk => (inf_le_inf_left _ (hF _ _ _ _ hz le_rfl)).trans hk

/-- Labels of `z`: the generators above it. -/
noncomputable def lab (p : ι → α) (z : α) : Finset ι := by
  classical exact Finset.univ.filter fun i => z ≤ p i

omit hF nw in
theorem mem_lab {z : α} {i : ι} : i ∈ lab p z ↔ z ≤ p i := by
  classical simp [lab]

/-- The history meet of the row `⋀_K p` at `y`. -/
def zK (F : α → α → α) (p : ι → α) (y : α) (K : Finset ι) : α := y ⊓ F (K.inf p) y

omit nw in
theorem zK_anti {y : α} {K K' : Finset ι} (h : K' ⊆ K) : zK F p y K ≤ zK F p y K' :=
  inf_le_inf_left _ (hF _ _ _ _ (Finset.inf_mono h) le_rfl)

omit nw in
theorem label_fixed {y : α} (ht : ∀ j, ∃ k, y ⊓ F (p j) y ≤ p k) :
    ∀ K : Finset ι, K.Nonempty → lab p (zK F p y K) ⊆ K →
      ∃ K', K'.Nonempty ∧ K' ⊆ K ∧ lab p (zK F p y K') = K' := by
  intro K
  induction K using Finset.strongInduction with
  | H K ih =>
    intro hne hsub
    by_cases heq : lab p (zK F p y K) = K
    · exact ⟨K, hne, subset_rfl, heq⟩
    · set K₁ := lab p (zK F p y K)
      have hne₁ : K₁.Nonempty := by
        obtain ⟨j, hj⟩ := hne
        obtain ⟨k, hk⟩ := ht j
        exact ⟨k, mem_lab.2 ((zK_anti hF (Finset.singleton_subset_iff.2 hj)).trans
          (by simpa [zK] using hk))⟩
      have hsub₁ : lab p (zK F p y K₁) ⊆ K₁ := fun i hi =>
        mem_lab.2 ((zK_anti hF hsub).trans (mem_lab.1 hi))
      obtain ⟨K', h1, h2, h3⟩ := ih K₁ (Finset.ssubset_iff_subset_ne.2 ⟨hsub, heq⟩) hne₁ hsub₁
      exact ⟨K', h1, h2.trans hsub, h3⟩

theorem fixed_sideways {y : α} (hy : ¬ ∃ j, y ≤ p j) {K : Finset ι} (hne : K.Nonempty)
    (hK : lab p (zK F p y K) = K) : ¬ F (K.inf p) y ≤ y := by
  intro hc
  obtain ⟨i, hi⟩ := hne
  have hle : F (K.inf p) y ≤ K.inf p := Finset.le_inf fun j hj => by
    have : zK F p y K ≤ p j := mem_lab.1 (hK.symm ▸ hj : j ∈ lab p (zK F p y K))
    simpa [zK, inf_eq_right.2 hc] using this
  exact (nw _ ⟨i, Finset.inf_le hi⟩ y hy).1 hle

theorem label_fixed_proper [Nonempty ι] {y : α} (hy : ¬ ∃ j, y ≤ p j)
    (ht : ∀ j, ∃ k, y ⊓ F (p j) y ≤ p k) (hh : F (Finset.univ.inf p) y ≤ y) :
    ∃ K : Finset ι, K.Nonempty ∧ K ≠ Finset.univ ∧ lab p (zK F p y K) = K ∧ ¬ F (K.inf p) y ≤ y := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨K, hne, -, hK⟩ := label_fixed hF ht Finset.univ ⟨i₀, Finset.mem_univ _⟩ (Finset.subset_univ _)
  refine ⟨K, hne, fun hu => fixed_sideways hF nw hy hne hK (hu ▸ hh), hK, fixed_sideways hF nw hy hne hK⟩

end Mordor.HistoryFix
