import Mordor.SupportExchange

/-!
# Input cofactors of reciprocal supports (round 26, §34.3z¹⁰²)

Response to the brief "cofactor exchange and staggered reciprocal supports". Supports are indexed families
`p : ι → α` (rows, `s = ⨆ᵢ F (pᵢ) s`) and `q : ι → α` (columns, `r = ⨅ᵢ F r (qᵢ)`), `ι` finite. Input cofactors:
`p⁻ᵢ = ⨆_{j≠i} pⱼ` (`rowCof`), `q⁻ᵢ = ⨅_{j≠i} qⱼ` (`colCof`).

* `row_cofactor_decomposition` / `column_cofactor_decomposition`: `s = uᵢ ⊔ U⁻ᵢ` with both strictly below `s` and
  incomparable (dually for `r`).
* `support_antichain_row` / `support_antichain_col`: an irredundant support is an antichain; `rowCof_strict`.
* `row_cofactor_exchange`, `column_cofactor_exchange`, `cofactor_exchange_dichotomy`: as in the brief (no regularity).
* **`rowCof_rowCof` / `colCof_colCof`**: for `|ι| ≥ 3` the second cofactor family is constant, `⨆ p` resp. `⨅ q`;
  hence **`second_cofactor_crosses`**: the second exchange fails at every index (`⨆ p ∉ D`, `⨅ q ∈ D`). Repeated
  cofactor exchange terminates after at most one success, with no ACC/DCC and no minimum-cardinality hypothesis;
  for `|ι| = 2` it is the swap.
* **`cofactor_petal_injective`**, `cofactor_stable_card`: for `D = ⋃ₖ ↓gₖ`, if every row cofactor is in `D` then
  distinct cofactors lie under distinct generators, so `|ι| ≤ k` (for `k = 2`, a size-3 row support always has a
  crossing cofactor); `cofactor_stable_comeets`: the support then sits under the co-meets `⨅_{i≠j} g_{σ i}` and those
  co-meets are themselves a row support (for `|ι| = k = 3`: the pairwise generator meets).
* `cofactor_threshold`: the cofactor row's orbit thresholds dominate those of every non-omitted row — threshold
  monotonicity (`row_orbit_mono_anchor`), nothing stronger.
-/

namespace Mordor.Profile

set_option linter.unusedSectionVars false

section Cof

variable {α : Type*} [CompleteLattice α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Input row cofactor `p⁻ᵢ = ⨆_{j ≠ i} pⱼ`. -/
def rowCof (p : ι → α) (i : ι) : α := (Finset.univ.erase i).sup p

/-- Input column cofactor `q⁻ᵢ = ⨅_{j ≠ i} qⱼ`. -/
def colCof (q : ι → α) (i : ι) : α := (Finset.univ.erase i).inf q

theorem le_rowCof (p : ι → α) {i j : ι} (h : j ≠ i) : p j ≤ rowCof p i :=
  Finset.le_sup (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩)

theorem colCof_le (q : ι → α) {i j : ι} (h : j ≠ i) : colCof q i ≤ q j :=
  Finset.inf_le (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩)

theorem rowCof_le_sup (p : ι → α) (i : ι) : rowCof p i ≤ Finset.univ.sup p :=
  Finset.sup_mono (Finset.erase_subset _ _)

theorem inf_le_colCof (q : ι → α) (i : ι) : Finset.univ.inf q ≤ colCof q i :=
  Finset.inf_mono (Finset.erase_subset _ _)

/-- Two distinct row cofactors cover the family. -/
theorem sup_le_rowCof_sup (p : ι → α) {i j : ι} (hij : i ≠ j) :
    Finset.univ.sup p ≤ rowCof p i ⊔ rowCof p j :=
  Finset.sup_le fun l _ => by
    by_cases hl : l = i
    · subst hl; exact le_sup_of_le_right (le_rowCof p hij)
    · exact le_sup_of_le_left (le_rowCof p hl)

theorem colCof_inf_le (q : ι → α) {i j : ι} (hij : i ≠ j) :
    colCof q i ⊓ colCof q j ≤ Finset.univ.inf q :=
  Finset.le_inf fun l _ => by
    by_cases hl : l = i
    · subst hl; exact inf_le_of_right_le (colCof_le q hij)
    · exact inf_le_of_left_le (colCof_le q hl)

theorem exists_third (h3 : 3 ≤ Fintype.card ι) (i l : ι) : ∃ j, j ≠ i ∧ j ≠ l := by
  by_contra h
  push_neg at h
  have hsub : (Finset.univ : Finset ι) ⊆ {i, l} := fun j _ => by
    by_cases hj : j = i
    · simp [hj]
    · simp [h j hj]
  have h1 := Finset.card_le_card hsub
  have h2 : ({i, l} : Finset ι).card ≤ 2 := (Finset.card_insert_le i {l}).trans (by simp)
  rw [Finset.card_univ] at h1
  omega

/-- **The second row cofactor family is constant** (`|ι| ≥ 3`). -/
theorem rowCof_rowCof (h3 : 3 ≤ Fintype.card ι) (p : ι → α) (i : ι) :
    rowCof (rowCof p) i = Finset.univ.sup p := by
  apply le_antisymm
  · exact Finset.sup_le fun j _ => rowCof_le_sup p j
  · refine Finset.sup_le fun l _ => ?_
    obtain ⟨j, hji, hjl⟩ := exists_third h3 i l
    exact (le_rowCof p (Ne.symm hjl)).trans (le_rowCof (rowCof p) hji)

/-- **The second column cofactor family is constant** (`|ι| ≥ 3`). -/
theorem colCof_colCof (h3 : 3 ≤ Fintype.card ι) (q : ι → α) (i : ι) :
    colCof (colCof q) i = Finset.univ.inf q := by
  apply le_antisymm
  · refine Finset.le_inf fun l _ => ?_
    obtain ⟨j, hji, hjl⟩ := exists_third h3 i l
    exact (colCof_le (colCof q) hji).trans (colCof_le q (Ne.symm hjl))
  · exact Finset.le_inf fun j _ => inf_le_colCof q j

/-- For an antichain of size `≥ 3`, each non-omitted member lies strictly below the cofactor. -/
theorem rowCof_strict (h3 : 3 ≤ Fintype.card ι) {p : ι → α} (hanti : ∀ i j, p i ≤ p j → i = j) {i j : ι}
    (h : j ≠ i) : p j < rowCof p i := by
  refine lt_of_le_of_ne (le_rowCof p h) fun he => ?_
  obtain ⟨l, hli, hlj⟩ := exists_third h3 i j
  exact hlj (hanti l j ((le_rowCof p hli).trans he.ge))

theorem colCof_strict (h3 : 3 ≤ Fintype.card ι) {q : ι → α} (hanti : ∀ i j, q i ≤ q j → i = j) {i j : ι}
    (h : j ≠ i) : colCof q i < q j := by
  refine lt_of_le_of_ne (colCof_le q h) fun he => ?_
  obtain ⟨l, hli, hlj⟩ := exists_third h3 i j
  exact hlj (hanti j l (he.ge.trans (colCof_le q hli))).symm

variable {F : α → α → α} {InD : α → Prop}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
  (hdown : ∀ x y, x ≤ y → InD y → InD x)
  (nw : ∀ x, InD x → ∀ y, ¬ InD y → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF in
/-- **An irredundant row support is an antichain.** -/
theorem support_antichain_row {s : α} {p : ι → α} (hP : s = Finset.univ.sup fun i => F (p i) s)
    (hess : ∀ i, ¬ s ≤ (Finset.univ.erase i).sup fun j => F (p j) s) : ∀ i j, p i ≤ p j → i = j := by
  intro i j hij
  by_contra hne
  refine hess i (hP.le.trans (Finset.sup_le fun l _ => ?_))
  by_cases hl : l = i
  · subst hl
    exact (hF _ _ _ _ hij le_rfl).trans
      (Finset.le_sup (f := fun j => F (p j) s) (Finset.mem_erase.2 ⟨Ne.symm hne, Finset.mem_univ _⟩))
  · exact Finset.le_sup (f := fun j => F (p j) s) (Finset.mem_erase.2 ⟨hl, Finset.mem_univ _⟩)

include hF in
/-- **An irredundant column support is an antichain.** -/
theorem support_antichain_col {r : α} {q : ι → α} (hQ : r = Finset.univ.inf fun i => F r (q i))
    (hess : ∀ i, ¬ (Finset.univ.erase i).inf (fun j => F r (q j)) ≤ r) : ∀ i j, q i ≤ q j → i = j := by
  intro i j hij
  by_contra hne
  refine hess j ((Finset.le_inf fun l _ => ?_).trans hQ.ge)
  by_cases hl : l = j
  · subst hl
    exact (Finset.inf_le (f := fun j => F r (q j)) (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)).trans
      (hF _ _ _ _ le_rfl hij)
  · exact Finset.inf_le (f := fun j => F r (q j)) (Finset.mem_erase.2 ⟨hl, Finset.mem_univ _⟩)

include nw in
/-- **Row decomposition**: `s = uᵢ ⊔ U⁻ᵢ`, both summands strictly below `s`, incomparable. -/
theorem row_cofactor_decomposition {s : α} (hs : ¬ InD s) (hsc : ∀ x, InD x → F x s ≤ s) {p : ι → α}
    (hp : ∀ i, InD (p i)) (hP : s = Finset.univ.sup fun i => F (p i) s)
    (hess : ∀ i, ¬ s ≤ (Finset.univ.erase i).sup fun j => F (p j) s) (i : ι) :
    let u := F (p i) s; let U := (Finset.univ.erase i).sup fun j => F (p j) s
    u < s ∧ U < s ∧ ¬ u ≤ U ∧ ¬ U ≤ u ∧ s = u ⊔ U := by
  intro u U
  have hu : u < s := lt_of_le_of_ne (hsc _ (hp i)) fun h => (nw _ (hp i) s hs).2 h.ge
  have hUs : U ≤ s := Finset.sup_le fun j _ => hsc _ (hp j)
  have hdec : s = u ⊔ U := le_antisymm
    (hP.le.trans (Finset.sup_le fun l _ => by
      by_cases hl : l = i
      · subst hl; exact le_sup_left
      · exact le_sup_of_le_right
          (Finset.le_sup (f := fun j => F (p j) s) (Finset.mem_erase.2 ⟨hl, Finset.mem_univ _⟩))))
    (sup_le hu.le hUs)
  refine ⟨hu, lt_of_le_of_ne hUs fun h => hess i h.ge, fun h => hess i ?_, fun h => ?_, hdec⟩
  · exact hdec.le.trans (sup_le h le_rfl)
  · exact hu.ne (le_antisymm hu.le (hdec.le.trans (sup_le le_rfl h)))

include nw in
/-- **Column decomposition**: `r = vᵢ ⊓ V⁻ᵢ`, both factors strictly above `r`, incomparable. -/
theorem column_cofactor_decomposition {r : α} (hr : InD r) (hrc : ∀ y, ¬ InD y → r ≤ F r y) {q : ι → α}
    (hq : ∀ i, ¬ InD (q i)) (hQ : r = Finset.univ.inf fun i => F r (q i))
    (hess : ∀ i, ¬ (Finset.univ.erase i).inf (fun j => F r (q j)) ≤ r) (i : ι) :
    let v := F r (q i); let V := (Finset.univ.erase i).inf fun j => F r (q j)
    r < v ∧ r < V ∧ ¬ v ≤ V ∧ ¬ V ≤ v ∧ r = v ⊓ V := by
  intro v V
  have hv : r < v := lt_of_le_of_ne (hrc _ (hq i)) fun h => (nw r hr _ (hq i)).1 h.ge
  have hrV : r ≤ V := Finset.le_inf fun j _ => hrc _ (hq j)
  have hdec : r = v ⊓ V := le_antisymm (le_inf hv.le hrV)
    ((Finset.le_inf fun l _ => by
      by_cases hl : l = i
      · subst hl; exact inf_le_left
      · exact inf_le_of_right_le
          (Finset.inf_le (f := fun j => F r (q j)) (Finset.mem_erase.2 ⟨hl, Finset.mem_univ _⟩))).trans hQ.ge)
  refine ⟨hv, lt_of_le_of_ne hrV fun h => hess i h.ge, fun h => ?_, fun h => hess i ?_, hdec⟩
  · exact hv.ne (le_antisymm hv.le ((le_inf le_rfl h).trans hdec.ge))
  · exact (le_inf h le_rfl).trans hdec.ge

include hF in
/-- **Row cofactor exchange** (`|ι| ≥ 2`, every cofactor in `D`; no regularity). -/
theorem row_cofactor_exchange [Nontrivial ι] {s : α} (hsc : ∀ x, InD x → F x s ≤ s) {p : ι → α}
    (hP : s = Finset.univ.sup fun i => F (p i) s) (hcof : ∀ i, InD (rowCof p i)) :
    s = Finset.univ.sup fun i => F (rowCof p i) s := by
  apply le_antisymm
  · refine hP.le.trans (Finset.sup_le fun l _ => ?_)
    obtain ⟨j, hj⟩ := exists_ne l
    exact (hF _ _ _ _ (le_rowCof p (Ne.symm hj)) le_rfl).trans
      (Finset.le_sup (f := fun i => F (rowCof p i) s) (Finset.mem_univ j))
  · exact Finset.sup_le fun i _ => hsc _ (hcof i)

include hF in
/-- **Column cofactor exchange** (`|ι| ≥ 2`, every cofactor outside `D`). -/
theorem column_cofactor_exchange [Nontrivial ι] {r : α} (hrc : ∀ y, ¬ InD y → r ≤ F r y) {q : ι → α}
    (hQ : r = Finset.univ.inf fun i => F r (q i)) (hcof : ∀ i, ¬ InD (colCof q i)) :
    r = Finset.univ.inf fun i => F r (colCof q i) := by
  apply le_antisymm
  · exact Finset.le_inf fun i _ => hrc _ (hcof i)
  · refine (Finset.le_inf fun l _ => ?_).trans hQ.ge
    obtain ⟨j, hj⟩ := exists_ne l
    exact (Finset.inf_le (f := fun i => F r (colCof q i)) (Finset.mem_univ j)).trans
      (hF _ _ _ _ le_rfl (colCof_le q (Ne.symm hj)))

include hF nw in
/-- **Cofactor exchange dichotomy**: each exchange succeeds, or a cofactor crosses and gives a strict cross pair
`r < F r p⁻ᵢ` (row) resp. `F q⁻ᵢ s < s` (column). -/
theorem cofactor_exchange_dichotomy [Nontrivial ι] {r s : α} (hr : InD r) (hs : ¬ InD s)
    (hsc : ∀ x, InD x → F x s ≤ s) (hrc : ∀ y, ¬ InD y → r ≤ F r y) {p q : ι → α}
    (hP : s = Finset.univ.sup fun i => F (p i) s) (hQ : r = Finset.univ.inf fun i => F r (q i)) :
    (((∀ i, InD (rowCof p i)) ∧ s = Finset.univ.sup fun i => F (rowCof p i) s) ∨
        ∃ i, ¬ InD (rowCof p i) ∧ r < F r (rowCof p i)) ∧
      (((∀ i, ¬ InD (colCof q i)) ∧ r = Finset.univ.inf fun i => F r (colCof q i)) ∨
        ∃ i, InD (colCof q i) ∧ F (colCof q i) s < s) := by
  constructor
  · by_cases h : ∀ i, InD (rowCof p i)
    · exact Or.inl ⟨h, row_cofactor_exchange hF hsc hP h⟩
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      exact Or.inr ⟨i, hi, lt_of_le_of_ne (hrc _ hi) fun he => (nw r hr _ hi).1 he.ge⟩
  · by_cases h : ∀ i, ¬ InD (colCof q i)
    · exact Or.inl ⟨h, column_cofactor_exchange hF hrc hQ h⟩
    · push_neg at h
      obtain ⟨i, hi⟩ := h
      exact Or.inr ⟨i, hi, lt_of_le_of_ne (hsc _ hi) fun he => (nw _ hi s hs).2 he.ge⟩

include hF nw in
theorem family_join_out {s : α} (hs : ¬ InD s) {p : ι → α} (hP : s = Finset.univ.sup fun i => F (p i) s) :
    ¬ InD (Finset.univ.sup p) := fun hin =>
  (nw _ hin s hs).2 (hP.le.trans (Finset.sup_le fun _ hi => hF _ _ _ _ (Finset.le_sup hi) le_rfl))

include hF nw in
theorem family_meet_in {r : α} (hr : InD r) {q : ι → α} (hQ : r = Finset.univ.inf fun i => F r (q i)) :
    InD (Finset.univ.inf q) := by
  by_contra hout
  exact (nw r hr _ hout).1 ((Finset.le_inf fun i hi => hF _ _ _ _ le_rfl (Finset.inf_le hi)).trans hQ.ge)

include hF nw in
/-- **Termination of cofactor exchange** (`|ι| ≥ 3`): after one exchange, the next cofactor family is the constant
`⨆ p ∉ D` (rows) resp. `⨅ q ∈ D` (columns), so the second exchange crosses at every index. -/
theorem second_cofactor_crosses (h3 : 3 ≤ Fintype.card ι) {r s : α} (hr : InD r) (hs : ¬ InD s) {p q : ι → α}
    (hP : s = Finset.univ.sup fun i => F (p i) s) (hQ : r = Finset.univ.inf fun i => F r (q i)) :
    (∀ i, ¬ InD (rowCof (rowCof p) i)) ∧ ∀ i, InD (colCof (colCof q) i) :=
  ⟨fun i => by rw [rowCof_rowCof h3]; exact family_join_out hF nw hs hP,
   fun i => by rw [colCof_colCof h3]; exact family_meet_in hF nw hr hQ⟩

include hF hdown nw in
/-- **Stable row cofactors lie under distinct generators.** -/
theorem cofactor_petal_injective {κ : Type*} (g : κ → α) (hg : ∀ k, InD (g k)) {s : α} (hs : ¬ InD s)
    {p : ι → α} (hP : s = Finset.univ.sup fun i => F (p i) s) (σ : ι → κ) (hσ : ∀ i, rowCof p i ≤ g (σ i)) :
    Function.Injective σ := by
  intro i j hij
  by_contra hne
  have h : Finset.univ.sup p ≤ g (σ i) :=
    (sup_le_rowCof_sup p hne).trans (sup_le (hσ i) (hij ▸ hσ j))
  exact family_join_out hF nw hs hP (hdown _ _ h (hg _))

include hF hdown nw in
/-- **Cardinality bound**: in `D = ⋃ₖ ↓gₖ`, a row support whose cofactors all stay in `D` has at most `k` members. -/
theorem cofactor_stable_card {κ : Type*} [Fintype κ] (g : κ → α) (hg : ∀ k, InD (g k))
    (hgen : ∀ x, InD x → ∃ k, x ≤ g k) {s : α} (hs : ¬ InD s) {p : ι → α}
    (hP : s = Finset.univ.sup fun i => F (p i) s) (hcof : ∀ i, InD (rowCof p i)) :
    Fintype.card ι ≤ Fintype.card κ := by
  choose σ hσ using fun i => hgen _ (hcof i)
  exact Fintype.card_le_of_injective σ (cofactor_petal_injective hF hdown nw g hg hs hP σ hσ)

include hF hdown in
/-- **Stable supports sit under co-meets of petals**, and the co-meets are a row support. -/
theorem cofactor_stable_comeets [Nontrivial ι] {κ : Type*} (g : κ → α) (hg : ∀ k, InD (g k)) {s : α}
    (hsc : ∀ x, InD x → F x s ≤ s) {p : ι → α} (hP : s = Finset.univ.sup fun i => F (p i) s) (σ : ι → κ)
    (hσ : ∀ i, rowCof p i ≤ g (σ i)) :
    (∀ j, p j ≤ (Finset.univ.erase j).inf (g ∘ σ)) ∧
      s = Finset.univ.sup fun j => F ((Finset.univ.erase j).inf (g ∘ σ)) s := by
  have hle : ∀ j, p j ≤ (Finset.univ.erase j).inf (g ∘ σ) := fun j =>
    Finset.le_inf fun i hi => (le_rowCof p (Finset.ne_of_mem_erase hi).symm).trans (hσ i)
  have hin : ∀ j, InD ((Finset.univ.erase j).inf (g ∘ σ)) := fun j => by
    obtain ⟨i, hi⟩ := exists_ne j
    exact hdown _ _ (Finset.inf_le (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩)) (hg (σ i))
  refine ⟨hle, le_antisymm (hP.le.trans (Finset.sup_le fun j hj => ?_)) (Finset.sup_le fun j _ => hsc _ (hin j))⟩
  exact (hF _ _ _ _ (hle j) le_rfl).trans
    (Finset.le_sup (f := fun j => F ((Finset.univ.erase j).inf (g ∘ σ)) s) hj)

include hF in
/-- Row orbits are monotone in the anchor. -/
theorem row_orbit_mono_anchor {a a' : α} (h : a ≤ a') (m : ℕ) : rowOrbit F a m ≤ rowOrbit F a' m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    unfold rowOrbit at *
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hF _ _ _ _ h ih

include hF hdown in
/-- **Cofactor thresholds** (`j ≠ i`): the cofactor row keeps every column-orbit containment, every row-orbit
containment and every outside row-orbit point of row `j`. These are threshold monotonicity for `pⱼ ≤ p⁻ᵢ`. -/
theorem cofactor_threshold (p : ι → α) {i j : ι} (h : j ≠ i) (b : α) :
    (∀ n, colOrbit F b n ≤ p j → colOrbit F b n ≤ rowCof p i) ∧
      (∀ m, b ≤ rowOrbit F (p j) m → b ≤ rowOrbit F (rowCof p i) m) ∧
      (∀ m, InD (rowOrbit F (rowCof p i) m) → InD (rowOrbit F (p j) m)) :=
  ⟨fun _ hc => hc.trans (le_rowCof p h),
   fun m hb => hb.trans (row_orbit_mono_anchor hF (le_rowCof p h) m),
   fun m hin => hdown _ _ (row_orbit_mono_anchor hF (le_rowCof p h) m) hin⟩

end Cof

end Mordor.Profile
