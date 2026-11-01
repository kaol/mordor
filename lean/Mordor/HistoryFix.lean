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

/-- **The terminal step** (§34.3z⁶⁹). At a label fixed point `K` of a column `y ∉ D`, the row `⋀_K p` steps
sideways (`fixed_sideways`), and its value `v = F (⋀_K p) y` has labels a **proper** subset of `K` (empty when
`v ∉ D`). The history meet `y ⊓ v` lies below `v`, so `lab v ⊆ K`; equality would put `v` below `⋀_K p`, a
witness. -/
theorem terminal_step {y : α} (hy : ¬ ∃ j, y ≤ p j) {K : Finset ι} (hne : K.Nonempty)
    (hK : lab p (zK F p y K) = K) :
    lab p (F (K.inf p) y) ⊂ K := by
  have hsub : lab p (F (K.inf p) y) ⊆ K := fun i hi => by
    rw [← hK]; exact mem_lab.2 (inf_le_right.trans (mem_lab.1 hi))
  refine Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun heq => ?_⟩
  obtain ⟨i, hi⟩ := hne
  have hle : F (K.inf p) y ≤ K.inf p := Finset.le_inf fun j hj => mem_lab.1 (heq.symm ▸ hj)
  exact (nw _ ⟨i, Finset.inf_le hi⟩ y hy).1 hle

/-- **A singleton label fixed point forces an outside sideways step**: if `lab (y ⊓ F pᵢ y) = {i}`, then
`F pᵢ y ∉ D` and `F pᵢ y ≰ y`. So a terminal column with a singleton fixed label continues the feedback ray sideways
by the generator row `pᵢ`. -/
theorem singleton_step {y : α} (hy : ¬ ∃ j, y ≤ p j) {i : ι} (hK : lab p (zK F p y {i}) = {i}) :
    (¬ ∃ j, F (p i) y ≤ p j) ∧ ¬ F (p i) y ≤ y := by
  have hside := fixed_sideways hF nw hy (Finset.singleton_nonempty i) hK
  rw [Finset.inf_singleton] at hside
  refine ⟨fun hv => ?_, hside⟩
  have := terminal_step hF nw hy (Finset.singleton_nonempty i) hK
  rw [Finset.ssubset_singleton_iff, Finset.inf_singleton] at this
  obtain ⟨j, hj⟩ := hv
  have hjK : j ∈ lab p (F (p i) y) := mem_lab.2 hj
  rw [this] at hjK
  exact Finset.notMem_empty _ hjK

/-- **Terminal descent** (§34.3z⁷⁰, DCC). Below every column `q ∉ D` there is a terminal column `y ≤ q`
(`y ∉ D` and `y ⊓ gⱼ y ∈ D` for every `j`). If `q` is not terminal, some meet `q ⊓ gⱼ q` lies outside `D`, and it is
strictly below `q` because `q ≰ gⱼ q` (no-witness). If a row `r ≤ ⋀ p` contracts at `q`, it contracts at the
terminal column too. -/
theorem terminal_below [WellFoundedLT α] {r : α} (hr : ∀ j, r ≤ p j) :
    ∀ q, (¬ ∃ j, q ≤ p j) → F r q ≤ q →
      ∃ y, y ≤ q ∧ (¬ ∃ j, y ≤ p j) ∧ F r y ≤ y ∧ ∀ j, ∃ k, y ⊓ F (p j) y ≤ p k := by
  intro q
  induction q using WellFoundedLT.induction with
  | _ q ih =>
    intro hq hrq
    by_cases ht : ∀ j, ∃ k, q ⊓ F (p j) q ≤ p k
    · exact ⟨q, le_rfl, hq, hrq, ht⟩
    · push_neg at ht
      obtain ⟨j, hj⟩ := ht
      have hjD : ¬ ∃ k, q ⊓ F (p j) q ≤ p k := fun ⟨k, hk⟩ => hj k hk
      have hlt : q ⊓ F (p j) q < q :=
        lt_of_le_of_ne inf_le_left fun heq => (nw (p j) ⟨j, le_rfl⟩ q hq).2 (heq.symm.le.trans inf_le_right)
      have hrw : F r (q ⊓ F (p j) q) ≤ q ⊓ F (p j) q :=
        le_inf ((hF _ _ _ _ le_rfl inf_le_left).trans hrq) (hF _ _ _ _ (hr j) inf_le_left)
      obtain ⟨y, hyw, h1, h2, h3⟩ := ih _ hlt hjD hrw
      exact ⟨y, hyw.trans inf_le_left, h1, h2, h3⟩

/-- Terminal descent without a contracting row. -/
theorem terminal_below' [WellFoundedLT α] :
    ∀ q, (¬ ∃ j, q ≤ p j) → ∃ y, y ≤ q ∧ (¬ ∃ j, y ≤ p j) ∧ ∀ j, ∃ k, y ⊓ F (p j) y ≤ p k := by
  intro q
  induction q using WellFoundedLT.induction with
  | _ q ih =>
    intro hq
    by_cases ht : ∀ j, ∃ k, q ⊓ F (p j) q ≤ p k
    · exact ⟨q, le_rfl, hq, ht⟩
    · push_neg at ht
      obtain ⟨j, hj⟩ := ht
      have hlt : q ⊓ F (p j) q < q :=
        lt_of_le_of_ne inf_le_left fun heq => (nw (p j) ⟨j, le_rfl⟩ q hq).2 (heq.symm.le.trans inf_le_right)
      obtain ⟨y, hyw, h1, h2⟩ := ih _ hlt fun ⟨k, hk⟩ => hj k hk
      exact ⟨y, hyw.trans inf_le_left, h1, h2⟩

/-! ### Terminal-shadow continuation and certificate joins (§34.3z⁷¹) -/

omit hF nw in
/-- Labels of a join are the intersection of labels. -/
theorem lab_sup (a b : α) : lab p (a ⊔ b) = lab p a ∩ lab p b := by
  ext i; simp only [mem_lab, Finset.mem_inter, sup_le_iff]

omit hF nw in
/-- **Below a meet row iff the labels contain its index set.** So `c ≤ ⋀_S p` is a label condition. -/
theorem le_meet_iff (c : α) (S : Finset ι) : c ≤ S.inf p ↔ S ⊆ lab p c := by
  rw [Finset.le_inf_iff]; exact ⟨fun h i hi => mem_lab.2 (h i hi), fun h i hi => mem_lab.1 (h hi)⟩

omit hF nw in
/-- An element is in `D` iff its label is nonempty. -/
theorem mem_D_iff (c : α) : (∃ j, c ≤ p j) ↔ (lab p c).Nonempty :=
  ⟨fun ⟨j, hj⟩ => ⟨j, mem_lab.2 hj⟩, fun ⟨j, hj⟩ => ⟨j, mem_lab.1 hj⟩⟩

/-- **Shadow escape** (a consequence of `Crossing.no_closed_rows`). If the meet row `⋀_K p` takes at the outside
column `q` a value whose labels lie in `K`, then either that value is outside `D`, or some generator row `pᵢ` with
`i` in its label escapes `D` at `q`, above it. -/
theorem shadow_escape {q : α} (hq : ¬ ∃ j, q ≤ p j) {K : Finset ι} (hsub : lab p (F (K.inf p) q) ⊆ K) :
    (¬ ∃ j, F (K.inf p) q ≤ p j) ∨
      ∃ i ∈ lab p (F (K.inf p) q), (¬ ∃ j, F (p i) q ≤ p j) ∧ F (K.inf p) q ≤ F (p i) q := by
  classical
  by_cases hw : ∃ j, F (K.inf p) q ≤ p j
  · right
    set M := lab p (F (K.inf p) q)
    have hMne : M.Nonempty := (mem_D_iff _).1 hw
    have hle : ∀ i ∈ M, F (K.inf p) q ≤ F (p i) q := fun i hi =>
      hF _ _ _ _ (Finset.inf_le (hsub hi)) le_rfl
    by_contra hno
    push_neg at hno
    refine Crossing.no_closed_rows hF p hq nw M hMne fun i hi => ?_
    have hex : ∃ j, F (p i) q ≤ p j := by
      by_contra h; push_neg at h; exact hno i hi h (hle i hi)
    obtain ⟨j, hj⟩ := hex
    exact ⟨j, mem_lab.2 ((hle i hi).trans hj), hj⟩
  · exact Or.inl hw

/-- **Terminal-shadow continuation.** If `y ≤ q` carries a label fixed point `K`, the feedback from `q` continues
by `⋀_K p` or by a generator row `pᵢ` with `i` in the label of `F (⋀_K p) y` (a proper subset of `K`), and the new
column lies above the certificate `a = y ⊓ F (⋀_K p) y`. -/
theorem terminal_shadow_escape {y q : α} (hyq : y ≤ q) (hy : ¬ ∃ j, y ≤ p j) (hq : ¬ ∃ j, q ≤ p j)
    {K : Finset ι} (hne : K.Nonempty) (hK : lab p (zK F p y K) = K) :
    ∃ r, (r = K.inf p ∨ ∃ i ∈ lab p (F (K.inf p) y), r = p i) ∧ (¬ ∃ j, F r q ≤ p j) ∧
      zK F p y K ≤ F r q := by
  have hvw : F (K.inf p) y ≤ F (K.inf p) q := hF _ _ _ _ le_rfl hyq
  have hlab : lab p (F (K.inf p) q) ⊆ lab p (F (K.inf p) y) := fun i hi => mem_lab.2 (hvw.trans (mem_lab.1 hi))
  have hstep := (terminal_step hF nw hy hne hK).1
  rcases shadow_escape hF nw hq (hlab.trans hstep) with hout | ⟨i, hi, hout, hle⟩
  · exact ⟨_, Or.inl rfl, hout, inf_le_right.trans hvw⟩
  · exact ⟨_, Or.inr ⟨i, hlab hi, rfl⟩, hout, inf_le_right.trans (hvw.trans hle)⟩

omit hF nw in
/-- **The certificate lies below both consecutive columns**: `a = y ⊓ F (⋀_K p) y ≤ q` (as `y ≤ q`), and
`a ≤ F r q` by `terminal_shadow_escape`. -/
theorem certificate_below {y q z : α} (hyq : y ≤ q) {K : Finset ι} (hz : zK F p y K ≤ z) :
    zK F p y K ≤ q ⊓ z :=
  le_inf (inf_le_left.trans hyq) hz

omit hF nw in
/-- **Certificate join.** Two certificates below a common column `q` join below `q`, with label the intersection of
their labels; the join is in `D` iff the labels meet. -/
theorem certificate_join {a a' q : α} {K K' : Finset ι} (ha : a ≤ q) (ha' : a' ≤ q) (hK : lab p a = K)
    (hK' : lab p a' = K') :
    a ⊔ a' ≤ q ∧ lab p (a ⊔ a') = K ∩ K' ∧ ((∃ j, a ⊔ a' ≤ p j) ↔ (K ∩ K').Nonempty) := by
  refine ⟨sup_le ha ha', by rw [lab_sup, hK, hK'], ?_⟩
  rw [mem_D_iff, lab_sup, hK, hK']

end Mordor.HistoryFix
