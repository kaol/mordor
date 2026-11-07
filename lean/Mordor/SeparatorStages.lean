import Mordor.ExtremalSeparators

/-!
# The extremal-separator refinement process (round 26, §34.3z¹²¹)

ChatGPT brief "uniform termination of extremal-separator refinement", Deliverables 1–3.

* `meetClose S`: the meets of all subsets of `S` (`∅.inf = ⊤`); finite, meet-closed, contains `S` and `⊤`.
* `Separated T x y`: some `s ∈ T` with `F x y ≤ s`, `y ≰ s`. `Bad T x y`: a cross pair of `T` not separated by `T`.
  `IsMaxSep x y s`: `F x y ≤ s`, `y ≰ s`, and `y ≤ t` for all `t > s` (a maximal upper separator).
* `Step T T'`: `T' = meetClose (T ∪ S)` where `S` consists of maximal separators of bad pairs of `T` and contains one
  for each bad pair (the choice is left open: this is the *existential* reading of a stage).
* `Run T`: `T 0 = {⊥, ⊤}`, and each stage is either terminal (no bad pair) and repeated, or followed by a `Step`.
* Deliverable 2: `run_closed` (every stage is meet-closed and contains `⊥, ⊤`; finiteness is the type `Finset`),
  `separated_mono` / `run_mono` (separations persist), `step_separates` (bad pairs are separated at the next stage),
  `step_strict` (a stage with a bad pair strictly grows).
* `step_exists` (ACC, no witness): every finite `T` has a `Step`.
* `terminal_witness`: a stage with no bad pair forces a witness (`separating_family_witness`); a *stuck* bad pair
  (`y ≤ F x y`) is a witness by definition.
* `bad_after_step_new`, `new_element_below_separator` (**causal chain**): a bad pair of stage `n + 1` involves an
  element of `Tₙ₊₁ ∖ Tₙ`, and every such element lies below a separator chosen at stage `n`. So a run of `N` stages
  carries a chain of separators `s₀, …, s_{N-1}`, `sₙ` separating a bad pair `(xₙ, yₙ)` (`F xₙ yₙ ≤ sₙ`, `yₙ ≰ sₙ`),
  with `xₙ₊₁ ≤ sₙ` or `yₙ₊₁ ≤ sₙ`.
* `cut_of_terminal_run` (**existential stage bound ⇒ Cut**): if some run reaches a terminal or stuck stage, `F` has a
  witness. `no_witness_strictMono` + `exists_run` (ACC): without a witness every run grows strictly at every stage, and
  a run exists — an infinite strictly increasing sequence of finite meet-closed families.
-/

namespace Mordor.SeparatorStages
open Finset Mordor.FiniteQuotient

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] [DecidableEq α]

/-- Meets of all subsets. -/
def meetClose (S : Finset α) : Finset α := S.powerset.image fun A => A.inf id

theorem subset_meetClose (S : Finset α) : S ⊆ meetClose S := fun s hs =>
  Finset.mem_image.2 ⟨{s}, Finset.mem_powerset.2 (Finset.singleton_subset_iff.2 hs), by simp⟩

theorem top_mem_meetClose (S : Finset α) : ⊤ ∈ meetClose S :=
  Finset.mem_image.2 ⟨∅, Finset.empty_mem_powerset S, by simp⟩

theorem meetClose_closed (S : Finset α) : ∀ a ∈ meetClose S, ∀ b ∈ meetClose S, a ⊓ b ∈ meetClose S := by
  intro a ha b hb
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hb
  refine Finset.mem_image.2 ⟨A ∪ B, Finset.mem_powerset.2 (Finset.union_subset (Finset.mem_powerset.1 hA)
    (Finset.mem_powerset.1 hB)), ?_⟩
  rw [Finset.inf_union]

variable (F : α → α → α) (D : Set α)

/-- `T` separates the pair. -/
def Separated (T : Finset α) (x y : α) : Prop := ∃ s ∈ T, F x y ≤ s ∧ ¬ y ≤ s

/-- A cross pair of `T` that `T` does not separate. -/
def Bad (T : Finset α) (x y : α) : Prop := x ∈ T ∧ x ∈ D ∧ y ∈ T ∧ y ∉ D ∧ ¬ Separated F T x y

/-- A maximal upper separator. -/
def IsMaxSep (x y s : α) : Prop := F x y ≤ s ∧ ¬ y ≤ s ∧ ∀ t, s < t → y ≤ t

/-- One refinement stage (existential in the separator choice). -/
def Step (T T' : Finset α) : Prop :=
  ∃ S : Finset α, T' = meetClose (T ∪ S) ∧ (∀ s ∈ S, ∃ x y, Bad F D T x y ∧ IsMaxSep F x y s) ∧
    ∀ x y, Bad F D T x y → ∃ s ∈ S, IsMaxSep F x y s

/-- A run of the process. -/
def Run (T : ℕ → Finset α) : Prop :=
  T 0 = {⊥, ⊤} ∧ ∀ n, ((∀ x y, ¬ Bad F D (T n) x y) ∧ T (n + 1) = T n) ∨ Step F D (T n) (T (n + 1))

variable {F D}

theorem separated_mono {T T' : Finset α} (h : T ⊆ T') {x y : α} : Separated F T x y → Separated F T' x y :=
  fun ⟨s, hs, h1, h2⟩ => ⟨s, h hs, h1, h2⟩

theorem step_subset {T T' : Finset α} (h : Step F D T T') : T ⊆ T' := by
  obtain ⟨S, rfl, -, -⟩ := h
  exact Finset.subset_union_left.trans (subset_meetClose _)

theorem step_separates {T T' : Finset α} (h : Step F D T T') {x y : α} (hb : Bad F D T x y) :
    Separated F T' x y := by
  obtain ⟨S, rfl, -, hall⟩ := h
  obtain ⟨s, hs, hF, hy, -⟩ := hall x y hb
  exact ⟨s, subset_meetClose _ (Finset.mem_union_right _ hs), hF, hy⟩

theorem step_strict {T T' : Finset α} (h : Step F D T T') {x y : α} (hb : Bad F D T x y) : T ⊂ T' := by
  refine Finset.ssubset_iff_subset_ne.2 ⟨step_subset h, fun he => hb.2.2.2.2 ?_⟩
  rw [he]; exact step_separates h hb

theorem run_mono {T : ℕ → Finset α} (hr : Run F D T) : Monotone T := by
  refine monotone_nat_of_le_succ fun n => ?_
  rcases hr.2 n with ⟨-, he⟩ | hs
  · rw [he]
  · exact step_subset hs

theorem run_closed {T : ℕ → Finset α} (hr : Run F D T) (n : ℕ) :
    ⊥ ∈ T n ∧ ⊤ ∈ T n ∧ ∀ a ∈ T n, ∀ b ∈ T n, a ⊓ b ∈ T n := by
  induction n with
  | zero =>
    rw [hr.1]
    refine ⟨by simp, by simp, fun a ha b hb => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb ⊢
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  | succ n ih =>
    rcases hr.2 n with ⟨-, he⟩ | ⟨S, he, -, -⟩
    · rw [he]; exact ih
    · rw [he]
      exact ⟨subset_meetClose _ (Finset.mem_union_left _ ih.1), top_mem_meetClose _, meetClose_closed _⟩

/-- **Causal chain, part 1.** A bad pair of the next stage involves an element created by the step. -/
theorem bad_after_step_new {T T' : Finset α} (h : Step F D T T') {x y : α} (hb : Bad F D T' x y) :
    x ∉ T ∨ y ∉ T := by
  by_contra hc
  push_neg at hc
  obtain ⟨hxT, hyT⟩ := hc
  by_cases hbad : Bad F D T x y
  · exact hb.2.2.2.2 (step_separates h hbad)
  · have hsep : Separated F T x y := by
      by_contra hs; exact hbad ⟨hxT, hb.2.1, hyT, hb.2.2.2.1, hs⟩
    exact hb.2.2.2.2 (separated_mono (step_subset h) hsep)

/-- **Causal chain, part 2.** An element created by a step (in a meet-closed `T ∋ ⊤`) lies below one of the new
separators: it is the meet of a set meeting the separator set `S`. -/
theorem new_element_below_separator {T T' : Finset α} (hcl : ∀ a ∈ T, ∀ b ∈ T, a ⊓ b ∈ T) (htT : ⊤ ∈ T)
    (h : Step F D T T') {e : α} (he : e ∈ T') (heT : e ∉ T) :
    ∃ s, (∃ x y, Bad F D T x y ∧ IsMaxSep F x y s) ∧ e ≤ s := by
  classical
  obtain ⟨S, rfl, hS, -⟩ := h
  obtain ⟨A, hA, rfl⟩ := Finset.mem_image.1 he
  have hA' := Finset.mem_powerset.1 hA
  by_cases hAS : ∃ s ∈ A, s ∈ S ∧ s ∉ T
  · obtain ⟨s, hsA, hsS, -⟩ := hAS
    exact ⟨s, hS s hsS, Finset.inf_le hsA⟩
  · push_neg at hAS
    exfalso; apply heT
    have hsub : A ⊆ T := fun a ha => by
      rcases Finset.mem_union.1 (hA' ha) with h1 | h1
      · exact h1
      · exact hAS a ha h1
    exact Mordor.FiniteQuotient.inf_mem_of_closed htT hcl A hsub

variable [DecidableLE α]

/-- A terminal stage forces a witness. -/
theorem terminal_witness (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) {T : Finset α} (hbT : ⊥ ∈ T)
    (htT : ⊤ ∈ T) (hcl : ∀ a ∈ T, ∀ b ∈ T, a ⊓ b ∈ T) (hterm : ∀ x y, ¬ Bad F D T x y) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  by_contra hno
  push_neg at hno
  refine separating_family_witness hF hD hbot htop (fun x hx y hy => ⟨(hno x hx y hy).1, (hno x hx y hy).2⟩)
    hbT htT hcl fun x hxT hx y hyT hy => ?_
  by_contra hs
  exact hterm x y ⟨hxT, hx, hyT, hy, hs⟩

/-- **Existential stage bound ⇒ Cut.** A run that reaches a terminal stage, or a stuck bad pair, gives a witness. -/
theorem cut_of_terminal_run (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) {T : ℕ → Finset α} (hr : Run F D T)
    {N : ℕ} (hN : (∀ x y, ¬ Bad F D (T N) x y) ∨ ∃ x y, Bad F D (T N) x y ∧ y ≤ F x y) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  obtain ⟨hb, ht, hc⟩ := run_closed hr N
  rcases hN with h | ⟨x, y, hxy, hst⟩
  · exact terminal_witness hF hD hbot htop hb ht hc h
  · exact ⟨x, hxy.2.1, y, hxy.2.2.2.1, Or.inr hst⟩

/-- **No witness: every run grows strictly at every stage.** -/
theorem no_witness_strictMono (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {T : ℕ → Finset α} (hr : Run F D T) : StrictMono T := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  obtain ⟨hb, ht, hc⟩ := run_closed hr n
  have hbad : ∃ x y, Bad F D (T n) x y := by
    by_contra h; push_neg at h
    obtain ⟨x, hx, y, hy, hw⟩ := terminal_witness hF hD hbot htop hb ht hc h
    rcases hw with h' | h'
    · exact (nw x hx y hy).1 h'
    · exact (nw x hx y hy).2 h'
  obtain ⟨x, y, hxy⟩ := hbad
  rcases hr.2 n with ⟨h, -⟩ | hs
  · exact absurd hxy (h x y)
  · exact step_strict hs hxy

/-- Every finite family has a refinement step (ACC, no witness). -/
theorem step_exists [WellFoundedGT α] (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (T : Finset α) :
    ∃ T', Step F D T T' := by
  classical
  have hsep : ∀ p : α × α, ∃ s, Bad F D T p.1 p.2 → IsMaxSep F p.1 p.2 s := fun p => by
    by_cases hb : Bad F D T p.1 p.2
    · obtain ⟨s, h1, h2, h3⟩ := Mordor.ExtremalSeparators.exists_upper_separator nw hb.2.1 hb.2.2.2.1
      exact ⟨s, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨⊤, fun h => absurd h hb⟩
  choose sep hsep using hsep
  let P := (T ×ˢ T).filter fun p => Bad F D T p.1 p.2
  refine ⟨meetClose (T ∪ P.image sep), P.image sep, rfl, fun s hs => ?_, fun x y hb => ?_⟩
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hs
    have hb := (Finset.mem_filter.1 hp).2
    exact ⟨p.1, p.2, hb, hsep p hb⟩
  · refine ⟨sep (x, y), Finset.mem_image.2 ⟨(x, y), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hb.1, hb.2.2.1⟩, hb⟩,
      rfl⟩, hsep (x, y) hb⟩

/-- **An infinite run exists** (ACC, no witness): an infinite strictly increasing sequence of finite meet-closed
families, each obtained from the last by maximal separators of all its bad pairs. -/
theorem exists_run [WellFoundedGT α] (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) : ∃ T : ℕ → Finset α, Run F D T ∧ StrictMono T := by
  classical
  choose nxt hnxt using step_exists (F := F) (D := D) nw
  let T : ℕ → Finset α := fun n => nxt^[n] {⊥, ⊤}
  have hr : Run F D T := ⟨rfl, fun n => Or.inr (by
    show Step F D (nxt^[n] {⊥, ⊤}) (nxt^[n + 1] {⊥, ⊤})
    rw [Function.iterate_succ_apply']; exact hnxt _)⟩
  exact ⟨T, hr, no_witness_strictMono hF hD hbot htop nw hr⟩

end Mordor.SeparatorStages
