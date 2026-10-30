import Mordor.CLL
import Mordor.MinSwitch
import Mathlib.Order.WithBot

/-!
# Infinite column posets for CLL (log §34.3z⁴³)

* **DCC alone does not suffice for chain-dependent CLL** (`not_cll_dcc`). On `C = WithTop Gap`, where `Gap` is `ℕ` with
  `n < m ↔ n + 2 ≤ m` (DCC, infinite ascending chains), the column labels `z σ = max σ + 1` (`⊤ ∉ σ`),
  `z σ = max σ + 3` (`⊤ ∈ σ ≠ {⊤}`), `z {⊤} = 0` form a `CLL.Labelling 1 C`. So a theorem
  `∀ C [OrderTop C] [WellFoundedLT C], Labelling k C → False` is false already for `k = 1`.
* **Max-only labellings.** FG∞ (and `CLL.cut_of_meets`) only ever uses labels `z(A, σ) = w(A, max σ)`. A
  `MaxLabelling` turns into a `Labelling` through `cmax` (`MaxLabelling.toLabelling`), so finite CLL covers it.
  For `k = 1`, DCC already suffices (`cll_max_one`), by descent: the column map `g` with `t ≰ g t` has a minimal
  `t` with `g t ≤ t`, and then `g t = t` (`column_descent`).
* **The minimal terminal meet lies in `D`** (`terminal_meet_le_p2`). At a terminal state `x` that is minimal for the
  triple-meet row `r = p₁ ⊓ p₂ ⊓ p₃` among columns outside `D` (`HistoryFix.min_terminal`), the meet
  `w = x ⊓ g₂ x` of case II is below `p₂`: otherwise `F r w ≤ F r x ≤ w` contradicts minimality.
-/

namespace Mordor.InfiniteCLL
open Finset Classical Mordor.CLL
set_option linter.unusedSectionVars false

/-! ### The gap order -/

/-- `ℕ` with `n < m ↔ n + 2 ≤ m`. -/
@[ext] structure Gap where
  n : ℕ

instance : PartialOrder Gap where
  le a b := a.n = b.n ∨ a.n + 2 ≤ b.n
  le_refl a := Or.inl rfl
  le_trans _ _ _ hab hbc := by
    rcases hab with h | h <;> rcases hbc with h' | h'
    · exact Or.inl (h.trans h')
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  le_antisymm a b hab hba := by
    rcases hab with h | h <;> rcases hba with h' | h'
    · exact Gap.ext h
    · exact Gap.ext h
    · exact Gap.ext (by omega)
    · exact absurd h' (by omega)

theorem gap_le {a b : Gap} : a ≤ b ↔ a.n = b.n ∨ a.n + 2 ≤ b.n := Iff.rfl

theorem gap_lt_n {a b : Gap} (h : a < b) : a.n < b.n := by
  obtain ⟨h1, h2⟩ := lt_iff_le_not_ge.1 h
  rcases h1 with h | h
  · exact absurd (Or.inl h.symm) h2
  · omega

instance : WellFoundedLT Gap :=
  ⟨Subrelation.wf (fun h => gap_lt_n h) (InvImage.wf Gap.n wellFounded_lt)⟩

abbrev C := WithTop Gap

/-- The level of a column (`⊤ ↦ 0`). -/
def lvl (c : C) : ℕ := (WithTop.untopD ⟨0⟩ c).n

/-- The top level among the non-top columns of `σ`. -/
noncomputable def L (σ : Finset C) : ℕ := (σ.filter (· ≠ ⊤)).sup lvl

/-- The label: `L σ + 1` without `⊤`, `L σ + 3` with `⊤` and another column, `0` at `{⊤}`. -/
noncomputable def val (σ : Finset C) : C :=
  if (⊤ : C) ∈ σ then (if σ = {⊤} then ((⟨0⟩ : Gap) : C) else ((⟨L σ + 3⟩ : Gap) : C))
  else ((⟨L σ + 1⟩ : Gap) : C)

theorem exists_top_level {σ : Finset C} (h : (σ.filter (· ≠ ⊤)).Nonempty) :
    ∃ g : Gap, (g : C) ∈ σ ∧ g.n = L σ := by
  obtain ⟨y, hy, he⟩ := Finset.exists_mem_eq_sup _ h lvl
  obtain ⟨hyσ, hyt⟩ := mem_filter.1 hy
  obtain ⟨g, rfl⟩ := WithTop.ne_top_iff_exists.1 hyt
  exact ⟨g, hyσ, by rw [L, he]; rfl⟩

theorem lvl_le_L {σ : Finset C} {g : Gap} (h : (g : C) ∈ σ) : g.n ≤ L σ :=
  Finset.le_sup (f := lvl) (mem_filter.2 ⟨h, WithTop.coe_ne_top⟩)

/-- Along an inclusion into a chain, the top level stays or jumps by at least two. -/
theorem L_step {σ σ' : Finset C} (hs : σ ⊆ σ') (hch : IsChain (· ≤ ·) (σ' : Set C))
    (hne : (σ.filter (· ≠ ⊤)).Nonempty) : L σ = L σ' ∨ L σ + 2 ≤ L σ' := by
  obtain ⟨g, hg, he⟩ := exists_top_level hne
  have hne' : (σ'.filter (· ≠ ⊤)).Nonempty := hne.mono (filter_subset_filter _ hs)
  obtain ⟨g', hg', he'⟩ := exists_top_level hne'
  have hle : g.n ≤ g'.n := he' ▸ lvl_le_L (hs hg)
  by_cases hgg : (g : C) = g'
  · left; rw [← he, ← he', WithTop.coe_inj.1 hgg]
  rcases hch (hs hg) hg' hgg with h | h
  · rcases (WithTop.coe_le_coe.1 h) with h | h
    · left; rw [← he, ← he', h]
    · right; omega
  · rcases (WithTop.coe_le_coe.1 h) with h | h
    · left; rw [← he, ← he', h]
    · omega

theorem val_mono {σ σ' : Finset C} (hs : σ ⊆ σ') (hne : σ.Nonempty) (hch : IsChain (· ≤ ·) (σ' : Set C)) :
    val σ ≤ val σ' := by
  unfold val
  by_cases ht : (⊤ : C) ∈ σ
  · have ht' : (⊤ : C) ∈ σ' := hs ht
    rw [if_pos ht, if_pos ht']
    by_cases h1 : σ = {⊤}
    · rw [if_pos h1]
      split_ifs
      · exact le_rfl
      · exact WithTop.coe_le_coe.2 (Or.inr (by simp))
    · have hne1 : (σ.filter (· ≠ ⊤)).Nonempty := by
        obtain ⟨y, hy, hyt⟩ : ∃ y ∈ σ, y ≠ ⊤ := by
          by_contra hno; push_neg at hno
          exact h1 (Finset.eq_singleton_iff_unique_mem.2 ⟨ht, hno⟩)
        exact ⟨y, mem_filter.2 ⟨hy, hyt⟩⟩
      have h1' : σ' ≠ {⊤} := fun h => h1 (Finset.eq_singleton_iff_unique_mem.2 ⟨ht, fun y hy => by
        have := hs hy; rw [h] at this; simpa using this⟩)
      rw [if_neg h1, if_neg h1']
      rcases L_step hs hch hne1 with h | h
      · rw [h]
      · exact WithTop.coe_le_coe.2 (Or.inr (by simp; omega))
  · rw [if_neg ht]
    have hne1 : (σ.filter (· ≠ ⊤)).Nonempty := by
      obtain ⟨y, hy⟩ := hne; exact ⟨y, mem_filter.2 ⟨hy, fun h => ht (h ▸ hy)⟩⟩
    have hL := L_step hs hch hne1
    by_cases ht' : (⊤ : C) ∈ σ'
    · have h1' : σ' ≠ {⊤} := fun h => by
        obtain ⟨y, hy⟩ := hne; have := hs hy; rw [h] at this
        exact ht ((Finset.mem_singleton.1 this) ▸ hy)
      rw [if_pos ht', if_neg h1']
      exact WithTop.coe_le_coe.2 (Or.inr (by simp; omega))
    · rw [if_neg ht']
      rcases hL with h | h
      · rw [h]
      · exact WithTop.coe_le_coe.2 (Or.inr (by simp; omega))

theorem val_w2 {σ : Finset C} (hne : σ.Nonempty) : ¬ ∀ y ∈ σ, y ≤ val σ := by
  intro hall
  unfold val at hall
  by_cases ht : (⊤ : C) ∈ σ
  · have := hall ⊤ ht
    rw [if_pos ht] at this
    split_ifs at this <;> exact WithTop.not_top_le_coe _ this
  · simp only [if_neg ht] at hall
    have hne1 : (σ.filter (· ≠ ⊤)).Nonempty := by
      obtain ⟨y, hy⟩ := hne; exact ⟨y, mem_filter.2 ⟨hy, fun h => ht (h ▸ hy)⟩⟩
    obtain ⟨g, hg, he⟩ := exists_top_level hne1
    rcases WithTop.coe_le_coe.1 (hall _ hg) with h | h
    · simp at h; omega
    · simp at h; omega

/-- **The DCC counterexample to chain-dependent CLL, `k = 1`.** -/
noncomputable def gapLabelling : Labelling 1 C where
  z _ σ := Sum.inr (val σ)
  ne _ _ _ _ _ _ h := by cases h
  w1 _ _ _ _ _ _ h := by cases h
  w2 _ σ c _ hσ _ h := by cases h; exact val_w2 hσ
  mono_col _ σ _ σ' c _ hσ hch _ hs h := by cases h; exact ⟨_, rfl, val_mono hs hσ hch⟩
  mono_lab _ _ _ _ _ _ _ _ _ _ _ h := by cases h

/-- **DCC does not suffice for (chain-dependent) CLL.** -/
theorem not_cll_dcc : ¬ ∀ (C : Type) [PartialOrder C] [OrderTop C] [WellFoundedLT C], Labelling 1 C → False :=
  fun h => h C gapLabelling

/-! ### Max-only labellings -/

/-- **Descent for one row.** A monotone column map with `t ≰ g t` everywhere is impossible under DCC. -/
theorem column_descent {β : Type*} [PartialOrder β] [OrderTop β] [WellFoundedLT β] (g : β → β) (hg : Monotone g)
    (hw : ∀ t, ¬ t ≤ g t) : False := by
  obtain ⟨m, hm, hmin⟩ := (wellFounded_lt (α := β)).has_min {t | g t ≤ t} ⟨⊤, le_top⟩
  have hgm : g m ∈ {t | g t ≤ t} := hg hm
  exact hw m (eq_of_le_of_not_lt hm (hmin _ hgm)).ge

variable (k : ℕ) (β : Type*) [PartialOrder β] [OrderTop β]

/-- A labelling depending only on the row set and the top column (the shape FG∞ produces). -/
structure MaxLabelling where
  w : Finset (Fin k) → β → Finset (Fin k) ⊕ β
  ne : ∀ (A : Finset (Fin k)) (c : β) (α : Finset (Fin k)), A.Nonempty → w A c = Sum.inl α → α.Nonempty
  w1 : ∀ (A : Finset (Fin k)) (c : β) (α : Finset (Fin k)), A.Nonempty → w A c = Sum.inl α → ¬ A ⊆ α
  w2 : ∀ (A : Finset (Fin k)) (c c' : β), A.Nonempty → w A c = Sum.inr c' → ¬ c ≤ c'
  mono_col : ∀ (A A' : Finset (Fin k)) (c c' d : β), A'.Nonempty → A' ⊆ A → c ≤ c' → w A c = Sum.inr d →
    ∃ d', w A' c' = Sum.inr d' ∧ d ≤ d'
  mono_lab : ∀ (A A' : Finset (Fin k)) (c c' : β) (α α' : Finset (Fin k)), A'.Nonempty → A' ⊆ A → c ≤ c' →
    w A c = Sum.inl α → w A' c' = Sum.inl α' → α' ⊆ α

variable {k β}

/-- A max-only labelling is a labelling (labels read at `cmax σ`). -/
noncomputable def MaxLabelling.toLabelling (M : MaxLabelling k β) : Labelling k β where
  z A σ := M.w A (cmax σ)
  ne A σ α hA hσ hch h := M.ne A _ α hA h
  w1 A σ α hA hσ hch h := M.w1 A _ α hA h
  w2 A σ c hA hσ hch h hall := M.w2 A _ c hA h (hall _ (cmax_spec hσ hch).1)
  mono_col A σ A' σ' c hA' hσ hch hsub hs h :=
    M.mono_col A A' _ _ c hA' hsub
      ((cmax_spec (hσ.mono hs) hch).2 _ (hs (cmax_spec hσ (hch.mono (by exact_mod_cast hs))).1)) h
  mono_lab A σ A' σ' α α' hA' hσ hch hsub hs h h' :=
    M.mono_lab A A' _ _ α α' hA' hsub
      ((cmax_spec (hσ.mono hs) hch).2 _ (hs (cmax_spec hσ (hch.mono (by exact_mod_cast hs))).1)) h h'

/-- Finite max-only CLL (from `CLL.cll`). -/
theorem cll_max [Fintype β] (hk : 0 < k) (M : MaxLabelling k β) : False := cll hk M.toLabelling

/-- **Infinite max-only CLL for one row, DCC only.** -/
theorem cll_max_one [WellFoundedLT β] (M : MaxLabelling 1 β) : False := by
  have hA : (univ : Finset (Fin 1)).Nonempty := univ_nonempty
  have hcol : ∀ c, ∃ d, M.w univ c = Sum.inr d := fun c => by
    rcases h : M.w univ c with α | d
    · exact absurd (fun i _ => by
        obtain ⟨j, hj⟩ := M.ne _ c α hA h
        rw [Subsingleton.elim i j]; exact hj) (M.w1 _ c α hA h)
    · exact ⟨d, rfl⟩
  choose g hg using hcol
  refine column_descent g (fun c c' h => ?_) (fun t => M.w2 _ t (g t) hA (hg t))
  obtain ⟨d', hd', hle⟩ := M.mono_col univ univ c c' (g c) hA (Finset.Subset.refl _) h (hg c)
  rw [hg c'] at hd'; cases hd'; exact hle


/-! ### Max-only CLL for two rows, DCC only (the poset form of `FGTwo.cut_two`) -/

section Two
variable [WellFoundedLT β] (M : MaxLabelling 2 β)

/-- A label at a larger cell forces a label at a smaller one, with a larger label set. -/
theorem MaxLabelling.lab_down {A A' : Finset (Fin 2)} (hA' : A'.Nonempty) (hsub : A' ⊆ A) {c c' : β} (hc : c ≤ c')
    {α' : Finset (Fin 2)} (h : M.w A' c' = Sum.inl α') : ∃ α, M.w A c = Sum.inl α ∧ α' ⊆ α := by
  rcases hw : M.w A c with α | d
  · exact ⟨α, rfl, M.mono_lab A A' c c' α α' hA' hsub hc hw h⟩
  · obtain ⟨d', hd', -⟩ := M.mono_col A A' c c' d hA' hsub hc hw
    rw [h] at hd'; cases hd'

theorem fin2_cover {a x : Fin 2} (hxa : x ≠ a) {γ : Finset (Fin 2)} (ha : a ∈ γ) (hx : x ∈ γ) : univ ⊆ γ := by
  intro y _
  have : y = a ∨ y = x := by fin_cases a <;> fin_cases x <;> fin_cases y <;> simp_all
  rcases this with rfl | rfl <;> assumption

/-- The orbit of the meet row `h = w(univ, ·)` from `s` ends at a label containing `a`. -/
inductive Ends (a : Fin 2) : β → Prop
  | stop {s : β} {α : Finset (Fin 2)} : M.w univ s = Sum.inl α → a ∈ α → Ends a s
  | step {s d : β} : M.w univ s = Sum.inr d → Ends a d → Ends a s

variable {M}

/-- **Squeeze.** If the orbit of `s` ends with label `a`, so does the orbit of every `t` with `h s ≤ t ≤ s`. -/
theorem Ends.squeeze {a : Fin 2} {s : β} (hE : Ends M a s) :
    ∀ t, t ≤ s → (∀ d, M.w univ s = Sum.inr d → d ≤ t) → Ends M a t := by
  induction hE with
  | stop hs ha =>
      intro t hts _
      obtain ⟨α', ht, hsub⟩ := M.lab_down univ_nonempty (Finset.Subset.refl _) hts hs
      exact Ends.stop ht (hsub ha)
  | @step s d hs hE ih =>
      intro t hts hlow
      have hdt : d ≤ t := hlow d hs
      rcases ht : M.w univ t with α' | d'
      · obtain ⟨αd, hd, hsub⟩ := M.lab_down univ_nonempty (Finset.Subset.refl _) hdt ht
        have hW := M.w1 univ d αd univ_nonempty hd
        have haα : a ∈ αd := by
          cases hE with
          | stop h1 h2 => rw [hd] at h1; cases h1; exact h2
          | step h1 _ => rw [hd] at h1; cases h1
        obtain ⟨x, hx⟩ := M.ne univ t α' univ_nonempty ht
        have hxa : x = a := by
          by_contra hxa; exact hW (fin2_cover hxa haα (hsub hx))
        exact Ends.stop ht (hxa ▸ hx)
      · obtain ⟨d'', hd'', hle⟩ := M.mono_col univ univ t s d' univ_nonempty (Finset.Subset.refl _) hts ht
        rw [hs] at hd''; cases hd''
        refine Ends.step ht (ih d' hle fun e he => ?_)
        obtain ⟨e', he', hle'⟩ := M.mono_col univ univ d t e univ_nonempty (Finset.Subset.refl _) hdt he
        rw [ht] at he'; cases he'; exact hle'

/-- A label in row `a` is incompatible with the orbit ending at a label containing `a`. -/
theorem Ends.not_lab {a : Fin 2} {c : β} (hE : Ends M a c) {α : Finset (Fin 2)} (hg : M.w {a} c = Sum.inl α) :
    False := by
  obtain ⟨αh, hh, hsub⟩ := M.lab_down (singleton_nonempty a) (subset_univ _) le_rfl hg
  have haα : a ∉ α := fun h => M.w1 {a} c α (singleton_nonempty a) hg (singleton_subset_iff.2 h)
  obtain ⟨x, hx⟩ := M.ne {a} c α (singleton_nonempty a) hg
  cases hE with
  | stop h1 h2 =>
      rw [hh] at h1; cases h1
      exact M.w1 univ c αh univ_nonempty hh (fin2_cover (fun (h : x = a) => haα (h ▸ hx)) h2 (hsub hx))
  | step h1 _ => rw [hh] at h1; cases h1

/-- **Infinite max-only CLL for two rows, DCC only.** This is the poset form of `FGTwo.cut_two`: the orbit of the
meet row from `⊤` ends at a label `a`; then row `a` contracts at `⊤`, and a contracting column whose orbit ends at
`a` has a strictly smaller one (`Ends.squeeze` at `w = w({a}, s)`), contradicting DCC. -/
theorem cll_max_two (M : MaxLabelling 2 β) : False := by
  have hends : ∀ s, (∀ d, M.w univ s = Sum.inr d → d ≤ s) → ∃ a, Ends M a s := by
    intro s
    induction s using WellFoundedLT.induction with
    | _ s ih =>
      intro hdesc
      rcases hs : M.w univ s with α | d
      · obtain ⟨a, ha⟩ := M.ne univ s α univ_nonempty hs; exact ⟨a, Ends.stop hs ha⟩
      · have hds := hdesc d hs
        have hlt : d < s := lt_of_le_of_ne hds fun h => M.w2 univ s d univ_nonempty hs (h ▸ le_rfl)
        obtain ⟨a, ha⟩ := ih d hlt fun e he => by
          obtain ⟨e', he', hle⟩ := M.mono_col univ univ d s e univ_nonempty (Finset.Subset.refl _) hds he
          rw [hs] at he'; cases he'; exact hle
        exact ⟨a, Ends.step hs ha⟩
  have hS : ∀ a s, (∃ d, M.w {a} s = Sum.inr d ∧ d ≤ s) → Ends M a s → False := by
    intro a s0 h0 hE0
    obtain ⟨s, ⟨⟨w, hw, hws⟩, hE⟩, hmin⟩ := (wellFounded_lt (α := β)).has_min
      {s | (∃ d, M.w {a} s = Sum.inr d ∧ d ≤ s) ∧ Ends M a s} ⟨s0, h0, hE0⟩
    have hlt : w < s := lt_of_le_of_ne hws fun h => M.w2 {a} s w (singleton_nonempty a) hw (h ▸ le_rfl)
    have hEw : Ends M a w := hE.squeeze w hws fun d hd => by
      obtain ⟨d', hd', hle⟩ := M.mono_col univ {a} s s d (singleton_nonempty a) (subset_univ _) le_rfl hd
      rw [hw] at hd'; cases hd'; exact hle
    have hgw : ∃ d, M.w {a} w = Sum.inr d ∧ d ≤ w := by
      rcases hg : M.w {a} w with α | d
      · exact (hEw.not_lab hg).elim
      · obtain ⟨d', hd', hle⟩ := M.mono_col {a} {a} w s d (singleton_nonempty a) (Finset.Subset.refl _) hlt.le hg
        rw [hw] at hd'; cases hd'; exact ⟨d, rfl, hle⟩
    exact hmin w ⟨hgw, hEw⟩ hlt
  obtain ⟨a, hE⟩ := hends ⊤ fun d _ => le_top
  refine hS a ⊤ ?_ hE
  rcases hg : M.w {a} ⊤ with α | d
  · exact (hE.not_lab hg).elim
  · exact ⟨d, rfl, le_top⟩

end Two


/-! ### FG∞ for two generators on posets -/

/-- **The Cut Lemma for two-generated cuts of bounded posets with DCC.** `D = ↓p ∪ ↓q`, `p ⊓ q` exists as a greatest
lower bound, `⊤ ∉ D`; no lattice structure on the complement is needed. (Lattice version: `FGTwo.cut_two`.) -/
theorem cut_two_poset {P : Type*} [PartialOrder P] [BoundedOrder P] [WellFoundedLT P] (D : Set P)
    (hD : ∀ a b, a ≤ b → b ∈ D → a ∈ D) {p q r : P} (hp : p ∈ D) (hq : q ∈ D) (hgen : ∀ x ∈ D, x ≤ p ∨ x ≤ q)
    (hrp : r ≤ p) (hrq : r ≤ q) (hglb : ∀ x, x ≤ p → x ≤ q → x ≤ r) (htop : ⊤ ∉ D)
    (F : P → P → P) (hF : ∀ a a' b b', a ≤ a' → b ≤ b' → F a b ≤ F a' b') :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  by_contra hno
  push_neg at hno
  letI : OrderTop {y : P // y ∉ D} := { top := ⟨⊤, htop⟩, le_top := fun a => (le_top : a.1 ≤ ⊤) }
  haveI : WellFoundedLT {y : P // y ∉ D} :=
    ⟨Subrelation.wf (fun {a b} h => (show a.1 < b.1 from h)) (InvImage.wf Subtype.val wellFounded_lt)⟩
  let gen : Fin 2 → P := ![p, q]
  let m : Finset (Fin 2) → P := fun A => if A = univ then r else if (0 : Fin 2) ∈ A then p else q
  have hm_le : ∀ A : Finset (Fin 2), A.Nonempty → ∀ i ∈ A, m A ≤ gen i := by
    intro A _ i hi
    simp only [m]
    split_ifs with h1 h2
    · fin_cases i <;> simp [gen, hrp, hrq]
    · fin_cases i
      · simp [gen]
      · have : A = univ := by
          ext j; fin_cases j <;> simp_all
        exact absurd this h1
    · fin_cases i
      · exact absurd hi h2
      · simp [gen]
  have hm_glb : ∀ A : Finset (Fin 2), A.Nonempty → ∀ x, (∀ i ∈ A, x ≤ gen i) → x ≤ m A := by
    intro A hA x hx
    simp only [m]
    split_ifs with h1 h2
    · exact hglb x (hx 0 (by simp [h1])) (hx 1 (by simp [h1]))
    · exact hx 0 h2
    · obtain ⟨i, hi⟩ := hA
      fin_cases i
      · exact absurd hi h2
      · exact hx 1 hi
  have hmD : ∀ A : Finset (Fin 2), A.Nonempty → m A ∈ D := fun A hA => by
    obtain ⟨i, hi⟩ := hA
    exact hD _ _ (hm_le A ⟨i, hi⟩ i hi) (by fin_cases i <;> simp [gen, hp, hq])
  have hm_mono : ∀ A A' : Finset (Fin 2), A'.Nonempty → A' ⊆ A → m A ≤ m A' := fun A A' hA' hsub =>
    hm_glb A' hA' _ fun i hi => hm_le A (hA'.mono hsub) i (hsub hi)
  let w : Finset (Fin 2) → {y : P // y ∉ D} → Finset (Fin 2) ⊕ {y : P // y ∉ D} := fun A c =>
    if hv : F (m A) c.1 ∈ D then Sum.inl (univ.filter fun i => F (m A) c.1 ≤ gen i)
    else Sum.inr ⟨F (m A) c.1, hv⟩
  refine cll_max_two
    { w := w
      ne := fun A c α hA h => ?_
      w1 := fun A c α hA h hsub => ?_
      w2 := fun A c c' hA h hle => ?_
      mono_col := fun A A' c c' d hA' hsub hc h => ?_
      mono_lab := fun A A' c c' α α' hA' hsub hc h h' => ?_ }
  · simp only [w] at h
    split_ifs at h with hv
    · cases h
      rcases hgen _ hv with h1 | h1
      · exact ⟨0, by simp [gen, h1]⟩
      · exact ⟨1, by simp [gen, h1]⟩
  · simp only [w] at h
    split_ifs at h with hv
    · cases h
      have hle : F (m A) c.1 ≤ m A := hm_glb A hA _ fun i hi => by simpa using hsub hi
      exact (hno _ (hmD A hA) _ c.2).1 hle
  · simp only [w] at h
    split_ifs at h with hv
    · cases h
      exact (hno _ (hmD A hA) _ c.2).2 hle
  · have hle : F (m A) c.1 ≤ F (m A') c'.1 := hF _ _ _ _ (hm_mono A A' hA' hsub) hc
    simp only [w] at h
    split_ifs at h with hv
    · cases h
      have hv' : F (m A') c'.1 ∉ D := fun h' => hv (hD _ _ hle h')
      exact ⟨⟨F (m A') c'.1, hv'⟩, by simp only [w, dif_neg hv'], hle⟩
  · have hle : F (m A) c.1 ≤ F (m A') c'.1 := hF _ _ _ _ (hm_mono A A' hA' hsub) hc
    simp only [w] at h h'
    split_ifs at h h' with hv hv'
    cases h; cases h'
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hle.trans hi

end Mordor.InfiniteCLL

/-! ### The minimal terminal meet -/

namespace Mordor.MinSwitch
variable {α : Type*} [Lattice α] [BoundedOrder α] {F : α → α → α} {p₁ p₂ p₃ x : α}

/-- **At a terminal state minimal for the triple-meet row, the case-II meet lies below `p₂`.** If `x` is minimal among
columns outside `D` at which `r = p₁ ⊓ p₂ ⊓ p₃` contracts (as `HistoryFix.min_terminal` provides), then
`w = x ⊓ g₂ x ∈ D`, and by `terminal_meet` it is below `p₂` and neither `p₁` nor `p₃`. -/
theorem terminal_meet_le_p2 (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (nw : ∀ a, (a ≤ p₁ ∨ a ≤ p₂ ∨ a ≤ p₃) → ∀ y, ¬ (y ≤ p₁ ∨ y ≤ p₂ ∨ y ≤ p₃) → ¬ F a y ≤ a ∧ ¬ y ≤ F a y)
    (T : Terminal F p₁ p₂ p₃ x) (hvx : ¬ F p₂ x ≤ x)
    (hmin : ∀ y, y < x → ¬ (y ≤ p₁ ∨ y ≤ p₂ ∨ y ≤ p₃) → ¬ F (p₁ ⊓ p₂ ⊓ p₃) y ≤ y) :
    x ⊓ F p₂ x ≤ p₂ := by
  obtain ⟨hlt, -, hhw, -, -, hn1, hn3⟩ := terminal_meet hF nw T hvx
  by_contra h2
  exact hmin _ hlt (by rintro (h | h | h); exacts [hn1 h, h2 h, hn3 h])
    ((hF _ _ _ _ le_rfl inf_le_left).trans hhw)

end Mordor.MinSwitch
