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
