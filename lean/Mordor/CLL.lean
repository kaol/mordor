import Mordor.ConeSperner
import Mathlib.Order.Preorder.Chain

/-!
# The chain labelling lemma (log §34.3z²⁹, §34.3z³³)

`C` is a finite poset with a top. A *cell* is `(A, σ)` with `∅ ≠ A ⊆ Fin k` and `σ` a nonempty chain of `C`, ordered by
`A ⊇ A'`, `σ ⊆ σ'`. A labelling gives each cell a nonempty label set `α ⊆ Fin k` or a column `c ∈ C`, monotonically,
with W1 (`A ⊄ α`) and W2 (`σ ⊄ ↓c`). **`cll`: no such labelling exists** (`k ≥ 1`).

Proof: the cone Sperner lemma (`ConeSperner.exists_full`) on the complex of sets `S ⊆ Fin k ⊕ C` with proper
`Fin k`-part and chain `C`-part, a cone with apex `⊤`. A pure face is labelled by a generator outside it, a label cell
by a generator of `A ∖ α`, a column cell by its column. Labels of a complete flag form a face: generator labels avoid
the first letter (if it is a generator) or the label set of the last label cell; column labels form a chain by
monotonicity. A fully labelled flag is impossible: a generator label at the top lies outside the face, and a column
label at the top would sit above every column of the face (W2).

Consequence (`cut_of_meets`, see the log): Cut on every finite bounded poset whose `D`-maxima have all meets.
-/

namespace Mordor.CLL
open Finset Classical Mordor.ConeSperner
set_option linter.unusedSectionVars false

variable {k : ℕ} {C : Type*} [Fintype C] [PartialOrder C] [OrderTop C]

/-- A chain labelling satisfying W1, W2 and monotonicity. -/
structure Labelling (k : ℕ) (C : Type*) [Fintype C] [PartialOrder C] [OrderTop C] where
  z : Finset (Fin k) → Finset C → Finset (Fin k) ⊕ C
  ne : ∀ (A : Finset (Fin k)) (σ : Finset C) (α : Finset (Fin k)), A.Nonempty → σ.Nonempty → IsChain (· ≤ ·) (σ : Set C) → z A σ = Sum.inl α → α.Nonempty
  w1 : ∀ (A : Finset (Fin k)) (σ : Finset C) (α : Finset (Fin k)), A.Nonempty → σ.Nonempty → IsChain (· ≤ ·) (σ : Set C) → z A σ = Sum.inl α → ¬ A ⊆ α
  w2 : ∀ (A : Finset (Fin k)) (σ : Finset C) (c : C), A.Nonempty → σ.Nonempty → IsChain (· ≤ ·) (σ : Set C) → z A σ = Sum.inr c → ¬ ∀ y ∈ σ, y ≤ c
  mono_col : ∀ (A : Finset (Fin k)) (σ : Finset C) (A' : Finset (Fin k)) (σ' : Finset C) (c : C), A'.Nonempty → σ.Nonempty → IsChain (· ≤ ·) (σ' : Set C) → A' ⊆ A → σ ⊆ σ' →
    z A σ = Sum.inr c → ∃ c', z A' σ' = Sum.inr c' ∧ c ≤ c'
  mono_lab : ∀ (A : Finset (Fin k)) (σ : Finset C) (A' : Finset (Fin k)) (σ' : Finset C)
      (α α' : Finset (Fin k)), A'.Nonempty → σ.Nonempty → IsChain (· ≤ ·) (σ' : Set C) → A' ⊆ A → σ ⊆ σ' →
    z A σ = Sum.inl α → z A' σ' = Sum.inl α' → α' ⊆ α

/-- Generator part, column part and complement of a set of vertices. -/
noncomputable def Bp (S : Finset (Fin k ⊕ C)) : Finset (Fin k) := univ.filter fun i => Sum.inl i ∈ S
noncomputable def Cp (S : Finset (Fin k ⊕ C)) : Finset C := univ.filter fun c => Sum.inr c ∈ S
noncomputable def Ap (S : Finset (Fin k ⊕ C)) : Finset (Fin k) := univ.filter fun i => Sum.inl i ∉ S

/-- The faces: nonempty, proper generator part, chain column part. -/
noncomputable def Kc (k : ℕ) (C : Type*) [Fintype C] [PartialOrder C] : Finset (Finset (Fin k ⊕ C)) :=
  univ.filter fun S => S.Nonempty ∧ (Ap S).Nonempty ∧ IsChain (· ≤ ·) (Cp S : Set C)

theorem mem_Kc {S : Finset (Fin k ⊕ C)} :
    S ∈ Kc k C ↔ S.Nonempty ∧ (Ap S).Nonempty ∧ IsChain (· ≤ ·) (Cp S : Set C) := by simp [Kc]

noncomputable def pick (hk : 0 < k) (T : Finset (Fin k)) : Fin k := if h : T.Nonempty then h.choose else ⟨0, hk⟩

theorem pick_mem (hk : 0 < k) {T : Finset (Fin k)} (h : T.Nonempty) : pick hk T ∈ T := by
  unfold pick; rw [dif_pos h]; exact h.choose_spec

/-- The labelling of faces. -/
noncomputable def φ (hk : 0 < k) (L : Labelling k C) (S : Finset (Fin k ⊕ C)) : Fin k ⊕ C :=
  if (Cp S).Nonempty then
    Sum.elim (fun α => Sum.inl (pick hk (Ap S \ α))) (fun c => Sum.inr c) (L.z (Ap S) (Cp S))
  else Sum.inl (pick hk (Ap S))

variable (hk : 0 < k) (L : Labelling k C)

theorem φ_inl {S : Finset (Fin k ⊕ C)} (hS : S ∈ Kc k C) {i : Fin k} (h : φ hk L S = Sum.inl i) :
    Sum.inl i ∉ S ∧ ∀ α, (Cp S).Nonempty → L.z (Ap S) (Cp S) = Sum.inl α → i ∉ α := by
  obtain ⟨_, hA, hch⟩ := mem_Kc.1 hS
  unfold φ at h
  split_ifs at h with hC
  · rcases hz : L.z (Ap S) (Cp S) with α | c
    · rw [hz] at h; simp only [Sum.elim_inl, Sum.inl.injEq] at h
      have hne : (Ap S \ α).Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hn
        exact L.w1 _ _ α hA hC hch hz hn
      have hm := pick_mem hk hne
      rw [h] at hm
      obtain ⟨hmA, hmα⟩ := mem_sdiff.1 hm
      refine ⟨by simpa [Ap] using hmA, fun α' _ hz' => ?_⟩
      cases hz'; exact hmα
    · rw [hz] at h; simp at h
  · have hm := pick_mem hk hA
    simp only [Sum.inl.injEq] at h
    rw [h] at hm
    exact ⟨by simpa [Ap] using hm, fun α hC' => absurd hC' hC⟩

theorem φ_inr {S : Finset (Fin k ⊕ C)} {c : C} (h : φ hk L S = Sum.inr c) :
    (Cp S).Nonempty ∧ L.z (Ap S) (Cp S) = Sum.inr c := by
  unfold φ at h
  split_ifs at h with hC
  · rcases hz : L.z (Ap S) (Cp S) with α | c'
    · rw [hz] at h; simp at h
    · rw [hz] at h; simp only [Sum.elim_inr, Sum.inr.injEq] at h; exact ⟨hC, h ▸ rfl⟩

theorem Ap_anti {S S' : Finset (Fin k ⊕ C)} (h : S ⊆ S') : Ap S' ⊆ Ap S := fun i hi => by
  simp only [Ap, mem_filter, mem_univ, true_and] at hi ⊢; exact fun h' => hi (h h')

theorem Cp_mono {S S' : Finset (Fin k ⊕ C)} (h : S ⊆ S') : Cp S ⊆ Cp S' := fun c hc => by
  simp only [Cp, mem_filter, mem_univ, true_and] at hc ⊢; exact h hc

theorem Kc_down {S T : Finset (Fin k ⊕ C)} (hS : S ∈ Kc k C) (hT : T ⊆ S) (hne : T.Nonempty) : T ∈ Kc k C := by
  obtain ⟨_, hA, hch⟩ := mem_Kc.1 hS
  exact mem_Kc.2 ⟨hne, hA.mono (Ap_anti hT), hch.mono (by exact_mod_cast Cp_mono hT)⟩

theorem Kc_apex {S : Finset (Fin k ⊕ C)} (hS : S ∈ Kc k C) : insert (Sum.inr ⊤) S ∈ Kc k C := by
  obtain ⟨hne, hA, hch⟩ := mem_Kc.1 hS
  refine mem_Kc.2 ⟨insert_nonempty _ _, ?_, ?_⟩
  · have : Ap (insert (Sum.inr ⊤) S) = Ap S := by ext i; simp [Ap]
    rw [this]; exact hA
  · have : (Cp (insert (Sum.inr (⊤ : C)) S) : Set C) = insert ⊤ (Cp S : Set C) := by
      ext c; simp [Cp]
    rw [this]
    exact hch.insert fun b _ _ => Or.inr le_top

theorem pre_sub {n : ℕ} {τ : Finset (Fin k ⊕ C)} {w : Fin n → Fin k ⊕ C} (hw : w ∈ W n τ) (t : ℕ) :
    pre w t ⊆ τ := fun x hx => by
  obtain ⟨s, _, rfl⟩ := mem_pre.1 hx
  have h := (mem_W.1 hw).2; rw [← h]; simp

theorem pre_mono' {n : ℕ} (w : Fin n → Fin k ⊕ C) {t t' : ℕ} (h : t ≤ t') : pre w t ⊆ pre w t' := fun x hx => by
  obtain ⟨s, hs, rfl⟩ := mem_pre.1 hx
  exact mem_pre.2 ⟨s, by omega, rfl⟩

theorem pre_ne {n : ℕ} (w : Fin n → Fin k ⊕ C) (hn : 0 < n) (t : ℕ) : w ⟨0, hn⟩ ∈ pre w t :=
  mem_pre.2 ⟨⟨0, hn⟩, Nat.zero_le _, rfl⟩

theorem mem_lab_iff {n : ℕ} (f : Finset (Fin k ⊕ C) → Fin k ⊕ C) (w : Fin n → Fin k ⊕ C) (x : Fin k ⊕ C) :
    x ∈ lab f w ↔ ∃ t : Fin n, f (pre w t.val) = x := by
  simp [lab, List.mem_ofFn]

/-- The labels of every complete flag form a face. -/
theorem lab_face {τ : Finset (Fin k ⊕ C)} (hτ : τ ∈ Kc k C) {n : ℕ} {w : Fin n → Fin k ⊕ C} (hw : w ∈ W n τ) :
    (lab (φ hk L) w).toFinset ∈ Kc k C := by
  have hn : 0 < n := by rw [← card_of_mem_W hw]; exact (mem_Kc.1 hτ).1.card_pos
  have hP : ∀ t : ℕ, pre w t ∈ Kc k C := fun t => Kc_down hτ (pre_sub hw t) ⟨_, pre_ne w hn t⟩
  have hPA : ∀ t, (Ap (pre w t)).Nonempty := fun t => (mem_Kc.1 (hP t)).2.1
  have hPC : ∀ t, IsChain (· ≤ ·) (Cp (pre w t) : Set C) := fun t => (mem_Kc.1 (hP t)).2.2
  refine mem_Kc.2 ⟨⟨φ hk L (pre w 0), List.mem_toFinset.2 ((mem_lab_iff _ w _).2 ⟨⟨0, hn⟩, rfl⟩)⟩, ?_, ?_⟩
  · -- a generator avoided by every label
    rcases hw0 : w ⟨0, hn⟩ with i₀ | c₀
    · refine ⟨i₀, ?_⟩
      simp only [Ap, mem_filter, mem_univ, true_and, List.mem_toFinset, mem_lab_iff]
      rintro ⟨t, ht⟩
      exact (φ_inl hk L (hP t) ht).1 (hw0 ▸ pre_ne w hn t)
    · have hCne : ∀ t, (Cp (pre w t)).Nonempty := fun t =>
        ⟨c₀, by simp only [Cp, mem_filter, mem_univ, true_and]; exact hw0 ▸ pre_ne w hn t⟩
      have hzl : ∀ t i, φ hk L (pre w t) = Sum.inl i →
          ∃ α, L.z (Ap (pre w t)) (Cp (pre w t)) = Sum.inl α := fun t i h => by
        rcases hz : L.z (Ap (pre w t)) (Cp (pre w t)) with α | c
        · exact ⟨α, rfl⟩
        · have h2 : φ hk L (pre w t) = Sum.inr c := by unfold φ; rw [if_pos (hCne t), hz]; rfl
          rw [h] at h2; exact absurd h2 (by simp)
      set T := univ.filter fun t : Fin n => ∃ i, φ hk L (pre w t.val) = Sum.inl i
      by_cases hT : T.Nonempty
      · obtain ⟨istar, histar⟩ := (mem_filter.1 (T.max'_mem hT)).2
        obtain ⟨αstar, hαstar⟩ := hzl _ _ histar
        obtain ⟨j, hj⟩ := L.ne _ _ αstar (hPA _) (hCne _) (hPC _) hαstar
        refine ⟨j, ?_⟩
        simp only [Ap, mem_filter, mem_univ, true_and, List.mem_toFinset, mem_lab_iff]
        rintro ⟨t, ht⟩
        have htT : t ∈ T := mem_filter.2 ⟨mem_univ _, j, ht⟩
        have hle : t ≤ T.max' hT := T.le_max' t htT
        obtain ⟨α, hα⟩ := hzl _ _ ht
        have hsub := pre_mono' w (Fin.le_def.1 hle)
        have := L.mono_lab _ _ _ _ α αstar (hPA _) (hCne _) (hPC _) (Ap_anti hsub) (Cp_mono hsub) hα hαstar
        exact (φ_inl hk L (hP t) ht).2 α (hCne t) hα (this hj)
      · refine ⟨⟨0, by omega⟩, ?_⟩
        simp only [Ap, mem_filter, mem_univ, true_and, List.mem_toFinset, mem_lab_iff]
        rintro ⟨t, ht⟩
        exact hT ⟨t, mem_filter.2 ⟨mem_univ _, _, ht⟩⟩
  · -- column labels are comparable
    intro a ha b hb _
    simp only [Cp, coe_filter, mem_univ, true_and, Set.mem_setOf_eq, List.mem_toFinset, mem_lab_iff] at ha hb
    obtain ⟨t, ht⟩ := ha; obtain ⟨t', ht'⟩ := hb
    obtain ⟨hC, hz⟩ := φ_inr hk L ht
    obtain ⟨hC', hz'⟩ := φ_inr hk L ht'
    rcases le_total t t' with h | h
    · have hsub := pre_mono' w (Fin.le_def.1 h)
      obtain ⟨c'', hc'', hle⟩ := L.mono_col _ _ _ _ a (hPA _) hC (hPC _) (Ap_anti hsub) (Cp_mono hsub) hz
      rw [hz'] at hc''; cases hc''; exact Or.inl hle
    · have hsub := pre_mono' w (Fin.le_def.1 h)
      obtain ⟨c'', hc'', hle⟩ := L.mono_col _ _ _ _ b (hPA _) hC' (hPC _) (Ap_anti hsub) (Cp_mono hsub) hz'
      rw [hz] at hc''; cases hc''; exact Or.inr hle

theorem cone_data : ConeData (Kc k C) (φ hk L) (Sum.inr ⊤) where
  ne := fun τ hτ => (mem_Kc.1 hτ).1
  down := fun τ hτ σ h hne => Kc_down hτ h hne
  apex := fun τ hτ => by convert Kc_apex hτ
  simp := fun τ hτ n w hw => by convert lab_face hk L hτ hw

/-- **The chain labelling lemma.** -/
theorem cll (hk : 0 < k) (L : Labelling k C) : False := by
  have hv : ({Sum.inr ⊤} : Finset (Fin k ⊕ C)) ∈ Kc k C := by
    refine mem_Kc.2 ⟨singleton_nonempty _, ⟨⟨0, hk⟩, by simp [Ap]⟩, ?_⟩
    have : (Cp ({Sum.inr (⊤ : C)} : Finset (Fin k ⊕ C)) : Set C) = {⊤} := by ext c; simp [Cp]
    rw [this]; exact Set.Subsingleton.isChain Set.subsingleton_singleton
  obtain ⟨τ, hτ, n, w, hw, hlab⟩ := exists_full (cone_data hk L) hv
  have hn : 0 < n := by rw [← card_of_mem_W hw]; exact (mem_Kc.1 hτ).1.card_pos
  have hP : ∀ t : ℕ, pre w t ∈ Kc k C := fun t => Kc_down hτ (pre_sub hw t) ⟨_, pre_ne w hn t⟩
  have htop : pre w (n - 1) = τ := by
    apply Subset.antisymm (pre_sub hw _)
    intro x hx
    have h := (mem_W.1 hw).2
    rw [← h] at hx
    simp only [mem_image, mem_univ, true_and] at hx
    obtain ⟨s, rfl⟩ := hx
    exact mem_pre.2 ⟨s, by omega, rfl⟩
  have hmemτ : ∀ x, x ∈ lab (φ hk L) w ↔ x ∈ τ := fun x => by
    rw [← Multiset.mem_coe, hlab]; rfl
  have hx₀ : φ hk L τ ∈ τ := (hmemτ _).1 ((mem_lab_iff _ w _).2 ⟨⟨n - 1, by omega⟩, by rw [htop]⟩)
  rcases hφ : φ hk L τ with i | c
  · rw [hφ] at hx₀; exact (φ_inl hk L hτ hφ).1 hx₀
  · obtain ⟨hC, hz⟩ := φ_inr hk L hφ
    obtain ⟨_, hA, hch⟩ := mem_Kc.1 hτ
    refine L.w2 _ _ c hA hC hch hz fun y hy => ?_
    have hyτ : Sum.inr y ∈ τ := by simpa [Cp] using hy
    obtain ⟨t, ht⟩ := (mem_lab_iff _ w _).1 ((hmemτ _).2 hyτ)
    obtain ⟨hCt, hzt⟩ := φ_inr hk L ht
    have hsub := pre_sub hw t.val
    obtain ⟨c'', hc'', hle⟩ := L.mono_col _ _ _ _ y hA hCt hch (Ap_anti hsub) (Cp_mono hsub) hzt
    rw [hz] at hc''; cases hc''; exact hle

end Mordor.CLL
