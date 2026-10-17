import Mordor.Cut
import Mathlib.Order.Atoms

/-!
# Corner and No-Room (log §16.2)

* `corner`: if `m < n` then `m < F m n < n` (the Corner Lemma, at the cell `(m, n)` instead of `(⊥, ⊤)` of a
  polar configuration, so no polar reduction is needed).
* `cl_noRoom`: on a complete lattice in which every element other than `⊥, ⊤` is both an atom and a coatom
  (edge-height ≤ 2, e.g. the diamonds `M_κ` for every cardinal `κ`, infinite included), commutation
  `a ∘ b = b ∘ a` forces `μX. νY. F = νY. μX. F`.
* `cut_noRoom`: on the same lattices the **Cut Lemma** holds for every `F` and every down-set (one cell of
  `{(⊥, ⊤), (c, ⊤), (⊥, c)}`, `c = F ⊥ ⊤`, is a witness), hence `semi_noRoom`: semi-commutation forces
  `m = n`. The log had this only through z3 (`C₁`, `C₂` unsat, §31.5).
-/

namespace Mordor
variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

theorem F_m_m : F (m F) (m F) = m F := by have h := row_a (F := F) (m F); rwa [a_m] at h
theorem F_n_n : F (n F) (n F) = n F := by have h := col_b (F := F) (n F); rwa [b_n] at h

/-- **Corner Lemma.** -/
theorem corner (hlt : m F < n F) : m F < F (m F) (n F) ∧ F (m F) (n F) < n F := by
  have hne_n : F (m F) (n F) ≠ n F := fun h => by
    have : n F ≤ a F (m F) := le_a h.ge
    rw [a_m] at this; exact lt_irrefl _ (lt_of_lt_of_le hlt this)
  have hne_m : F (m F) (n F) ≠ m F := fun h => by
    have : b F (n F) ≤ m F := b_le h.le
    rw [b_n] at this; exact lt_irrefl _ (lt_of_lt_of_le hlt this)
  have h1 : m F ≤ F (m F) (n F) :=
    calc m F = F (m F) (m F) := F_m_m.symm
      _ ≤ F (m F) (n F) := (F (m F)).mono hlt.le
  have h2 : F (m F) (n F) ≤ n F :=
    calc F (m F) (n F) ≤ F (n F) (n F) := F.mono hlt.le (n F)
      _ = n F := F_n_n
  exact ⟨lt_of_le_of_ne h1 (Ne.symm hne_m), lt_of_le_of_ne h2 hne_n⟩

/-- **No-Room ⟹ CL.** -/
theorem cl_noRoom (hmid : ∀ x : α, x ≠ ⊥ → x ≠ ⊤ → IsAtom x ∧ IsCoatom x)
    (hcomm : ∀ x, a F (b F x) = b F (a F x)) : m F = n F := by
  by_contra hne
  have hlt : m F < n F := lt_of_le_of_ne m_le_n hne
  obtain ⟨hmc, hcn⟩ := corner hlt
  set c := F (m F) (n F) with hc
  have hcat := hmid c (ne_bot_of_gt hmc) (ne_top_of_lt hcn)
  have hm : m F = ⊥ := hcat.1.2 _ hmc
  have hn : n F = ⊤ := hcat.2.2 _ hcn
  -- row ⊥ at c: F ⊥ c ≤ c, and F ⊥ c = c would put c ≤ a ⊥ = ⊥
  have hbc : b F c = ⊥ := by
    have hle : F ⊥ c ≤ c := by
      calc F ⊥ c ≤ F ⊥ ⊤ := (F ⊥).mono le_top
        _ = c := by rw [hc, hm, hn]
    rcases lt_or_eq_of_le hle with hlt' | heq
    · have h0 : F ⊥ c = ⊥ := hcat.1.2 _ hlt'
      exact le_bot_iff.mp (b_le (le_of_eq h0))
    · exfalso
      have : c ≤ a F ⊥ := le_a heq.ge
      rw [← hm, a_m, hm] at this
      exact absurd this (ne_bot_of_gt hmc ∘ le_bot_iff.mp)
  -- column ⊤ at c: c ≤ F c ⊤, and F c ⊤ = c would put b ⊤ ≤ c < ⊤
  have hac : a F c = ⊤ := by
    have hge : c ≤ F c ⊤ := by
      calc c = F ⊥ ⊤ := by rw [hc, hm, hn]
        _ ≤ F c ⊤ := F.mono bot_le ⊤
    rcases lt_or_eq_of_le hge with hlt' | heq
    · have h0 : F c ⊤ = ⊤ := hcat.2.2 _ hlt'
      exact top_le_iff.mp (le_a (ge_of_eq h0))
    · exfalso
      have : b F ⊤ ≤ c := b_le heq.ge
      rw [← hn, b_n, hn] at this
      exact absurd this (ne_top_of_lt hcn ∘ top_le_iff.mp)
  -- commutation at c: a ⊥ = b ⊤, i.e. m = n
  have := hcomm c
  rw [hbc, hac, ← hm, a_m, ← hn, b_n] at this
  exact hne this

/-- **The Cut Lemma at edge-height ≤ 2.** -/
theorem cut_noRoom (hmid : ∀ x : α, x ≠ ⊥ → x ≠ ⊤ → IsAtom x ∧ IsCoatom x) (G : α →o α →o α) :
    CutCells G := by
  intro D hD ⟨d, hd⟩ ⟨u, hu⟩
  have hbot : ⊥ ∈ D := hD bot_le hd
  have htop : ⊤ ∉ D := fun h => hu (hD le_top h)
  by_cases hc0 : G ⊥ ⊤ = ⊥
  · exact ⟨⊥, hbot, ⊤, htop, Or.inl hc0.le⟩
  by_cases hc1 : G ⊥ ⊤ = ⊤
  · exact ⟨⊥, hbot, ⊤, htop, Or.inr hc1.ge⟩
  obtain ⟨hat, hco⟩ := hmid _ hc0 hc1
  by_cases hcD : G ⊥ ⊤ ∈ D
  · refine ⟨G ⊥ ⊤, hcD, ⊤, htop, ?_⟩
    rcases lt_or_eq_of_le (G.mono (bot_le : ⊥ ≤ G ⊥ ⊤) ⊤) with hlt | heq
    · exact Or.inr (hco.2 _ hlt).ge
    · exact Or.inl heq.ge
  · refine ⟨⊥, hbot, G ⊥ ⊤, hcD, ?_⟩
    rcases lt_or_eq_of_le ((G ⊥).mono (le_top : G ⊥ ⊤ ≤ ⊤)) with hlt | heq
    · exact Or.inl (hat.2 _ hlt).le
    · exact Or.inr heq.ge

/-- **Semi-CL at edge-height ≤ 2.** -/
theorem semi_noRoom (hmid : ∀ x : α, x ≠ ⊥ → x ≠ ⊤ → IsAtom x ∧ IsCoatom x) (G : α →o α →o α)
    (hsemi : ∀ x, b G (a G x) ≤ a G (b G x)) : m G = n G :=
  semi_of_cut (cutMaps_of_cells (cut_noRoom hmid G)) hsemi

end Mordor
