import Mordor.Cut

/-!
# Orbit laxity of the transposed Cut Lemma (log §32.6)

Down-set orbit `R₀ = ↓⊥`, `R_{k+1} = ↓(R_k ∪ a(R_k) ∪ b⁻¹(R_k))`; ideal orbit `r₀ = ⊥`,
`r_{k+1} = r_k ⊔ a r_k ⊔ ⋁{y | b y ≤ r_k}` (the κ-iteration).
* `step_lax`: `⋁ Θ D ≤ κ⁺ (⋁ D)` for every set `D` (the lax square), hence `orbit_lax`: `⋁ R_k ≤ r_k`.
* `step_principal`: on a principal ideal the square commutes.
* `orbit_tight`: on a top-closed lattice (every down-set containing ⊥ whose join it misses has join ⊤),
  `⋁ R_k = r_k` for all `k` and every `F`.
-/

namespace Mordor
variable {α : Type*} [CompleteLattice α] (F : α →o α →o α)

/-- One inflationary down-set step `Θ⁺ D = ↓(D ∪ a(D) ∪ b⁻¹(D))`. -/
def step (D : Set α) : Set α := {x | ∃ y, x ≤ y ∧ (y ∈ D ∨ (∃ z ∈ D, y = a F z) ∨ b F y ∈ D)}

/-- One inflationary ideal step `κ⁺ r = r ⊔ a r ⊔ ⋁{y | b y ≤ r}`. -/
def kstep (r : α) : α := r ⊔ a F r ⊔ sSup {y | b F y ≤ r}

def Rk (k : ℕ) : Set α := (step F)^[k] (Set.Iic ⊥)
def rk (k : ℕ) : α := (kstep F)^[k] ⊥

variable {F}

theorem step_lax (D : Set α) : sSup (step F D) ≤ kstep F (sSup D) := by
  apply sSup_le
  rintro x ⟨y, hxy, hy | ⟨z, hz, rfl⟩ | hb⟩
  · exact hxy.trans ((le_sSup hy).trans (le_sup_left.trans le_sup_left))
  · exact hxy.trans (((a F).mono (le_sSup hz)).trans (le_sup_right.trans le_sup_left))
  · have hy : y ∈ {y | b F y ≤ sSup D} := le_sSup hb
    exact hxy.trans ((le_sSup hy).trans le_sup_right)

theorem step_principal (s : α) : sSup (step F (Set.Iic s)) = kstep F s := by
  apply le_antisymm
  · simpa using step_lax (F := F) (Set.Iic s)
  · apply sup_le (sup_le _ _) _
    · exact le_sSup ⟨s, le_rfl, Or.inl le_rfl⟩
    · exact le_sSup ⟨a F s, le_rfl, Or.inr (Or.inl ⟨s, le_rfl, rfl⟩)⟩
    · exact sSup_le fun y hy => le_sSup ⟨y, le_rfl, Or.inr (Or.inr hy)⟩

theorem kstep_mono : Monotone (kstep F) := fun _ _ h =>
  sup_le_sup (sup_le_sup h ((a F).mono h)) (sSup_le_sSup fun _ hy => le_trans hy h)

theorem rk_succ (k : ℕ) : rk F (k + 1) = kstep F (rk F k) := Function.iterate_succ_apply' _ _ _
theorem Rk_succ (k : ℕ) : Rk F (k + 1) = step F (Rk F k) := Function.iterate_succ_apply' _ _ _

theorem subset_step (D : Set α) : D ⊆ step F D := fun x hx => ⟨x, le_rfl, Or.inl hx⟩

/-- **The lax square along the orbit.** `⋁ R_k ≤ r_k`. -/
theorem orbit_lax : ∀ k, sSup (Rk F k) ≤ rk F k
  | 0 => by simp [Rk, rk]
  | k + 1 => by
      rw [Rk_succ, rk_succ]
      exact (step_lax _).trans (kstep_mono (orbit_lax k))

theorem Rk_down : ∀ k, IsDown (Rk F k)
  | 0 => fun x y hxy hy => le_trans hxy hy
  | k + 1 => by
      rw [Rk_succ]; exact fun x y hxy ⟨w, hyw, h⟩ => ⟨w, hxy.trans hyw, h⟩

theorem bot_mem_Rk : ∀ k, (⊥ : α) ∈ Rk F k
  | 0 => le_rfl
  | k + 1 => by rw [Rk_succ]; exact subset_step _ (bot_mem_Rk k)

/-- Top-closed: every down-set containing `⊥` that does not contain its own join has join `⊤`
(in a finite lattice: every non-principal down-set has join `⊤`, i.e. `L ∖ {⊤}` is a tree). -/
def TopClosed (α : Type*) [CompleteLattice α] : Prop :=
  ∀ D : Set α, IsDown D → ⊥ ∈ D → sSup D ∉ D → sSup D = ⊤

/-- **Orbit tightness on top-closed lattices (§32.6.3).** -/
theorem orbit_tight (htc : TopClosed α) : ∀ k, sSup (Rk F k) = rk F k
  | 0 => by simp [Rk, rk]
  | k + 1 => by
      have ih := orbit_tight htc k
      rw [Rk_succ, rk_succ]
      by_cases hmem : sSup (Rk F k) ∈ Rk F k
      · -- principal: R_k = ↓(⋁ R_k) and the square commutes
        have hR : Rk F k = Set.Iic (sSup (Rk F k)) :=
          Set.ext fun x => ⟨fun hx => le_sSup hx, fun hx => Rk_down k hx hmem⟩
        rw [hR, step_principal, ih]
      · -- non-principal: both orbits are already at ⊤
        have htop := htc _ (Rk_down k) (bot_mem_Rk k) hmem
        have hr : rk F k = ⊤ := ih.symm.trans htop
        have h1 : sSup (step F (Rk F k)) = ⊤ := by
          apply top_le_iff.mp; rw [← htop]; exact sSup_le_sSup (subset_step _)
        have h2 : kstep F (rk F k) = ⊤ := by
          apply top_le_iff.mp; rw [hr]; exact le_sup_left.trans le_sup_left
        rw [h1, h2]

end Mordor
