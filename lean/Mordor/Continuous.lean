import Mordor.Derived
import Mathlib.Data.ENat.Lattice

/-!
# A continuous counterexample to CL on ω + 1 (log §34.3i)

The foundations postulate M0: the signature preserves ω-colimits and ω-limits of chains. The counterexamples behind
Sharpness and Theorem A (§22–§23, `Sharpness.lean`) are not continuous: the ladder has `F x ω = s x` while
`F x n = x` for every `n < ω`. So they do not refute the foundations' claim (I2, I5) that one-step commutation
suffices *under M0*. This file does: on `ℕ∞ = ω + 1`,

  `F x y = min (x + 1) (y - 1)`   (truncated subtraction, `⊤ ± 1 = ⊤`)

preserves sups of monotone sequences and infs of antitone sequences, jointly, and has `a x = 0` for `x < ω`,
`a ω = ω`, `b y = y - 1`. Hence `a ∘ b = b ∘ a`, while `m = 0 ≠ ω = n`.
-/

namespace Mordor.Continuous
open ENat

/-- `F x y = min (x + 1) (y - 1)` on `ℕ∞`. -/
noncomputable def F : ℕ∞ →o ℕ∞ →o ℕ∞ :=
  ⟨fun x => ⟨fun y => min (x + 1) (y - 1), fun _ _ h => by dsimp only; gcongr⟩,
   fun _ _ h _ => by dsimp only; gcongr⟩

theorem F_apply (x y : ℕ∞) : F x y = min (x + 1) (y - 1) := rfl

/-! ### M0: continuity -/

/-- `y ↦ y - 1` is a left adjoint (`y - 1 ≤ z ↔ y ≤ z + 1`), so it preserves all sups. -/
theorem gc_sub : GaloisConnection (fun y : ℕ∞ => y - 1) (fun z => z + 1) := fun _ _ => tsub_le_iff_right

/-- `F` preserves sups of monotone sequences, jointly in both arguments. -/
theorem F_iSup (c d : ℕ → ℕ∞) (hc : Monotone c) (hd : Monotone d) :
    F (⨆ i, c i) (⨆ i, d i) = ⨆ i, F (c i) (d i) := by
  simp only [F_apply, ENat.iSup_add, gc_sub.l_iSup]
  exact (iSup_inf_of_monotone (fun i j h => by gcongr; exact hc h)
    (fun i j h => by gcongr; exact hd h)).symm

/-- `F` preserves infs of antitone sequences (automatic: `ℕ∞` is well-founded, so the infs are attained). -/
theorem F_iInf (c d : ℕ → ℕ∞) (hc : Antitone c) (hd : Antitone d) :
    F (⨅ i, c i) (⨅ i, d i) = ⨅ i, F (c i) (d i) := by
  obtain ⟨i, hi⟩ : ∃ i, c i = ⨅ i, c i := ⟨_, (ciInf_mem c).choose_spec⟩
  obtain ⟨j, hj⟩ : ∃ j, d j = ⨅ i, d i := ⟨_, (ciInf_mem d).choose_spec⟩
  refine le_antisymm (le_iInf fun k => (F.mono (iInf_le c k) (⨅ i, d i)).trans ((F (c k)).mono (iInf_le d k))) ?_
  · have h1 : c (max i j) = ⨅ i, c i := le_antisymm (hi ▸ hc (le_max_left i j)) (iInf_le _ _)
    have h2 : d (max i j) = ⨅ i, d i := le_antisymm (hj ▸ hd (le_max_right i j)) (iInf_le _ _)
    rw [← h1, ← h2]; exact iInf_le (fun k => F (c k) (d k)) (max i j)

/-! ### The derived maps -/

theorem a_F (x : ℕ∞) : a F x = if x = ⊤ then ⊤ else 0 := by
  revert x
  refine (a_eq_iff (F := F) (fun x => if x = ⊤ then ⊤ else 0)).2 fun x => ⟨?_, fun y hy => ?_⟩
  · by_cases hx : x = ⊤ <;> simp [F_apply, hx]
  · by_cases hx : x = ⊤
    · simp [hx]
    · simp only [hx, if_false, nonpos_iff_eq_zero]
      rw [F_apply] at hy
      induction x using ENat.recTopCoe with
      | top => exact absurd rfl hx
      | coe p =>
        induction y using ENat.recTopCoe with
        | top => simp at hy; exact absurd hy (by exact_mod_cast ENat.coe_ne_top (p + 1))
        | coe q =>
          have : min ((p : ℕ∞) + 1) ((q : ℕ∞) - 1) = ((min (p + 1) (q - 1) : ℕ) : ℕ∞) := rfl
          rw [this] at hy; have := ENat.coe_inj.mp hy; norm_cast; omega

theorem b_F (y : ℕ∞) : b F y = y - 1 := by
  revert y
  refine (b_eq_iff (F := F) (fun y => y - 1)).2 fun y => ⟨?_, fun x hx => ?_⟩
  · rw [F_apply]; exact min_eq_right le_self_add
  · rw [F_apply] at hx
    induction x using ENat.recTopCoe with
    | top => exact le_top
    | coe p =>
      rcases min_choice ((p : ℕ∞) + 1) (y - 1) with h | h
      · rw [h] at hx; exact absurd hx (by norm_cast; omega)
      · rw [h] at hx; exact hx.le

/-- **Commutation holds.** -/
theorem comm (x : ℕ∞) : a F (b F x) = b F (a F x) := by
  rw [a_F, b_F, a_F, b_F]
  by_cases hx : x = ⊤
  · simp [hx]
  · have : x - 1 ≠ ⊤ := fun h => hx (by simpa using (ENat.sub_eq_top_iff.mp h).1)
    simp [hx, this]

theorem m_F : m F = 0 := le_antisymm ((a F).lfp_le (by rw [a_F]; simp)) bot_le
theorem n_F : n F = ⊤ := le_antisymm le_top ((b F).le_gfp (by rw [b_F]; simp))

/-- **CL fails on ω + 1 for an M0-continuous `F`.** -/
theorem cl_fails_continuous :
    (∀ c d : ℕ → ℕ∞, Monotone c → Monotone d → F (⨆ i, c i) (⨆ i, d i) = ⨆ i, F (c i) (d i)) ∧
    (∀ c d : ℕ → ℕ∞, Antitone c → Antitone d → F (⨅ i, c i) (⨅ i, d i) = ⨅ i, F (c i) (d i)) ∧
    (∀ x, a F (b F x) = b F (a F x)) ∧ m F ≠ n F :=
  ⟨F_iSup, F_iInf, comm, by rw [m_F, n_F]; exact ENat.zero_ne_top⟩

end Mordor.Continuous
