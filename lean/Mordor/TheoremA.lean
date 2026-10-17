import Mordor.Sharpness
import Mordor.Retract
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Fintype.EquivFin

/-!
# Theorem A: a complete lattice containing an infinite chain fails CL (log §23.2)

An infinite chain contains a strictly increasing or strictly decreasing sequence `c`
(`exists_increasing_or_nonincreasing_subseq`). `ℕ∞` (resp. `ℕ∞ᵒᵈ`) is an infinite complete chain, so it fails
CL by `sharpness`; `ι e = ⨆_{n ≤ e} cₙ` (resp. `⨅`) and `σ x = sInf {e | x ≤ ι e}` (resp. `sSup {e | ι e ≤ x}`)
form a retraction pair, and `retract_fail` transports the failure to `L`. The log instead builds the complete
subchain `{⊥} ∪ {cₙ} ∪ {⋁ cₙ, ⊤}` of `L`; with the abstract retract theorem no subchain is needed.
-/

namespace Mordor
open OrderDual

variable {L : Type*} [CompleteLattice L]

/-- A complete chain that is infinite fails CL. -/
theorem fail_of_infinite {C : Type*} [CompleteLinearOrder C] [Infinite C] :
    ∃ F : C →o C →o C, (∀ x, a F (b F x) = b F (a F x)) ∧ m F ≠ n F := by
  by_contra h
  push_neg at h
  haveI := sharpness.mp h
  exact not_finite C

theorem fail_of_retract {C : Type*} [CompleteLinearOrder C] [Infinite C] (ι : C →o L) (σ : L →o C)
    (hσι : ∀ c, σ (ι c) = c) : ∃ F : L →o L →o L, (∀ x, a F (b F x) = b F (a F x)) ∧ m F ≠ n F := by
  obtain ⟨F₀, hc, hne⟩ := fail_of_infinite (C := C)
  exact ⟨_, retract_fail hσι hc hne⟩

instance : Infinite ℕ∞ := Infinite.of_injective (fun n : ℕ => (n : ℕ∞)) Nat.cast_injective
instance : Infinite ℕ∞ᵒᵈ := Infinite.of_injective (fun n : ℕ => toDual (n : ℕ∞))
  (fun _ _ h => Nat.cast_injective (toDual_inj.mp h))

/-- Ascending case. -/
theorem fail_of_strictMono (c : ℕ → L) (hc : StrictMono c) :
    ∃ F : L →o L →o L, (∀ x, a F (b F x) = b F (a F x)) ∧ m F ≠ n F := by
  let ι : ℕ∞ →o L := ⟨fun e => ⨆ (n : ℕ) (_ : (n : ℕ∞) ≤ e), c n,
    fun e e' h => iSup₂_mono' fun n hn => ⟨n, hn.trans h, le_rfl⟩⟩
  have hιk : ∀ k : ℕ, ι k = c k := fun k => le_antisymm
    (iSup₂_le fun n hn => hc.monotone (Nat.cast_le.mp hn)) (le_iSup₂_of_le k le_rfl le_rfl)
  -- ι reflects <
  have hlt : ∀ e e' : ℕ∞, e' < e → ι e' < ι e := by
    intro e e' h
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℕ∞) = e' := ⟨e'.toNat, ENat.coe_toNat (ne_top_of_lt h)⟩
    have hk1 : ((k + 1 : ℕ) : ℕ∞) ≤ e := by
      rw [Nat.cast_add, Nat.cast_one]; exact Order.add_one_le_of_lt h
    rw [hιk]
    exact (hc (Nat.lt_succ_self k)).trans_le (le_iSup₂_of_le (k + 1) hk1 le_rfl)
  let σ : L →o ℕ∞ := ⟨fun x => sInf {e | x ≤ ι e}, fun x x' h => sInf_le_sInf fun e he => h.trans he⟩
  refine fail_of_retract ι σ fun e => le_antisymm (sInf_le le_rfl) (le_sInf fun e' he' => ?_)
  by_contra hne
  exact lt_irrefl _ ((hlt e e' (not_le.mp hne)).trans_le he')

/-- Descending case. -/
theorem fail_of_strictAnti (c : ℕ → L) (hc : StrictAnti c) :
    ∃ F : L →o L →o L, (∀ x, a F (b F x) = b F (a F x)) ∧ m F ≠ n F := by
  let ι : ℕ∞ᵒᵈ →o L := ⟨fun d => ⨅ (n : ℕ) (_ : (n : ℕ∞) ≤ ofDual d), c n,
    fun d d' h => iInf₂_mono' fun n hn => ⟨n, hn.trans (ofDual_le_ofDual.mpr h), le_rfl⟩⟩
  have hιk : ∀ k : ℕ, ι (toDual (k : ℕ∞)) = c k := fun k => le_antisymm
    (iInf₂_le_of_le k le_rfl le_rfl) (le_iInf₂ fun n hn => hc.antitone (Nat.cast_le.mp hn))
  have hlt : ∀ d d' : ℕ∞ᵒᵈ, d < d' → ι d < ι d' := by
    intro d d' h
    have h' : ofDual d' < ofDual d := h
    obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℕ∞) = ofDual d' := ⟨(ofDual d').toNat, ENat.coe_toNat (ne_top_of_lt h')⟩
    have hd' : d' = toDual (k : ℕ∞) := by rw [hk]; rfl
    have hk1 : ((k + 1 : ℕ) : ℕ∞) ≤ ofDual d := by
      rw [Nat.cast_add, Nat.cast_one, hk]; exact Order.add_one_le_of_lt h'
    rw [hd', hιk]
    exact (iInf₂_le_of_le (k + 1) hk1 le_rfl).trans_lt (hc (Nat.lt_succ_self k))
  let σ : L →o ℕ∞ᵒᵈ := ⟨fun x => sSup {d | ι d ≤ x}, fun x x' h => sSup_le_sSup fun d hd => hd.trans h⟩
  refine fail_of_retract ι σ fun d => le_antisymm (sSup_le fun d' hd' => ?_) (le_sSup le_rfl)
  by_contra hne
  exact lt_irrefl _ ((hlt d d' (not_le.mp hne)).trans_le hd')

/-- **Theorem A (Infinite-Chain Criterion).** -/
theorem theoremA (K : Set L) (hK : IsChain (· ≤ ·) K) (hinf : K.Infinite) :
    ∃ F : L →o L →o L, (∀ x, a F (b F x) = b F (a F x)) ∧ m F ≠ n F := by
  haveI : Infinite K := hinf.to_subtype
  let e := Infinite.natEmbedding K
  let f : ℕ → L := fun n => (e n : L)
  have finj : Function.Injective f := fun i j h => e.injective (Subtype.ext h)
  haveI : IsTrans L (· < ·) := ⟨fun _ _ _ => lt_trans⟩
  obtain ⟨g, hup | hdown⟩ := exists_increasing_or_nonincreasing_subseq (· < ·) f
  · exact fail_of_strictMono (f ∘ g) fun i j hij => hup i j hij
  · refine fail_of_strictAnti (f ∘ g) fun i j hij => ?_
    have hne : f (g i) ≠ f (g j) := fun h => hij.ne (g.injective (finj h))
    rcases hK (e (g i)).2 (e (g j)).2 hne with h | h
    · exact absurd (lt_of_le_of_ne h hne) (hdown i j hij)
    · exact lt_of_le_of_ne h hne.symm

/-- **Corollary (§23.2).** A complete lattice satisfying CL is chain-finite. -/
theorem chainFinite_of_CL (hCL : ∀ F : L →o L →o L, (∀ x, a F (b F x) = b F (a F x)) → m F = n F)
    (K : Set L) (hK : IsChain (· ≤ ·) K) : K.Finite := by
  by_contra hinf
  obtain ⟨F, hc, hne⟩ := theoremA K hK hinf
  exact hne (hCL F hc)

end Mordor
