import Mordor.Rectangle
import Mathlib.Data.Finset.Image
import Mordor.Stable

/-!
# Boundary steps and support patterns (round 26, §34.3z⁶³)

Response to an outside brief on "provenance": capture processes on the boundary table `Max D × Min Dᶜ`, with
nested versus Δ-system support patterns.

* `boundary_step`, `boundary_step_dual`: a boundary cell `F(p, u)` in `D` has a maximal capturer `p'` with
  `p' ≰ p` (so `p' ≠ p`); dually outside `D`. The brief's transition `T`.
* `support_family`: the dichotomy "every infinite family of finite supports has a nested or a Δ-system
  subsequence" is **false** for unbounded supports. `Aₙ = {0, 2, …, 2n} ∪ {2n+1}` has no two nested members and no
  three members with equal pairwise intersections. The correct statement adds a third pattern: a growing root
  (intersections increasing along an infinite limit set) with disjoint petals.
-/

namespace Mordor.Provenance
open Skeleton Rectangle

section Step
variable {L : Type*} [CompleteLattice L] {F : L → L → L} {D : Set L}

/-- **The boundary step on the `D` side.** -/
theorem boundary_step [WellFoundedGT L] (h : NoWit F D) {p u : L} (hp : p ∈ D) (hu : u ∉ D) (hz : F p u ∈ D) :
    ∃ p', p' ∈ D ∧ (∀ q ∈ D, ¬ p' < q) ∧ F p u ≤ p' ∧ ¬ p' ≤ p := by
  obtain ⟨p', hp'D, hmax, hle⟩ := capturer_exists hz
  exact ⟨p', hp'D, hmax, hle, fun h' => (h p hp u hu).1 (hle.trans h')⟩

/-- **The boundary step on the complement side.** -/
theorem boundary_step_dual [WellFoundedLT L] (h : NoWit F D) {p u : L} (hp : p ∈ D) (hu : u ∉ D)
    (hz : F p u ∉ D) : ∃ u', u' ∉ D ∧ (∀ v, v ∉ D → ¬ v < u') ∧ u' ≤ F p u ∧ ¬ u ≤ u' := by
  obtain ⟨u', hu'D, hmin, hle⟩ := capturer_exists_dual hz
  exact ⟨u', hu'D, hmin, hle, fun h' => (h p hp u hu).2 (h'.trans hle)⟩

end Step

section Supports

/-- `Aₙ = {0, 2, …, 2n} ∪ {2n + 1}`. -/
def A (n : ℕ) : Finset ℕ := (Finset.range (n + 1)).image (2 * ·) ∪ {2 * n + 1}

theorem mem_A {n k : ℕ} : k ∈ A n ↔ (∃ i ≤ n, k = 2 * i) ∨ k = 2 * n + 1 := by
  simp only [A, Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro (⟨i, hi, rfl⟩ | rfl)
    · exact Or.inl ⟨i, by omega, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨i, hi, rfl⟩ | rfl)
    · exact Or.inl ⟨i, by omega, rfl⟩
    · exact Or.inr rfl

/-- **No two members are nested** (in either order). -/
theorem not_nested {n m : ℕ} (h : n ≠ m) : ¬ A n ⊆ A m := by
  intro hs
  rcases mem_A.1 (hs (mem_A.2 (Or.inr rfl))) with ⟨i, -, hi⟩ | hi <;> omega

/-- **No three members form a Δ-system**: for `n < m < k`, `Aₙ ∩ Aₘ ≠ Aₘ ∩ A_k`. -/
theorem not_delta {n m k : ℕ} (hnm : n < m) (hmk : m < k) : A n ∩ A m ≠ A m ∩ A k := by
  intro he
  have h2m : 2 * m ∈ A m ∩ A k :=
    Finset.mem_inter.2 ⟨mem_A.2 (Or.inl ⟨m, le_rfl, rfl⟩), mem_A.2 (Or.inl ⟨m, hmk.le, rfl⟩)⟩
  rw [← he] at h2m
  rcases mem_A.1 (Finset.mem_inter.1 h2m).1 with ⟨i, hi, h⟩ | h <;> omega

/-- **The nested/Δ-system dichotomy fails**: an infinite family of finite sets with no nested pair of distinct
members and no Δ-subsystem of size three. -/
theorem support_family :
    (∀ n m, n ≠ m → ¬ A n ⊆ A m) ∧ (∀ n m k, n < m → m < k → A n ∩ A m ≠ A m ∩ A k) :=
  ⟨fun _ _ h => not_nested h, fun _ _ _ h1 h2 => not_delta h1 h2⟩

end Supports

section Root
variable {L : Type*} [CompleteLattice L]

/-- **Effective root** (§34.3z⁶⁴). For an increasing family of row supports `K n` with union `K`, the meets `⋀ K n`
are eventually `⋀ K` (DCC); so a growing-root support `K n ∪ E n` has meet `⋀ K ⊓ ⋀ E n` from some stage on.
The finite basis is `Stable.sInf_finite_support`, but stabilization alone already gives it. -/
theorem effective_root [WellFoundedLT L] (K E : ℕ → Set L) (hK : Monotone K) :
    ∃ N, ∀ n, N ≤ n → sInf (K n ∪ E n) = sInf (⋃ k, K k) ⊓ sInf (E n) := by
  obtain ⟨t, ht, hinf⟩ := sInf_finite_support (⋃ k, K k)
  have hidx : ∀ x ∈ t, ∃ k, x ∈ K k := fun x hx => Set.mem_iUnion.1 (ht hx)
  choose! idx hidx using hidx
  refine ⟨t.sup idx, fun n hn => ?_⟩
  have hsub : (t : Set L) ⊆ K n := fun x hx => hK ((Finset.le_sup hx).trans hn) (hidx x hx)
  have heq : sInf (K n) = sInf (⋃ k, K k) := le_antisymm
    (hinf ▸ Finset.le_inf fun x hx => sInf_le (hsub hx))
    (sInf_le_sInf (Set.subset_iUnion K n))
  rw [sInf_union, heq]

/-- Dual (ACC): column supports `H n ∪ G n` have join `⋁ H ⊔ ⋁ G n` from some stage on. -/
theorem effective_root_dual [WellFoundedGT L] (H G : ℕ → Set L) (hH : Monotone H) :
    ∃ N, ∀ n, N ≤ n → sSup (H n ∪ G n) = sSup (⋃ k, H k) ⊔ sSup (G n) := by
  obtain ⟨t, ht, hsup⟩ := sSup_finite_support (⋃ k, H k)
  have hidx : ∀ x ∈ t, ∃ k, x ∈ H k := fun x hx => Set.mem_iUnion.1 (ht hx)
  choose! idx hidx using hidx
  refine ⟨t.sup idx, fun n hn => ?_⟩
  have hsub : (t : Set L) ⊆ H n := fun x hx => hH ((Finset.le_sup hx).trans hn) (hidx x hx)
  have heq : sSup (H n) = sSup (⋃ k, H k) := le_antisymm
    (sSup_le_sSup (Set.subset_iUnion H n))
    (hsup ▸ Finset.sup_le fun x hx => le_sSup (hsub hx))
  rw [sSup_union, heq]

end Root
end Mordor.Provenance
