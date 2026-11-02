import Mordor.CrossCellInduction

/-!
# The finite meet-row net (round 26, §34.3z⁸⁵)

Response to the brief "from a frontier ladder to a finite net". For a nonempty generator set `A`, `m_A = ⋀_A p` and
`h_A = F m_A`; every `h_A`-orbit of `⊤` descends and enters `D` (`orbit_end`).

* `net_entry`: the first entry of `h_A` from `⊤`, with label `Λ_A` nonempty and `A ⊄ Λ_A` (`endpoint_not_le`).
* `net_time_mono`, `net_equal_time`: `A ⊆ B` gives `τ B ≤ τ A`, and at equal times `Λ_A ⊆ Λ_B` (`entry_mono`,
  `entry_eq_le`).
* `net_sync`: **synchronization at equal times**: `h_B^n ⊤ ≤ h_A^n ⊤` for `A ⊆ B`, so at the column
  `y = h_U^n ⊤` (`U` the union of a family) every row `m_A` (`A` in the family) satisfies `F m_A y ≤ h_A^{n+1} ⊤`.
* `net_no_closed`: hence no family of meet rows is closed by its time-`(n+1)` values while `h_U^n ⊤ ∉ D`.
  For two generators this excludes exactly the profile `τ₁ = τ₂ = τ₁₂` (`net_two_equal`). All other two-generator
  profiles are consistent with the net (z3, `experiments/net/net_profile.py`): the net is the profile at `⊤`, and the
  relation it omits is the sandwich's shifted comparison of orbits from different starting columns.
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF nw in
/-- **First entry of a meet-row orbit**, with its label restrictions. -/
theorem net_entry [WellFoundedLT α] (htop : ¬ ∃ i, ⊤ ≤ p i) {A : Finset ι} (hA : A.Nonempty) :
    ∃ n, EntersAt (F (A.inf p)) (fun x => ∃ i, x ≤ p i) ⊤ n ∧
      (∃ i, (F (A.inf p))^[n + 1] ⊤ ≤ p i) ∧ ∃ a ∈ A, ¬ (F (A.inf p))^[n + 1] ⊤ ≤ p a := by
  obtain ⟨a₀, ha₀⟩ := hA
  have hD : ∃ i, A.inf p ≤ p i := ⟨a₀, Finset.inf_le ha₀⟩
  obtain ⟨n, hU, hin⟩ := FGTwo.orbit_end (InD := fun x => ∃ i, x ≤ p i) hF hD nw ⊤ htop le_top
  have hE : EntersAt (F (A.inf p)) (fun x => ∃ i, x ≤ p i) ⊤ n :=
    ⟨hU, by rw [Function.iterate_succ_apply']; exact hin⟩
  refine ⟨n, hE, hE.2, ?_⟩
  by_contra hall
  push_neg at hall
  exact endpoint_not_le nw hD hE (Finset.le_inf fun a ha => hall a ha)

include hF in
theorem net_time_mono {A B : Finset ι} (hAB : A ⊆ B) {n n' : ℕ}
    (hEA : EntersAt (F (A.inf p)) (fun x => ∃ i, x ≤ p i) ⊤ n)
    (hEB : EntersAt (F (B.inf p)) (fun x => ∃ i, x ≤ p i) ⊤ n') : n' ≤ n :=
  entry_mono hF (fun _ _ hxy ⟨i, hi⟩ => ⟨i, hxy.trans hi⟩) (Finset.inf_mono (f := p) hAB) hEB hEA

include hF in
/-- At equal entry times the larger set's entry is below the smaller set's, so it carries every label of it. -/
theorem net_equal_time {A B : Finset ι} (hAB : A ⊆ B) (n : ℕ) {i : ι}
    (hi : (F (A.inf p))^[n + 1] ⊤ ≤ p i) : (F (B.inf p))^[n + 1] ⊤ ≤ p i :=
  (entry_eq_le hF (Finset.inf_mono (f := p) hAB) (n := n) (s := ⊤)).trans hi

include hF in
/-- **Synchronization at equal times.** -/
theorem net_sync {A B : Finset ι} (hAB : A ⊆ B) (n : ℕ) :
    (F (B.inf p))^[n] ⊤ ≤ (F (A.inf p))^[n] ⊤ ∧
      F (A.inf p) ((F (B.inf p))^[n] ⊤) ≤ (F (A.inf p))^[n + 1] ⊤ := by
  have h := iterate_le hF (Finset.inf_mono (f := p) hAB) ⊤ n
  exact ⟨h, by rw [Function.iterate_succ_apply']; exact hF _ _ _ _ le_rfl h⟩

include hF nw in
/-- **No closed family at a synchronized column.** -/
theorem net_no_closed (𝒜 : Finset (Finset ι)) (hne : 𝒜.Nonempty) (hA : ∀ A ∈ 𝒜, A.Nonempty) (n : ℕ)
    (hout : ¬ ∃ i, (F ((𝒜.sup id).inf p))^[n] ⊤ ≤ p i)
    (hcl : ∀ A ∈ 𝒜, ∃ B ∈ 𝒜, (F (A.inf p))^[n + 1] ⊤ ≤ B.inf p) : False := by
  refine no_closed_meet_family hF p nw hout 𝒜 hne hA fun A hA' => ?_
  obtain ⟨B, hB, hle⟩ := hcl A hA'
  have hsub : A ⊆ 𝒜.sup id := Finset.le_sup (f := id) hA'
  exact ⟨B, hB, (net_sync hF p hsub n).2.trans hle⟩

include hF in
/-- **Two generators: the only profile the net excludes.** If the orbits of `p₀`, `p₁` and `p₀ ⊓ p₁` all enter at the
same time, the closed family `{{0}, {1}}` at the last outside point of the meet orbit is a contradiction. -/
theorem net_two_equal (p : Fin 2 → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {n : ℕ}
    (hout : ¬ ∃ i, (F (p 0 ⊓ p 1))^[n] ⊤ ≤ p i)
    (h0 : (F (p 0))^[n + 1] ⊤ ≤ p 1) (h1 : (F (p 1))^[n + 1] ⊤ ≤ p 0) : False := by
  have hU : (({{0}, {1}} : Finset (Finset (Fin 2))).sup id).inf p = p 0 ⊓ p 1 := by
    rw [show (({{0}, {1}} : Finset (Finset (Fin 2))).sup id) = Finset.univ by decide]
    rw [show (Finset.univ : Finset (Fin 2)) = {0, 1} by decide]; simp
  refine net_no_closed hF p nw {{0}, {1}} ⟨{0}, by simp⟩ (by simp) n (by rwa [hU]) fun A hA => ?_
  rcases Finset.mem_insert.1 hA with rfl | hA1
  · exact ⟨{1}, by simp, by simpa using h0⟩
  · rw [Finset.mem_singleton.1 hA1]; exact ⟨{0}, by simp, by simpa using h1⟩

end Mordor.Profile
