import Mordor.BoundedSupportPivot
import Mordor.LocalizedCut
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Axis-capture graphs (round 26, §34.3z¹¹⁷)

ChatGPT brief "axis-capture graphs, bounded support and the height-six obstruction", Program A.

Rows `gᵢ ∈ D`, orbits `uᵢ(n) = F(gᵢ, ·)ⁿ(⊤)`, first-entry times `Eᵢ` (`uᵢ(Eᵢ) ∈ D`, `uᵢ(m) ∉ D` for `m < Eᵢ`),
entry points `eᵢ = uᵢ(Eᵢ)`. Axis-capture graph: `i → j ⟺ eᵢ ≤ gⱼ`.

* `entry_pos`, `no_loop`: `Eᵢ ≥ 1` and `eᵢ ≰ gᵢ` (the graph is loopless).
* `axis_le_entry`, `interior_iff`: `uᵢ(n) ∈ D ⟺ Eᵢ ≤ n`, and then `uᵢ(n) ≤ eᵢ`.
* `axis_escape_iff`: some `D`-valued axis point of row `i` is uncaptured ⟺ vertex `i` has out-degree `0`.
* `axis_or_mixed` (A2): either some vertex has out-degree `0` (Situation I, an axis escape), or there is an
  **interior** uncaptured column (`tᵢ < Eᵢ` for all `i`) with a nonempty `T` and `F(m_T, c) ≤ m_T`.
* `exists_cycle`: in Situation II the graph has a directed cycle (of length ≥ 2, by `no_loop`).
* `mixed_minimal_support` (A2 + B1): in Situation II at edge-height ≤ `H`, some interior uncaptured column has a
  minimal support `S` with `2 ≤ |S|`, `|S| + 1 ≤ H`, and `tᵢ + |S| ≤ H` for `i ∈ S`.
* `new_maximum` (A3): if the rows are maximal in `D`, every uncaptured `c ∈ D` lies below a maximal `q ∈ D`
  incomparable with every row.
The opposite-boundary facts of A4 are `InfCapture.maximal_pairwise_join_outside` / `minimal_pairwise_meet_inside`.
-/

namespace Mordor.AxisCapture
open Finset Mordor.AsyncGrid Mordor.BoundedSupport

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {k : ℕ} {F : α → α → α}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set α}
  (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (htop : ⊤ ∉ D)
  (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (g : Fin k → α) (hg : ∀ i, g i ∈ D)
  (E : Fin k → ℕ) (hE : ∀ i, (F (g i))^[E i] ⊤ ∈ D) (hEmin : ∀ i, ∀ m < E i, (F (g i))^[m] ⊤ ∉ D)

include hF in
theorem orbit_anti (i : Fin k) : Antitone fun n => (F (g i))^[n] ⊤ :=
  Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) le_top

include htop hE in
theorem entry_pos (i : Fin k) : 1 ≤ E i := by
  rcases Nat.eq_zero_or_pos (E i) with h | h
  · exact absurd (by simpa [h] using hE i) htop
  · exact h

include htop nw hg hE hEmin in
/-- Loopless: `eᵢ ≰ gᵢ`. -/
theorem no_loop (i : Fin k) : ¬ (F (g i))^[E i] ⊤ ≤ g i := by
  have h1 := entry_pos htop g E hE i
  have heq : E i = (E i - 1) + 1 := by omega
  rw [heq, Function.iterate_succ_apply']
  exact (nw _ (hg i) _ (hEmin i _ (by omega))).1

include hF hD hE hEmin in
theorem interior_iff (i : Fin k) (n : ℕ) : (F (g i))^[n] ⊤ ∈ D ↔ E i ≤ n := by
  constructor
  · intro h; by_contra hlt; exact hEmin i n (by omega) h
  · intro h; exact hD _ _ (orbit_anti hF g i h) (hE i)

include hF in
theorem axis_le_entry (i : Fin k) {n : ℕ} (h : E i ≤ n) : (F (g i))^[n] ⊤ ≤ (F (g i))^[E i] ⊤ :=
  orbit_anti hF g i h

include hF hD hE hEmin in
/-- Axis escape ⟺ out-degree `0`. -/
theorem axis_escape_iff (i : Fin k) :
    (∃ n, (F (g i))^[n] ⊤ ∈ D ∧ ∀ j, ¬ (F (g i))^[n] ⊤ ≤ g j) ↔ ∀ j, ¬ (F (g i))^[E i] ⊤ ≤ g j := by
  constructor
  · rintro ⟨n, hn, hunc⟩ j hj
    exact hunc j ((axis_le_entry hF g E i ((interior_iff hF hD g E hE hEmin i n).1 hn)).trans hj)
  · intro h; exact ⟨E i, hE i, h⟩

include hF hD htop nw hg hE hEmin in
/-- **A2: axis escape or interior mixed pivot.** -/
theorem axis_or_mixed [WellFoundedLT α] (hk : 0 < k) :
    (∃ i, ∀ j, ¬ (F (g i))^[E i] ⊤ ≤ g j) ∨
    ∃ t : Fin k → ℕ, W (fun i m => (F (g i))^[m] ⊤) t ∈ D ∧ (∀ i, ¬ W (fun i m => (F (g i))^[m] ⊤) t ≤ g i) ∧
      (∀ i, t i < E i) ∧
      ∃ T : Finset (Fin k), T.Nonempty ∧ F (T.inf g) (W (fun i m => (F (g i))^[m] ⊤) t) ≤ T.inf g := by
  by_cases hI : ∃ i, ∀ j, ¬ (F (g i))^[E i] ⊤ ≤ g j
  · exact Or.inl hI
  · right
    push_neg at hI
    obtain ⟨t, htD, hunc, hint, T, hT, halt⟩ := Mordor.LocalizedCut.interior_row_contraction hk hF hD htop g hg nw
      (fun t ⟨i, hi⟩ => by
        obtain ⟨j, hj⟩ := hI i
        exact ⟨j, (W_le _ t i).trans ((axis_le_entry hF g E i
          ((interior_iff hF hD g E hE hEmin i (t i)).1 hi)).trans hj)⟩)
    refine ⟨t, htD, hunc, fun i => ?_, T, hT, halt⟩
    by_contra hge; exact hint i ((interior_iff hF hD g E hE hEmin i (t i)).2 (by omega))

/-- **Situation II has a directed cycle.** Any out-neighbour choice `σ` has a periodic point. -/
theorem exists_cycle (hk : 0 < k) (σ : Fin k → Fin k) : ∃ i, ∃ n, 1 ≤ n ∧ σ^[n] i = i := by
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => σ^[n] ⟨0, hk⟩)
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · refine ⟨σ^[a] ⟨0, hk⟩, b - a, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]; exact he.symm
  · refine ⟨σ^[b] ⟨0, hk⟩, a - b, by omega, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel h.le]; exact he

include hF hD htop nw hg hE hEmin in
/-- **A2 + B1.** In Situation II at edge-height ≤ `H`, an interior uncaptured column has a minimal support `S` with
`2 ≤ |S| ≤ H - 1` and `tᵢ + |S| ≤ H` on `S`. -/
theorem mixed_minimal_support [WellFoundedLT α] (hk : 0 < k) {H : ℕ} (hH : Mordor.Ground.NoChain α (H + 1))
    (hII : ∀ i, ∃ j, (F (g i))^[E i] ⊤ ≤ g j) :
    ∃ t : Fin k → ℕ, (∀ i, t i < E i) ∧ ∃ S : Finset (Fin k),
      Good (D := D) g (S.inf fun i => (F (g i))^[t i] ⊤) ∧
      (∀ S' ⊂ S, ¬ Good (D := D) g (S'.inf fun i => (F (g i))^[t i] ⊤)) ∧
      2 ≤ S.card ∧ S.card + 1 ≤ H ∧ ∀ i ∈ S, t i + S.card ≤ H := by
  rcases axis_or_mixed hF hD htop nw g hg E hE hEmin hk with ⟨i, hi⟩ | ⟨t, htD, hunc, hint, -⟩
  · obtain ⟨j, hj⟩ := hII i; exact absurd hj (hi j)
  set v : Fin k → α := fun i => (F (g i))^[t i] ⊤
  obtain ⟨S, -, hS, hmin⟩ := exists_minimal_support (P := Good (D := D) g) (v := v) (S₀ := univ) ⟨htD, hunc⟩
  have h2 : 2 ≤ S.card := by
    by_contra hlt
    rcases Nat.lt_or_ge S.card 1 with h0 | h1
    · have : S = ∅ := Finset.card_eq_zero.1 (by omega)
      exact htop (by simpa [this] using hS.1)
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 (show S.card = 1 by omega)
      have := hS.1; rw [Finset.inf_singleton] at this
      exact absurd ((interior_iff hF hD g E hE hEmin i (t i)).1 this) (by have := hint i; omega)
  exact ⟨t, hint, S, hS, hmin, h2, minimal_support_card hH hS hmin (not_good_bot g hk),
    fun i hi => orbit_support_bound g hH hk hF hD nw hg t hS hmin h2 hi⟩

include hD in
/-- **A3.** Below every uncaptured `c ∈ D` sits a maximal `q ∈ D` incomparable with every (maximal) row. -/
theorem new_maximum [WellFoundedGT α] (hmax : ∀ i, ∀ x ∈ D, g i ≤ x → x = g i) {c : α} (hc : c ∈ D)
    (hunc : ∀ i, ¬ c ≤ g i) :
    ∃ q ∈ D, c ≤ q ∧ (∀ x ∈ D, q ≤ x → x = q) ∧ ∀ i, ¬ q ≤ g i ∧ ¬ g i ≤ q := by
  obtain ⟨q, hq, hcq, hqmax⟩ := Mordor.InfCapture.exists_maximal_above (D := D) hc
  refine ⟨q, hq, hcq, hqmax, fun i => ⟨fun h => hunc i (hcq.trans h), fun h => ?_⟩⟩
  exact hunc i (hcq.trans (hmax i q hq h).le)

end Mordor.AxisCapture
