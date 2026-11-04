import Mordor.ResponsePalette

/-!
# Paired generator/anchor orbits and their endpoints (round 26, §34.3z¹⁰⁴)

`D = ⋃ᵢ ↓gᵢ`, `cᵢ = anchor g i ≤ gᵢ`, `s ∉ D` contracting for every generator row.

* `paired_orbit_order`, `paired_entry_order`: `(F cᵢ)^[n] s ≤ (F gᵢ)^[n] s`, so the anchor orbit enters no later.
* `two_common_outside`: two indices with `F cᵢ s, F gᵢ s, F cⱼ s, F gⱼ s ∉ D` (from `two_outside_anchor_responses`).
* `paired_endpoint_responses`: at the last outside point `vᵢ` of the `gᵢ`-orbit, `F gᵢ vᵢ ∈ D \ ↓gᵢ` and
  `F cᵢ vᵢ ∈ D \ ↓gᵢ` (`anchor_sandwich` at `vᵢ`), so the endpoint label set `Λᵢ` is nonempty and avoids `i`.
* `endpoint_closed_meet_in_D`: for any set `T` of indices closed under endpoint labels, `⨅_T vᵢ ∈ D`
  (`no_upward_transfer_cycle`); `endpoint_two_cycle` (`T = {i, j}`); **`endpoint_total_meet_in_D`**: the meet of all
  generator endpoints is in `D` (the generator-orbit analogue of `lastpoints_no_common_lower`).
* `labels_sub_palette`: `Λᵢ ⊆ Π(vᵢ)`.
* `three_cycle_of_no_two_cycle`, `three_endpoint_cycle`: for three generators with all pairwise endpoint meets outside
  `D`, any choice of one label per endpoint is a Hamiltonian 3-cycle (and the triple meet is in `D` regardless).
* **`palette_cycle_rigidity`**: in that case every endpoint palette is the singleton `{σ i}` (`Λᵢ = Πᵢ = {σ i}`).
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

/-- A fixed-point-free map of `Fin 3` without 2-cycles is a 3-cycle. -/
theorem three_cycle_of_no_two_cycle :
    ∀ σ : Fin 3 → Fin 3, (∀ i, σ i ≠ i) → (∀ i, σ (σ i) ≠ i) → ∀ i, σ (σ (σ i)) = i := by decide

section Paired

variable {α : Type*} [CompleteLattice α] {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (g : κ → α)
  (nw' : ∀ x, (∃ i, x ≤ g i) → ∀ y, ¬ (∃ i, y ≤ g i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF in
/-- **Paired iteration dominance.** -/
theorem paired_orbit_order {c d : α} (hcd : c ≤ d) (s : α) (n : ℕ) : (F c)^[n] s ≤ (F d)^[n] s := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact hF _ _ _ _ hcd ih

include hF in
/-- **The smaller row enters no later.** -/
theorem paired_entry_order {c d s : α} (hcd : c ≤ d) {nc nd : ℕ}
    (hEc : EntersAt (F c) (fun x => ∃ i, x ≤ g i) s nc) (hEd : EntersAt (F d) (fun x => ∃ i, x ≤ g i) s nd) :
    nc ≤ nd := by
  by_contra h
  push_neg at h
  obtain ⟨k, hk⟩ := hEd.2
  exact hEc.1 (nd + 1) (by omega) ⟨k, (paired_orbit_order hF hcd s (nd + 1)).trans hk⟩

include hF nw' in
/-- **Two common outside indices.** -/
theorem two_common_outside [WellFoundedLT α] [Nonempty κ] {s : α} (hs : ¬ ∃ i, s ≤ g i)
    (hgs : ∀ i, F (g i) s ≤ s) :
    ∃ i j, i ≠ j ∧ (¬ ∃ k, F (anchor g i) s ≤ g k) ∧ (¬ ∃ k, F (g i) s ≤ g k) ∧
      (¬ ∃ k, F (anchor g j) s ≤ g k) ∧ ¬ ∃ k, F (g j) s ≤ g k := by
  obtain ⟨i, j, hij, hi, hj⟩ := two_outside_anchor_responses hF g nw' hs hgs
  have up : ∀ l, (¬ ∃ k, F (anchor g l) s ≤ g k) → ¬ ∃ k, F (g l) s ≤ g k := fun l h ⟨k, hk⟩ =>
    h ⟨k, (hF _ _ _ _ (anchor_le g l) le_rfl).trans hk⟩
  exact ⟨i, j, hij, hi, up i hi, hj, up j hj⟩

include hF nw' in
/-- **Paired endpoint responses** at the last outside point `v` of the `gᵢ`-orbit of `s`. -/
theorem paired_endpoint_responses [WellFoundedLT α] {s : α} (i : κ) (hgs : F (g i) s ≤ s) {n : ℕ}
    (hE : EntersAt (F (g i)) (fun x => ∃ j, x ≤ g j) s n) :
    (¬ ∃ j, (F (g i))^[n] s ≤ g j) ∧ F (g i) ((F (g i))^[n] s) ≤ (F (g i))^[n] s ∧
      (∃ j, F (g i) ((F (g i))^[n] s) ≤ g j) ∧ ¬ F (g i) ((F (g i))^[n] s) ≤ g i ∧
      (∃ j, j ≠ i ∧ F (anchor g i) ((F (g i))^[n] s) ≤ g j) ∧ ¬ F (anchor g i) ((F (g i))^[n] s) ≤ g i := by
  have hv := hE.1 n le_rfl
  have hin : ∃ j, F (g i) ((F (g i))^[n] s) ≤ g j := by
    have := hE.2; rwa [Function.iterate_succ_apply'] at this
  have hcon : F (g i) ((F (g i))^[n] s) ≤ (F (g i))^[n] s := by
    have : (F (g i))^[n + 1] s ≤ (F (g i))^[n] s :=
      Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) hgs (Nat.le_succ n)
    rwa [Function.iterate_succ_apply'] at this
  have hsand : ¬ F (anchor g i) ((F (g i))^[n] s) ≤ g i := by
    have := anchor_sandwich hF g i nw' hv hcon 0 (fun m hm => by rw [show m = 0 by omega]; simpa using hv)
    simpa using this
  obtain ⟨j, hj⟩ := hin
  have hcj : F (anchor g i) ((F (g i))^[n] s) ≤ g j := (hF _ _ _ _ (anchor_le g i) le_rfl).trans hj
  exact ⟨hv, hcon, ⟨j, hj⟩, (nw' _ ⟨i, le_rfl⟩ _ hv).1,
    ⟨j, fun h => hsand (h ▸ hcj), hcj⟩, hsand⟩

include hF nw' in
/-- **Label-closed endpoint sets have their meet in `D`.** -/
theorem endpoint_closed_meet_in_D (v : κ → α) (T : Finset κ) (hT : T.Nonempty) {u : α}
    (hu : ¬ ∃ j, u ≤ g j) (hlow : ∀ a ∈ T, u ≤ v a)
    (hlab : ∀ a ∈ T, ∃ k ∈ T, k ≠ a ∧ F (anchor g a) (v a) ≤ g k) : False :=
  no_upward_transfer_cycle hF g nw' hu T hT fun a ha => by
    obtain ⟨k, hk, hka, h⟩ := hlab a ha
    exact ⟨k, hk, hka, v a, hlow a ha, h⟩

include hF nw' in
/-- **No endpoint 2-cycle with outside meet.** -/
theorem endpoint_two_cycle (v : κ → α) {i j : κ} (hij : i ≠ j) (hi : F (anchor g i) (v i) ≤ g j)
    (hj : F (anchor g j) (v j) ≤ g i) : ∃ k, v i ⊓ v j ≤ g k := by
  by_contra hout
  refine endpoint_closed_meet_in_D hF g nw' v {i, j} ⟨i, by simp⟩ hout (fun a ha => ?_) (fun a ha => ?_)
  · rcases Finset.mem_insert.1 ha with rfl | ha
    · exact inf_le_left
    · rw [Finset.mem_singleton.1 ha]; exact inf_le_right
  · rcases Finset.mem_insert.1 ha with rfl | ha
    · exact ⟨j, by simp, Ne.symm hij, hi⟩
    · have ha' := Finset.mem_singleton.1 ha; subst ha'; exact ⟨i, by simp, hij, hj⟩

include hF nw' in
/-- **The meet of all generator endpoints is in `D`.** -/
theorem endpoint_total_meet_in_D [WellFoundedLT α] [Nonempty κ] {s : α} (hgs : ∀ i, F (g i) s ≤ s) (n : κ → ℕ)
    (hE : ∀ i, EntersAt (F (g i)) (fun x => ∃ j, x ≤ g j) s (n i)) :
    ∃ k, Finset.univ.inf (fun i => (F (g i))^[n i] s) ≤ g k := by
  by_contra hout
  obtain ⟨i₀⟩ := ‹Nonempty κ›
  refine endpoint_closed_meet_in_D hF g nw' (fun i => (F (g i))^[n i] s) Finset.univ ⟨i₀, Finset.mem_univ _⟩ hout
    (fun a _ => Finset.inf_le (f := fun i => (F (g i))^[n i] s) (Finset.mem_univ a)) (fun a _ => ?_)
  obtain ⟨-, -, -, -, ⟨j, hja, hj⟩, -⟩ := paired_endpoint_responses hF g nw' a (hgs a) (hE a)
  exact ⟨j, Finset.mem_univ _, hja, hj⟩

include hF in
/-- **Endpoint labels lie in the palette.** -/
theorem labels_sub_palette [Nontrivial κ] (i : κ) (y : α) : labels F g (anchor g i) y ⊆ palette F g y := by
  obtain ⟨j, hj⟩ := exists_ne i
  refine palette_response_subset hF g (le_trans ?_ (Finset.le_sup (f := fun l => g i ⊓ g l)
    (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)))
  exact le_inf (Finset.inf_le (Finset.mem_univ i)) (Finset.inf_le (Finset.mem_univ j))

end Paired

/-- **Three endpoints with outside pairwise meets carry a Hamiltonian label cycle.** -/
theorem three_endpoint_cycle {α : Type*} [CompleteLattice α] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (g : Fin 3 → α)
    (nw' : ∀ x, (∃ i, x ≤ g i) → ∀ y, ¬ (∃ i, y ≤ g i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (v : Fin 3 → α)
    (σ : Fin 3 → Fin 3) (hσ : ∀ i, σ i ≠ i ∧ F (anchor g i) (v i) ≤ g (σ i))
    (hmeet : ∀ i j, i ≠ j → ¬ ∃ k, v i ⊓ v j ≤ g k) : ∀ i, σ (σ (σ i)) = i := by
  refine three_cycle_of_no_two_cycle σ (fun i => (hσ i).1) fun i h2 => ?_
  have hne : σ i ≠ i := (hσ i).1
  exact hmeet i (σ i) (Ne.symm hne) (endpoint_two_cycle hF g nw' v (Ne.symm hne) (hσ i).2
    (by have := (hσ (σ i)).2; rwa [h2] at this))

theorem fin3_three_elements :
    ∀ S : Finset (Fin 3), ∀ a b c : Fin 3, a ∈ S → b ∈ S → c ∈ S → a ≠ b → a ≠ c → b ≠ c → S = Finset.univ := by
  decide

theorem fin3_cycle_pick :
    ∀ σ : Fin 3 → Fin 3, (∀ i, σ i ≠ i) → (∀ i, σ (σ (σ i)) = i) →
      ∀ i j : Fin 3, (∀ k, k ≠ i → j = σ i ∨ j = σ k) → j = σ i := by
  decide

theorem fin3_cycle_injective :
    ∀ σ : Fin 3 → Fin 3, (∀ i, σ i ≠ i) → (∀ i, σ (σ (σ i)) = i) → ∀ i k, i ≠ k → σ i ≠ σ k := by
  decide

/-- **Palette rigidity of an endpoint 3-cycle.** If all pairwise endpoint meets are outside `D` and `σ` selects
endpoint labels, then every endpoint palette is the singleton `{σ i}` (so `Λᵢ = Πᵢ = {σ i}`): the pairwise-meet
palettes `Π(vᵢ ⊓ v_k) ⊇ Π(vᵢ) ∪ Π(v_k) ∋ σ i, σ k` are proper, hence equal to `{σ i, σ k}`. -/
theorem palette_cycle_rigidity {α : Type*} [CompleteLattice α] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (g : Fin 3 → α)
    (nw' : ∀ x, (∃ i, x ≤ g i) → ∀ y, ¬ (∃ i, y ≤ g i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (v : Fin 3 → α)
    (σ : Fin 3 → Fin 3) (hσ : ∀ i, σ i ≠ i ∧ F (anchor g i) (v i) ≤ g (σ i))
    (hmeet : ∀ i j, i ≠ j → ¬ ∃ k, v i ⊓ v j ≤ g k) : ∀ i, palette F g (v i) = {σ i} := by
  have hcyc := three_endpoint_cycle hF g nw' v σ hσ hmeet
  have hfix : ∀ i, σ i ≠ i := fun i => (hσ i).1
  have hlab : ∀ i, σ i ∈ palette F g (v i) := fun i =>
    labels_sub_palette hF g i (v i) (mem_labels.2 (hσ i).2)
  intro i
  refine Finset.eq_singleton_iff_unique_mem.2 ⟨hlab i, fun j hj => ?_⟩
  refine fin3_cycle_pick σ hfix hcyc i j fun k hki => ?_
  by_contra hne
  push_neg at hne
  have hw := hmeet i k (Ne.symm hki)
  have h1 := palette_antitone hF g (inf_le_left : v i ⊓ v k ≤ v i)
  have h2 := palette_antitone hF g (inf_le_right : v i ⊓ v k ≤ v k)
  exact palette_proper g nw' hw (fin3_three_elements _ _ _ _ (h1 hj) (h1 (hlab i)) (h2 (hlab k)) hne.1 hne.2
    (fin3_cycle_injective σ hfix hcyc i k (Ne.symm hki)))

end Mordor.Profile
