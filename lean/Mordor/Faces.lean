import Mordor.Baseline

/-!
# Face-wise provenance (round 26, §34.3z⁹¹)

Response to the brief "face-wise provenance and cycle compression". `wᵢ` the last outside point of the anchor orbit
of `⊤`, `eᵢ = F cᵢ wᵢ ≤ p_{λ i}`; faces `v_S = ⋀_{i∈S} wᵢ`.

* `inf_le_anchor_of_mem`: for a set `J` with two distinct members, `⋀_J p ≤ cᵢ` for each `i ∈ J`.
* `cycle_meet_in_D`: the brief's cycle-meet observation (a column below every `wᵢ` of a label cycle is in `D`) is
  `no_upward_transfer_cycle`; here in face form.
* `face_closure`: at an outside column `y`, if the anchor rows of `S ⊆ J` give labels `λ(S)` and the `J`-meet row has
  labels `K` at `y`, and `λ(S) ∪ K ⊇ J`, then `F (⋀_J p) y ≤ ⋀_J p`: a witness. This is the only closure the face system
  supports at one column.
* `top_entry_face_closure`: the labels `K` can be imported from **any column above `y`**, in particular from `⊤`: if the
  `J`-meet row enters `D` at once (`F (⋀_J p) ⊤ ≤ pₖ`, `k ∈ K`), every face column inherits `K`.
* `length_one_sync`: if every anchor orbit of `J` has length one (`wᵢ = F cᵢ ⊤`), then `F (⋀_J p) ⊤ ≤ v_J`, so a
  dependent `J` (`v_J ∈ D`) makes the `J`-meet row enter at once. With `face_closure` this refutes the Hamiltonian
  3-cycle with length-one orbits (z3: UNSAT); with length-two orbits the same profile is SAT.
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

theorem inf_le_anchor_of_mem {J : Finset ι} (htwo : ∃ a ∈ J, ∃ b ∈ J, a ≠ b) {i : ι} (hi : i ∈ J) :
    J.inf p ≤ anchor p i := by
  obtain ⟨a₀, ha₀, b₀, hb₀, hab⟩ := htwo
  obtain ⟨b, hb, hbi⟩ : ∃ b ∈ J, b ≠ i := by
    by_cases h : i = a₀
    · exact ⟨b₀, hb₀, fun e => hab (h ▸ e.symm ▸ rfl)⟩
    · exact ⟨a₀, ha₀, fun e => h e.symm⟩
  exact (le_inf (Finset.inf_le hi) (Finset.inf_le hb)).trans (meet_le_anchor p hbi)

include hF nw in
/-- **Cycle-meet observation**, face form: no outside column lies below the last points of a label cycle. -/
theorem cycle_meet_in_D {C : Finset ι} (hC : C.Nonempty) (lam : ι → ι) (hlam : ∀ i ∈ C, lam i ∈ C ∧ lam i ≠ i)
    (w : ι → α) (he : ∀ i ∈ C, F (anchor p i) (w i) ≤ p (lam i)) {y : α} (hy : ¬ ∃ k, y ≤ p k)
    (hyw : ∀ i ∈ C, y ≤ w i) : False :=
  no_upward_transfer_cycle hF p nw hy C hC fun a ha =>
    ⟨lam a, (hlam a ha).1, (hlam a ha).2, w a, hyw a ha, he a ha⟩

include hF nw in
/-- **Face closure at one column.** -/
theorem face_closure {J S K : Finset ι} (hSJ : S ⊆ J) (htwo : ∃ a ∈ J, ∃ b ∈ J, a ≠ b) (lam : ι → ι)
    {y : α} (hy : ¬ ∃ k, y ≤ p k) (hface : ∀ i ∈ S, F (anchor p i) y ≤ p (lam i))
    (hK : ∀ k ∈ K, F (J.inf p) y ≤ p k) (hcover : ∀ l ∈ J, l ∈ K ∨ ∃ i ∈ S, lam i = l) : False := by
  obtain ⟨a₀, ha₀, -⟩ := id htwo
  refine (nw _ ⟨a₀, Finset.inf_le ha₀⟩ y hy).1 (Finset.le_inf fun l hl => ?_)
  rcases hcover l hl with hlK | ⟨i, hiS, rfl⟩
  · exact hK l hlK
  · exact (hF _ _ _ _ (inf_le_anchor_of_mem p htwo (hSJ hiS)) le_rfl).trans (hface i hiS)

include hF nw in
/-- **Labels imported from a higher column**, e.g. `⊤`. -/
theorem top_entry_face_closure {J S K : Finset ι} (hSJ : S ⊆ J) (htwo : ∃ a ∈ J, ∃ b ∈ J, a ≠ b)
    (lam : ι → ι) {y u : α} (hy : ¬ ∃ k, y ≤ p k) (hyu : y ≤ u) (hface : ∀ i ∈ S, F (anchor p i) y ≤ p (lam i))
    (hK : ∀ k ∈ K, F (J.inf p) u ≤ p k) (hcover : ∀ l ∈ J, l ∈ K ∨ ∃ i ∈ S, lam i = l) : False :=
  face_closure hF p nw hSJ htwo lam hy hface (fun k hk => (hF _ _ _ _ le_rfl hyu).trans (hK k hk)) hcover

include hF in
/-- **Length-one synchronization through `⊤`.** -/
theorem length_one_sync {J : Finset ι} (htwo : ∃ a ∈ J, ∃ b ∈ J, a ≠ b) :
    F (J.inf p) ⊤ ≤ J.inf (fun i => F (anchor p i) ⊤) :=
  Finset.le_inf fun _ hi => hF _ _ _ _ (inf_le_anchor_of_mem p htwo hi) le_rfl

end Mordor.Profile
