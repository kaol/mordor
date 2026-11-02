import Mordor.Faces
import Mathlib.Data.Fintype.Powerset

/-!
# Set-valued face labels, boundary labels, hybrid and dual faces (round 26, §34.3z⁹²)

Response to the brief "set-valued provenance and dual-face lifting". `wᵢ` anchor last points, `eᵢ = F cᵢ wᵢ`,
`v_S = ⋀_{i∈S} wᵢ`; `J` *minimally dependent*: `v_J ∈ D`, `v_S ∉ D` for nonempty proper `S ⊂ J`.

* `label_closed_eq`: every nonempty `S ⊆ J` that is *label-closed* (each `eₐ`, `a ∈ S`, below some `pₖ`, `k ∈ S`)
  is `J` (`no_upward_transfer_cycle` at `v_S`). This is the whole content of the brief's Target A.
* `labels_core`, `hamiltonian_full_triple`: for three generators and `J = univ` the escape branch is empty (each
  `eᵢ ∈ D`), and the labels are **exactly** a cyclic permutation: `eᵢ ≤ pⱼ ↔ j = σ i` with `σ` one of the two
  3-cycles. (`decide` over all label assignments.)
* `boundary_labels`: for `J` with an exact cyclic labelling `σ`, the codimension-one face `yᵢ` has
  `F m_J yᵢ ≤ pⱼ` for every `j = σ t`, `t ≠ i`, and not all of `J` (no witness).
* `hybrid_entry`: if `F m_J q ≤ pₖ` at an outside column `q`, then `q ⊓ v_{J \ {σ⁻¹ k}} ∈ D`. This is `face_closure`
  with `K = {k}`.
* `dual_face_bounds`: for `u = yᵢ ⊔ yⱼ`, `F m_J u ≥ F m_J yᵢ ⊔ F m_J yⱼ`, so it is below neither `p_{σ i}` nor
  `p_{σ j}`.
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF nw in
/-- **Label-closed subsets of a minimally dependent set are the whole set.** -/
theorem label_closed_eq {J : Finset ι} (w : ι → α)
    (hmin : ∀ S ⊆ J, S.Nonempty → S ≠ J → ¬ ∃ k, S.inf w ≤ p k)
    (hsand : ∀ i ∈ J, ¬ F (anchor p i) (w i) ≤ p i) {S : Finset ι} (hSJ : S ⊆ J) (hne : S.Nonempty)
    (hcl : ∀ a ∈ S, ∃ k ∈ S, F (anchor p a) (w a) ≤ p k) : S = J := by
  by_contra hSne
  refine no_upward_transfer_cycle hF p nw (hmin S hSJ hne hSne) S hne fun a ha => ?_
  obtain ⟨k, hk, hle⟩ := hcl a ha
  exact ⟨k, hk, fun e => hsand a (hSJ ha) (e ▸ hle), w a, Finset.inf_le ha, hle⟩

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- The combinatorial core for three generators. -/
theorem labels_core (K0 K1 K2 : Finset (Fin 3)) (h0 : 0 ∉ K0) (h1 : 1 ∉ K1) (h2 : 2 ∉ K2)
    (n0 : K0.Nonempty) (n1 : K1.Nonempty) (n2 : K2.Nonempty)
    (hcl : ∀ S : Finset (Fin 3), S.Nonempty → (0 ∈ S → (K0 ∩ S).Nonempty) → (1 ∈ S → (K1 ∩ S).Nonempty) →
      (2 ∈ S → (K2 ∩ S).Nonempty) → S = Finset.univ) :
    (K0 = {1} ∧ K1 = {2} ∧ K2 = {0}) ∨ (K0 = {2} ∧ K1 = {0} ∧ K2 = {1}) := by
  revert K0 K1 K2
  set_option maxRecDepth 20000 in decide

set_option maxHeartbeats 1000000 in
include hF in
/-- **Three generators, `J = univ`: the labels are exactly a 3-cycle.** -/
theorem hamiltonian_full_triple (p : Fin 3 → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (w : Fin 3 → α)
    (hmin : ∀ S : Finset (Fin 3), S.Nonempty → S ≠ Finset.univ → ¬ ∃ k, S.inf w ≤ p k)
    (hsand : ∀ i, ¬ F (anchor p i) (w i) ≤ p i) (hin : ∀ i, ∃ k, F (anchor p i) (w i) ≤ p k) :
    (∀ i j, F (anchor p i) (w i) ≤ p j ↔ j = i + 1) ∨ (∀ i j, F (anchor p i) (w i) ≤ p j ↔ j = i + 2) := by
  classical
  let K : Fin 3 → Finset (Fin 3) := fun i => Finset.univ.filter (fun j => F (anchor p i) (w i) ≤ p j)
  have hK : ∀ i j, j ∈ K i ↔ F (anchor p i) (w i) ≤ p j := fun i j => by simp [K]
  have hcl : ∀ S : Finset (Fin 3), S.Nonempty → (∀ a ∈ S, (K a ∩ S).Nonempty) → S = Finset.univ :=
    fun S hS hc => label_closed_eq hF p nw (J := Finset.univ) w
      (fun S _ hne hne' => hmin S hne hne') (fun i _ => hsand i) (Finset.subset_univ S) hS
      (fun a ha => by
        obtain ⟨k, hk⟩ := hc a ha
        exact ⟨k, (Finset.mem_inter.1 hk).2, (hK a k).1 (Finset.mem_inter.1 hk).1⟩)
  have hne : ∀ i, (K i).Nonempty := fun i => by obtain ⟨k, hk⟩ := hin i; exact ⟨k, (hK i k).2 hk⟩
  have hnot : ∀ i, i ∉ K i := fun i h => hsand i ((hK i i).1 h)
  rcases labels_core (K 0) (K 1) (K 2) (hnot 0) (hnot 1) (hnot 2) (hne 0) (hne 1) (hne 2)
      (fun S hS c0 c1 c2 => hcl S hS fun a ha => by fin_cases a <;> simp_all) with ⟨e0, e1, e2⟩ | ⟨e0, e1, e2⟩
  · left; intro i j; rw [← hK]; fin_cases i <;> fin_cases j <;> simp [e0, e1, e2]
  · right; intro i j; rw [← hK]; fin_cases i <;> fin_cases j <;> simp [e0, e1, e2]

include hF in
/-- **Codimension-one boundary labels.** -/
theorem boundary_labels {J : Finset ι} (htwo : ∃ a ∈ J, ∃ b ∈ J, a ≠ b) (w : ι → α) (σ : ι → ι)
    (he : ∀ t ∈ J, F (anchor p t) (w t) ≤ p (σ t)) {i : ι} {y : α} (hy : ∀ t ∈ J, t ≠ i → y ≤ w t)
    {t : ι} (ht : t ∈ J) (hti : t ≠ i) : F (J.inf p) y ≤ p (σ t) :=
  (hF _ _ _ _ (inf_le_anchor_of_mem p htwo ht) (hy t ht hti)).trans (he t ht)

include hF nw in
/-- **Hybrid-face entry** (`face_closure` with a single imported label). -/
theorem hybrid_entry {J : Finset ι} (htwo : ∃ a ∈ J, ∃ b ∈ J, a ≠ b) (w : ι → α) (σ : ι → ι)
    (he : ∀ t ∈ J, F (anchor p t) (w t) ≤ p (σ t)) {i k : ι}
    (hcover : ∀ l ∈ J, l = k ∨ ∃ t ∈ J.erase i, σ t = l) {q : α} (hq : F (J.inf p) q ≤ p k) :
    ∃ l, q ⊓ (J.erase i).inf w ≤ p l := by
  by_contra hout
  refine face_closure hF p nw (Finset.erase_subset i J) htwo σ hout (K := {k}) (fun t ht => ?_)
    (fun k' hk' => by rw [Finset.mem_singleton.1 hk']; exact (hF _ _ _ _ le_rfl inf_le_left).trans hq)
    (fun l hl => (hcover l hl).elim (fun h => Or.inl (Finset.mem_singleton.2 h)) Or.inr)
  exact (hF _ _ _ _ le_rfl (inf_le_right.trans (Finset.inf_le ht))).trans (he t (Finset.mem_of_mem_erase ht))

include hF nw in
/-- **Dual-face bounds.** -/
theorem dual_face_bounds {J : Finset ι} {yi yj : α} {a b : ι} (hyi : ¬ ∃ k, yi ≤ p k) (hyj : ¬ ∃ k, yj ≤ p k)
    (hJa : a ∈ J) (hai : ∀ l ∈ J, l ≠ a → F (J.inf p) yi ≤ p l)
    (hbj : ∀ l ∈ J, l ≠ b → F (J.inf p) yj ≤ p l) :
    F (J.inf p) yi ⊔ F (J.inf p) yj ≤ F (J.inf p) (yi ⊔ yj) ∧ ¬ F (J.inf p) (yi ⊔ yj) ≤ p a ∧
      ¬ F (J.inf p) (yi ⊔ yj) ≤ p b := by
  have hle : F (J.inf p) yi ⊔ F (J.inf p) yj ≤ F (J.inf p) (yi ⊔ yj) :=
    sup_le (hF _ _ _ _ le_rfl le_sup_left) (hF _ _ _ _ le_rfl le_sup_right)
  have hJD : ∃ k, J.inf p ≤ p k := ⟨a, Finset.inf_le hJa⟩
  refine ⟨hle, fun h => (nw _ hJD yi hyi).1 (Finset.le_inf fun l hl => ?_),
    fun h => (nw _ hJD yj hyj).1 (Finset.le_inf fun l hl => ?_)⟩
  · by_cases hla : l = a
    · exact hla ▸ (le_sup_left.trans hle).trans h
    · exact hai l hl hla
  · by_cases hlb : l = b
    · exact hlb ▸ (le_sup_right.trans hle).trans h
    · exact hbj l hl hlb

end Mordor.Profile
