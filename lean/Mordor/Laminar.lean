import Mordor.FGTwo
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic

/-!
# The Cut Lemma for laminar cuts (log §34.3z¹⁷)

`FGTwo.cut_bouquet` handles generators that meet pairwise in one common element. Here the meets may form a hierarchy.

* `transport`: let `D = Q ∪ Q'` with `Q ∩ Q' ⊆ ↓r`, and let `r ≤ r'` both lie in `D`. If the `F r`-orbit of a column `s`
  (with `F r' s ≤ s`) ends in `Q`, so does its `F r'`-orbit. The proof squeezes the `F r`-orbit of `w = F r' s`
  between consecutive terms of the orbit of `s` (as in `FGTwo.sandwich`) and descends along `w < s`.
* `Lam p S`: `S` is a leaf `{i}`, or a union `S₁ ∪ S₂` of laminar sets whose cross meets `pᵢ ⊓ pⱼ` (`i ∈ S₁`,
  `j ∈ S₂`) lie below `⋀_{S₁ ∪ S₂} p`.
* `cut_laminar`: if the whole (finite) index set is laminar, every monotone `F` has a witness for
  `D = ⋃ᵢ ↓pᵢ` with `⊤ ∉ D`, in any bounded lattice with DCC. The orbit end is pushed down the hierarchy by `transport`
  until a leaf, where `FGTwo.sandwich` closes it.

Three generators are laminar iff, after renaming, `p₁ ⊓ p₃ ≤ p₂` and `p₂ ⊓ p₃ ≤ p₁`, i.e. `p₁ ⊓ p₃ = p₂ ⊓ p₃ ≤ p₁ ⊓ p₂`.
-/

namespace Mordor.Laminar
open Mordor.FGTwo

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] [WellFoundedLT α]

/-- The `h`-orbit of `s` stays outside `D` up to some step `n` and then enters `D` at a value in `Q`. -/
def Ends (h : α → α) (InD Q : α → Prop) (s : α) : Prop :=
  ∃ n, (∀ k ≤ n, ¬ InD (h^[k] s)) ∧ Q (h (h^[n] s))

section Transport
variable {F : α → α → α} {InD Q Q' : α → Prop} {r r' : α}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
  (hD : ∀ x, InD x ↔ Q x ∨ Q' x) (hQ : ∀ x y, x ≤ y → Q y → Q x) (hQ' : ∀ x y, x ≤ y → Q' y → Q' x)
  (hrr : r ≤ r') (hrD : InD r) (hr'D : InD r') (hr : ∀ z, Q z → Q' z → z ≤ r)
  (nw : ∀ x, InD x → ∀ y, ¬ InD y → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
include hF hD hQ hQ' hrr hrD hr'D hr nw

theorem transport : ∀ s, ¬ InD s → F r' s ≤ s → Ends (F r) InD Q s → Ends (F r') InD Q s := by
  intro s
  induction s using WellFoundedLT.induction with
  | _ s ih =>
    intro hs hgs ⟨m, hU, hend⟩
    have hmono : Monotone (F r) := fun y y' hy => hF _ _ _ _ le_rfl hy
    have h1 : F r s ≤ F r' s := hF _ _ _ _ hrr le_rfl
    have down : ∀ x y, x ≤ y → InD y → InD x := fun x y hxy hy => by
      rcases (hD y).1 hy with h | h
      · exact (hD x).2 (Or.inl (hQ _ _ hxy h))
      · exact (hD x).2 (Or.inr (hQ' _ _ hxy h))
    have notQ' : ∀ u, ¬ InD u → Q (F r u) → ¬ Q' (F r u) := fun u hu hq hq' =>
      (nw r hrD u hu).1 (hr _ hq hq')
    by_cases hw : InD (F r' s)
    · refine ⟨0, fun k hk => by rw [show k = 0 by omega]; simpa using hs, ?_⟩
      simp only [Function.iterate_zero, id]
      have hhs : InD (F r s) := down _ _ h1 hw
      have hm0 : m = 0 := by
        rcases Nat.eq_zero_or_pos m with h | h
        · exact h
        · exact ((hU 1 h) (by simpa using hhs)).elim
      subst hm0
      simp only [Function.iterate_zero, id] at hend
      rcases (hD _).1 hw with hq | hq'
      · exact hq
      · exact (notQ' s hs hend (hQ' _ _ h1 hq')).elim
    · have hlt : F r' s < s := lt_of_le_of_ne hgs (fun heq => (nw r' hr'D s hs).2 heq.ge)
      have hgw : F r' (F r' s) ≤ F r' s := hF _ _ _ _ le_rfl hgs
      have lo : ∀ k, (F r)^[k + 1] s ≤ (F r)^[k] (F r' s) := fun k => by
        rw [Function.iterate_succ_apply]; exact (hmono.iterate k) h1
      have hi : ∀ k, (F r)^[k] (F r' s) ≤ (F r)^[k] s := fun k => (hmono.iterate k) hgs
      have hUw : ∀ k, k < m → ¬ InD ((F r)^[k] (F r' s)) := fun k hk hin =>
        hU (k + 1) (by omega) (down _ _ (lo k) hin)
      have hEw : Ends (F r) InD Q (F r' s) := by
        by_cases hlast : InD ((F r)^[m] (F r' s))
        · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
            rcases m with _ | m'
            · exact (hw (by simpa using hlast)).elim
            · exact ⟨m', rfl⟩
          refine ⟨m', fun k hk => hUw k (by omega), ?_⟩
          rw [← Function.iterate_succ_apply' (F r) m' (F r' s)]
          have hz : F r ((F r)^[m' + 1] s) ≤ (F r)^[m' + 1] (F r' s) := by
            have := lo (m' + 1); rwa [Function.iterate_succ_apply'] at this
          rcases (hD _).1 hlast with hq | hq'
          · exact hq
          · exact (notQ' _ (hU (m' + 1) le_rfl) hend (hQ' _ _ hz hq')).elim
        · refine ⟨m, fun k hk => ?_, hQ _ _ (hmono (hi m)) hend⟩
          rcases Nat.lt_or_ge k m with hk' | hk'
          · exact hUw k hk'
          · rwa [show k = m by omega]
      obtain ⟨n, hUn, hendn⟩ := ih (F r' s) hlt hw hgw hEw
      refine ⟨n + 1, fun k hk => ?_, by rwa [Function.iterate_succ_apply]⟩
      cases k with
      | zero => simpa using hs
      | succ j => rw [Function.iterate_succ_apply]; exact hUn j (by omega)

end Transport

variable {ι : Type*} [DecidableEq ι]

/-- Laminar index sets: leaves, and unions of laminar sets whose cross meets lie below the meet of the union. -/
inductive Lam (p : ι → α) : Finset ι → Prop
  | single (i : ι) : Lam p {i}
  | split (S₁ S₂ : Finset ι) : Lam p S₁ → Lam p S₂ →
      (∀ i ∈ S₁, ∀ j ∈ S₂, ∀ z, z ≤ p i → z ≤ p j → z ≤ (S₁ ∪ S₂).inf p) → Lam p (S₁ ∪ S₂)

theorem Lam.nonempty {p : ι → α} {S : Finset ι} (h : Lam p S) : S.Nonempty := by
  induction h with
  | single i => exact Finset.singleton_nonempty i
  | split S₁ S₂ _ _ _ ih₁ _ => exact ih₁.mono Finset.subset_union_left

section Main
variable {F : α → α → α} {p : ι → α}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (htop : ¬ ∃ i, ⊤ ≤ p i)
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
include hF htop nw

theorem lam_main {S : Finset ι} (hS : Lam p S) : ∀ r, (∀ i ∈ S, r ≤ p i) →
    (∀ i ∈ S, ∀ j, j ∉ S → ∀ z, z ≤ p i → z ≤ p j → z ≤ r) →
    Ends (F r) (fun x => ∃ i, x ≤ p i) (fun x => ∃ i ∈ S, x ≤ p i) ⊤ → False := by
  induction hS with
  | single i =>
    intro r hrS hcross ⟨n, hU, i', hi', hle⟩
    rw [Finset.mem_singleton] at hi'; subst hi'
    exact sandwich (InD := fun x => ∃ i, x ≤ p i) (InB := fun x => ∃ j, j ≠ i' ∧ x ≤ p j) (a := p i') hF
      (fun x => ⟨fun ⟨i, hi⟩ => (em (i = i')).elim (fun h => Or.inl (h ▸ hi)) (fun h => Or.inr ⟨i, h, hi⟩),
        fun h => h.elim (fun h => ⟨i', h⟩) (fun ⟨j, _, hj⟩ => ⟨j, hj⟩)⟩)
      (fun _ _ hxy ⟨j, hj, hy⟩ => ⟨j, hj, hxy.trans hy⟩) (hrS i' (Finset.mem_singleton_self i'))
      (fun z hza ⟨j, hj, hzj⟩ => hcross i' (Finset.mem_singleton_self i') j (by simpa using hj) z hza hzj)
      nw ⊤ htop le_top n hU hle
  | split S₁ S₂ h₁ h₂ hlam ih₁ ih₂ =>
    intro r hrS hcross hE
    set r' := (S₁ ∪ S₂).inf p with hr'
    obtain ⟨i₀, hi₀⟩ := (Lam.split S₁ S₂ h₁ h₂ hlam).nonempty
    have hrr : r ≤ r' := Finset.le_inf (fun i hi => hrS i hi)
    have hE' := transport (InD := fun x => ∃ i, x ≤ p i) (Q := fun x => ∃ i ∈ S₁ ∪ S₂, x ≤ p i)
      (Q' := fun x => ∃ j, j ∉ S₁ ∪ S₂ ∧ x ≤ p j) hF
      (fun x => ⟨fun ⟨i, hi⟩ => (em (i ∈ S₁ ∪ S₂)).elim (fun h => Or.inl ⟨i, h, hi⟩) (fun h => Or.inr ⟨i, h, hi⟩),
        fun h => h.elim (fun ⟨i, _, hi⟩ => ⟨i, hi⟩) (fun ⟨j, _, hj⟩ => ⟨j, hj⟩)⟩)
      (fun _ _ hxy ⟨i, hi, hy⟩ => ⟨i, hi, hxy.trans hy⟩) (fun _ _ hxy ⟨j, hj, hy⟩ => ⟨j, hj, hxy.trans hy⟩)
      hrr ⟨i₀, hrS i₀ hi₀⟩ ⟨i₀, Finset.inf_le hi₀⟩ (fun z ⟨i, hi, hzi⟩ ⟨j, hj, hzj⟩ => hcross i hi j hj z hzi hzj)
      nw ⊤ htop le_top hE
    obtain ⟨n, hU, i, hi, hle⟩ := hE'
    rcases Finset.mem_union.1 hi with hi1 | hi2
    · refine ih₁ r' (fun i hi => Finset.inf_le (Finset.mem_union_left _ hi)) ?_ ⟨n, hU, i, hi1, hle⟩
      intro i hi j hj z hzi hzj
      by_cases hj2 : j ∈ S₂
      · exact hlam i hi j hj2 z hzi hzj
      · exact (hcross i (Finset.mem_union_left _ hi) j (by simp [hj, hj2]) z hzi hzj).trans hrr
    · refine ih₂ r' (fun i hi => Finset.inf_le (Finset.mem_union_right _ hi)) ?_ ⟨n, hU, i, hi2, hle⟩
      intro i hi j hj z hzi hzj
      by_cases hj1 : j ∈ S₁
      · exact hlam j hj1 i hi z hzj hzi
      · exact (hcross i (Finset.mem_union_right _ hi) j (by simp [hj, hj1]) z hzi hzj).trans hrr

end Main

/-- **The Cut Lemma for laminar cuts.** In a bounded lattice with DCC, let `D = ⋃ᵢ ↓pᵢ` over a finite index set that is
laminar (`Lam p univ`), with `⊤ ∉ D`. Every monotone `F` has a witness. -/
theorem cut_laminar [Fintype ι] [Nonempty ι] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α) (hlam : Lam p Finset.univ)
    (htop : ¬ ∃ i, ⊤ ≤ p i) :
    ∃ x, (∃ i, x ≤ p i) ∧ ∃ y, ¬ (∃ i, y ≤ p i) ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  have nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y :=
    fun x hx y hy => ⟨fun h => hno ⟨x, hx, y, hy, Or.inl h⟩, fun h => hno ⟨x, hx, y, hy, Or.inr h⟩⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  set r := Finset.univ.inf p
  obtain ⟨n, hU, i, hi⟩ := orbit_end (InD := fun x => ∃ i, x ≤ p i) hF ⟨i₀, Finset.inf_le (Finset.mem_univ i₀)⟩
    nw ⊤ htop le_top
  exact lam_main hF htop nw hlam r (fun i _ => Finset.inf_le (Finset.mem_univ i))
    (fun i _ j hj => absurd (Finset.mem_univ j) hj) ⟨n, hU, i, Finset.mem_univ i, hi⟩

end Mordor.Laminar

namespace Mordor.Laminar

variable {α : Type*} [Lattice α] [BoundedOrder α] [WellFoundedLT α]

/-- **Three laminar generators.** If `p₁ ⊓ p₃ ≤ p₂` and `p₂ ⊓ p₃ ≤ p₁` (so `p₁ ⊓ p₃ = p₂ ⊓ p₃ ≤ p₁ ⊓ p₂`), the cut
`↓p₁ ∪ ↓p₂ ∪ ↓p₃` (`⊤` outside) has a witness for every monotone `F`, in any bounded lattice with DCC. -/
theorem cut_three_laminar {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {p₁ p₂ p₃ : α} (h13 : p₁ ⊓ p₃ ≤ p₂) (h23 : p₂ ⊓ p₃ ≤ p₁) (htop : ¬ (⊤ ≤ p₁ ∨ ⊤ ≤ p₂ ∨ ⊤ ≤ p₃)) :
    ∃ x, (x ≤ p₁ ∨ x ≤ p₂ ∨ x ≤ p₃) ∧ ∃ y, ¬ (y ≤ p₁ ∨ y ≤ p₂ ∨ y ≤ p₃) ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  let p : Fin 3 → α := ![p₁, p₂, p₃]
  have hex : ∀ x, (∃ i, x ≤ p i) ↔ (x ≤ p₁ ∨ x ≤ p₂ ∨ x ≤ p₃) := fun x => by
    simp [p, Fin.exists_fin_succ]
  have hlam : Lam p Finset.univ := by
    have hu : (Finset.univ : Finset (Fin 3)) = ({0} ∪ {1}) ∪ {2} := by decide
    rw [hu]
    refine Lam.split _ _ (Lam.split _ _ (Lam.single 0) (Lam.single 1) ?_) (Lam.single 2) ?_
    · intro i hi j hj z hzi hzj
      simp only [Finset.mem_singleton] at hi hj; subst hi; subst hj
      simpa [p] using le_inf hzi hzj
    · intro i hi j hj z hzi hzj
      simp only [Finset.mem_singleton] at hj; subst hj
      have hz3 : z ≤ p₃ := by simpa [p] using hzj
      simp only [Finset.mem_union, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl
      · have hz1 : z ≤ p₁ := by simpa [p] using hzi
        have hz2 : z ≤ p₂ := (le_inf hz1 hz3).trans h13
        simp [p, Finset.inf_insert, hz1, hz2, hz3]
      · have hz2 : z ≤ p₂ := by simpa [p] using hzi
        have hz1 : z ≤ p₁ := (le_inf hz2 hz3).trans h23
        simp [p, Finset.inf_insert, hz1, hz2, hz3]
  obtain ⟨x, hx, y, hy, hw⟩ := cut_laminar hF p hlam (fun ⟨i, hi⟩ => htop ((hex ⊤).1 ⟨i, hi⟩))
  exact ⟨x, (hex x).1 hx, y, fun h => hy ((hex y).2 h), hw⟩

end Mordor.Laminar
