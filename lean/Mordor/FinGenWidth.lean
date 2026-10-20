import Mordor.FinGen11
import Mordor.FinGen12
import Mordor.FinGen13
import Mordor.FinGen21
import Mordor.FinGen22
import Mordor.FinGen23
import Mordor.FinGen31
import Mordor.FinGen32
import Mordor.FinGen33
import Mordor.Cut
import Mathlib.Order.Antichain
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Card

/-!
# The Cut Lemma on lattices of width ≤ 3 (log §34.3m)

In a finite poset of width ≤ w every nonempty set is generated, from above, by its ≤ w maximal elements. A cut
`D` of a finite lattice of width ≤ 3 is therefore k × l-generated with k, l ≤ 3 (by the maximal elements of `D`
and the minimal elements of its complement), and `lab_kl` applies. A chain-finite poset of finite width is finite
(Dilworth), so `Finite` costs nothing against "chain-finite"; the generated lemmas `labkl` themselves need no
chain condition at all.
-/

namespace Mordor.FinGen
open Classical

theorem gens {β : Type*} [PartialOrder β] [Finite β] {w : ℕ}
    (hw : ∀ s : Finset β, IsAntichain (· ≤ ·) (s : Set β) → s.card ≤ w) (S : Set β) (hS : S.Nonempty) :
    ∃ k, 0 < k ∧ k ≤ w ∧ ∃ p : Fin k → β, (∀ i, p i ∈ S) ∧ ∀ x ∈ S, ∃ i, x ≤ p i := by
  haveI := Fintype.ofFinite β
  set M := Finset.univ.filter (fun m => m ∈ S ∧ ∀ y ∈ S, m ≤ y → y = m)
  have hM : ∀ x ∈ S, ∃ m ∈ M, x ≤ m := by
    intro x hx
    obtain ⟨m, ⟨hmS, hxm⟩, hmin⟩ := (wellFounded_gt (α := β)).has_min {y | y ∈ S ∧ x ≤ y} ⟨x, hx, le_rfl⟩
    refine ⟨m, Finset.mem_filter.2 ⟨Finset.mem_univ _, hmS, fun y hy hmy => ?_⟩, hxm⟩
    by_contra hne
    exact hmin y ⟨hy, hxm.trans hmy⟩ (lt_of_le_of_ne hmy (Ne.symm hne))
  have hMS : ∀ m ∈ M, m ∈ S := fun m hm => (Finset.mem_filter.1 hm).2.1
  have hA : IsAntichain (· ≤ ·) (M : Set β) := by
    intro a ha b hb hab hle
    exact hab ((Finset.mem_filter.1 ha).2.2 b (hMS b hb) hle).symm
  obtain ⟨x0, hx0⟩ := hS
  obtain ⟨m0, hm0, -⟩ := hM x0 hx0
  refine ⟨M.card, Finset.card_pos.2 ⟨m0, hm0⟩, hw M hA, fun i => (M.equivFin.symm i : β),
    fun i => hMS _ (M.equivFin.symm i).2, fun x hx => ?_⟩
  obtain ⟨m, hm, hxm⟩ := hM x hx
  exact ⟨M.equivFin ⟨m, hm⟩, by simpa using hxm⟩

/-- **The Cut Lemma on finite lattices of width ≤ 3** (no height bound). -/
theorem cut_width3 {α : Type*} [Lattice α] [BoundedOrder α] [Finite α]
    (hw : ∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ 3)
    (F : α → α → α) (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (D : Set α) (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  obtain ⟨k, hk0, hk3, p, hpD, hgD⟩ := gens hw D ⟨⊥, hbot⟩
  obtain ⟨l, hl0, hl3, u, huU, hgU⟩ :=
    gens (β := αᵒᵈ) (fun s hs => hw s hs.swap) (Dᶜ : Set α) ⟨OrderDual.toDual (⊤ : α), htop⟩
  have H : Cx F D p u := ⟨hF, hD, hpD, huU, hgD, hgU, fun x hx y hy => ⟨fun h => (hno x hx y hy).1 h,
    fun h => (hno x hx y hy).2 h⟩⟩
  obtain rfl | rfl | rfl : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  all_goals obtain rfl | rfl | rfl : l = 1 ∨ l = 2 ∨ l = 3 := by omega
  exacts [lab11 H, lab12 H, lab13 H, lab21 H, lab22 H, lab23 H, lab31 H, lab32 H, lab33 H]

end Mordor.FinGen

namespace Mordor
open FinGen

variable {α : Type*} [CompleteLattice α] [Finite α]

/-- The Cut Lemma in the form of `Cut.lean`, on finite lattices of width ≤ 3. -/
theorem cutCells_width3 (hw : ∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ 3)
    (F : α →o α →o α) : CutCells F := by
  intro D hD ⟨d, hd⟩ ⟨u, hu⟩
  exact cut_width3 hw (fun x y => F x y) (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) D
    (fun x y h hy => hD h hy) (hD bot_le hd) (fun ht => hu (hD le_top ht))

/-- **Semi-CL, hence CL, on finite lattices of width ≤ 3.** -/
theorem semi_width3 (hw : ∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ 3)
    (F : α →o α →o α) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F :=
  semi_of_cut (cutMaps_of_cells (cutCells_width3 hw F)) hsemi

theorem cl_width3 (hw : ∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ 3)
    (F : α →o α →o α) (hcomm : ∀ x, b F (a F x) = a F (b F x)) : m F = n F :=
  semi_width3 hw F fun x => (hcomm x).le

end Mordor
