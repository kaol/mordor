import Mordor.FGTwo
import Mordor.Laminar
import Mathlib.Order.Iterate
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic

/-!
# Finitely generated cuts: orbit entry times, the column lemma, join anchors (log §34.3z¹⁸)

`D = ⋃ᵢ ↓pᵢ` over a finite index set, `⊤ ∉ D`, `F` monotone, and no witness. These are the facts available at a single
column or along a single orbit, for every finite family and in particular for the open crossing case of three
generators.

* `endpoint_not_le` (Lemma A), `entry_mono` (Lemma B), `entry_eq_le` (Lemma C): for anchors `a ≤ a'` in `D`, the orbit of
  `F a` enters `D` no later than that of `F a'`, at equal times below it, and never at a value below its own anchor.
* `no_closed_rows`, `column_lemma`: at a column `y ∉ D` no nonempty set of generator rows has all its values below
  generators of the same set; in particular some generator row `F (pᵢ) y` lies outside `D`.
* `escape_below`: escapes along rows that contract at `y` stay strictly below `y` (the composition law of escapes).
* `meetRow`, `rows_to_meets`: compressing every row to the meet of the generators above it preserves monotonicity and
  witness-freeness, so the meet-row reduction loses nothing about rows (log §34.3z¹⁹).
* `anchor_sandwich`: with the join anchor `cᵢ = ⨆_{j ≠ i} pᵢ ⊓ pⱼ ≤ pᵢ`, the `F cᵢ`-orbit of a column `s` with
  `F pᵢ s ≤ s` (e.g. `⊤`) never enters `D` below `pᵢ`. This is `FGTwo.sandwich` with `InB = ⋃_{j ≠ i} ↓pⱼ`.
-/

namespace Mordor.Crossing
open Mordor.FGTwo

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α]

/-- The `h`-orbit of `s` is outside `D` for steps `0, …, n` and inside at step `n + 1`. -/
def EntersAt (h : α → α) (InD : α → Prop) (s : α) (n : ℕ) : Prop :=
  (∀ k ≤ n, ¬ InD (h^[k] s)) ∧ InD (h^[n + 1] s)

section Entry
variable {F : α → α → α} {InD : α → Prop}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hdown : ∀ x y, x ≤ y → InD y → InD x)
  (nw : ∀ x, InD x → ∀ y, ¬ InD y → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include nw in
/-- **Lemma A.** The value at which the `F a`-orbit enters `D` is not below the anchor `a`. -/
theorem endpoint_not_le {a s : α} {n : ℕ} (ha : InD a) (hE : EntersAt (F a) InD s n) : ¬ (F a)^[n + 1] s ≤ a := by
  rw [Function.iterate_succ_apply']; exact (nw a ha _ (hE.1 n le_rfl)).1

include hF in
theorem iterate_le {a a' : α} (haa : a ≤ a') (s : α) (k : ℕ) : (F a)^[k] s ≤ (F a')^[k] s :=
  Monotone.iterate_le_of_le (fun _ _ hy => hF _ _ _ _ le_rfl hy) (fun _ => hF _ _ _ _ haa le_rfl) k s

include hF hdown in
/-- **Lemma B.** A lower anchor enters `D` no later. -/
theorem entry_mono {a a' s : α} {n n' : ℕ} (haa : a ≤ a') (hE : EntersAt (F a) InD s n)
    (hE' : EntersAt (F a') InD s n') : n ≤ n' := by
  by_contra h
  exact hE.1 (n' + 1) (by omega) (hdown _ _ (iterate_le hF haa s (n' + 1)) hE'.2)

include hF in
/-- **Lemma C.** At equal entry times the lower anchor enters below, so its endpoint carries every label of the other. -/
theorem entry_eq_le {a a' s : α} {n : ℕ} (haa : a ≤ a') : (F a)^[n + 1] s ≤ (F a')^[n + 1] s :=
  iterate_le hF haa s (n + 1)

end Entry

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Closed row sets are impossible.** At a column `y ∉ D`, no nonempty set `S` of generator rows has every value
`F (pᵢ) y` (`i ∈ S`) below some `pⱼ` with `j ∈ S`. The targets of `S` form a smaller such set unless they are all of
`S`, and then `F (⋀_S p) y ≤ ⋀_S p` (W1 at row `⋀_S p`). -/
theorem no_closed_rows {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α) {y : α}
    (hy : ¬ ∃ i, y ≤ p i)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) :
    ∀ S : Finset ι, S.Nonempty → ¬ ∀ i ∈ S, ∃ j ∈ S, F (p i) y ≤ p j := by
  classical
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hne hS
    set S' := S.filter (fun j => ∃ i ∈ S, F (p i) y ≤ p j) with hS'
    have hsub : S' ⊆ S := Finset.filter_subset _ _
    by_cases heq : S' = S
    · obtain ⟨i₀, hi₀⟩ := hne
      have hle : F (S.inf p) y ≤ S.inf p := Finset.le_inf fun j hj => by
        have hj' : j ∈ S' := heq ▸ hj
        obtain ⟨i, hi, hij⟩ := (Finset.mem_filter.1 hj').2
        exact (hF _ _ _ _ (Finset.inf_le hi) le_rfl).trans hij
      exact (nw _ ⟨i₀, Finset.inf_le hi₀⟩ y hy).1 hle
    · have hlt : S' ⊂ S := Finset.ssubset_iff_subset_ne.2 ⟨hsub, heq⟩
      obtain ⟨i₀, hi₀⟩ := hne
      obtain ⟨j₀, hj₀, h₀⟩ := hS i₀ hi₀
      refine ih S' hlt ⟨j₀, Finset.mem_filter.2 ⟨hj₀, i₀, hi₀, h₀⟩⟩ fun i hi => ?_
      obtain ⟨j, hj, hij⟩ := hS i (hsub hi)
      exact ⟨j, Finset.mem_filter.2 ⟨hj, i, hsub hi, hij⟩, hij⟩

/-- **Column lemma.** At every column outside `D = ⋃ᵢ ↓pᵢ`, some generator row takes a value outside `D`. -/
theorem column_lemma [Nonempty ι] {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : ι → α) {y : α} (hy : ¬ ∃ i, y ≤ p i)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) :
    ∃ i, ¬ ∃ j, F (p i) y ≤ p j := by
  by_contra hall
  push_neg at hall
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact no_closed_rows hF p hy nw Finset.univ ⟨i₀, Finset.mem_univ _⟩ fun i _ => by
    obtain ⟨j, hj⟩ := hall i; exact ⟨j, Finset.mem_univ _, hj⟩

/-- **Escapes stay below a contracting column.** If row `pᵢ` contracts at `y` (`F (pᵢ) y ≤ y`), then for every column
`x ≤ y` outside `D`, `F (pᵢ) x < y`. By induction, an escape path from `y` that uses only rows contracting at `y` stays
strictly below `y`. This is all that monotonicity gives for compositions of escapes: once a path uses a row that does
not contract at its starting column, no comparison survives. -/
theorem escape_below {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {i : ι} {x y : α} (hyi : F (p i) y ≤ y) (hxy : x ≤ y) (hx : ¬ ∃ j, x ≤ p j) : F (p i) x < y := by
  refine lt_of_le_of_ne ((hF _ _ _ _ le_rfl hxy).trans hyi) fun heq => ?_
  exact (nw (p i) ⟨i, le_rfl⟩ x hx).2 (heq ▸ hxy)

/-- Meet of the generators above `x`: the row a witness-free `F` may be compressed to (`rows_to_meets`). -/
noncomputable def meetRow (p : ι → α) (x : α) : α :=
  Finset.univ.inf fun i => @ite _ (x ≤ p i) (Classical.propDecidable _) (p i) ⊤

theorem le_meetRow (p : ι → α) (x : α) : x ≤ meetRow p x :=
  Finset.le_inf fun i _ => by
    by_cases h : x ≤ p i
    · rw [if_pos h]; exact h
    · rw [if_neg h]; exact le_top

theorem meetRow_le {p : ι → α} {x : α} {i : ι} (hi : x ≤ p i) : meetRow p x ≤ p i :=
  (Finset.inf_le (f := fun i => @ite _ (x ≤ p i) (Classical.propDecidable _) (p i) ⊤) (Finset.mem_univ i)).trans
    (by rw [if_pos hi])

theorem meetRow_mono (p : ι → α) : Monotone (meetRow p) := fun x x' h =>
  Finset.inf_mono_fun fun i _ => by
    by_cases h' : x' ≤ p i
    · rw [if_pos h', if_pos (h.trans h')]
    · rw [if_neg h']; exact le_top

/-- **Row compression is lossless for finitely generated cuts.** `F'(x, y) = F (⋀{pᵢ : x ≤ pᵢ}) y` is monotone and
witness-free whenever `F` is, with no chain condition. So a counterexample may be assumed to read only the meet rows
`⋀_S p`; the reduced meet-row theory forgets nothing about rows, only the lattice structure among columns. -/
theorem rows_to_meets {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) :
    (∀ x x' y y', x ≤ x' → y ≤ y' → F (meetRow p x) y ≤ F (meetRow p x') y') ∧
    ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F (meetRow p x) y ≤ x ∧ ¬ y ≤ F (meetRow p x) y := by
  refine ⟨fun x x' y y' hx hy => hF _ _ _ _ (meetRow_mono p hx) hy, fun x ⟨i, hi⟩ y hy => ?_⟩
  obtain ⟨h1, h2⟩ := nw (meetRow p x) ⟨i, meetRow_le hi⟩ y hy
  exact ⟨fun h => h1 (h.trans (le_meetRow p x)), h2⟩

/-- The join anchor of `i`: `cᵢ = ⨆_{j ≠ i} pᵢ ⊓ pⱼ`. -/
def anchor (p : ι → α) (i : ι) : α := (Finset.univ.erase i).sup (fun j => p i ⊓ p j)

theorem anchor_le (p : ι → α) (i : ι) : anchor p i ≤ p i :=
  Finset.sup_le fun _ _ => inf_le_left

/-- **Join-anchor sandwich.** Let `s ∉ D` with `F (pᵢ) s ≤ s` (e.g. `s = ⊤`). The `F cᵢ`-orbit of `s` never enters `D`
at a value below `pᵢ`. -/
theorem anchor_sandwich [WellFoundedLT α] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α) (i : ι)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {s : α} (hs : ¬ ∃ j, s ≤ p j) (hgs : F (p i) s ≤ s) (n : ℕ)
    (hU : ∀ k ≤ n, ¬ ∃ j, (F (anchor p i))^[k] s ≤ p j) : ¬ F (anchor p i) ((F (anchor p i))^[n] s) ≤ p i :=
  fun hend => sandwich (InD := fun x => ∃ j, x ≤ p j) (InB := fun x => ∃ j, j ≠ i ∧ x ≤ p j) (a := p i) hF
    (fun _ => ⟨fun ⟨j, hj⟩ => (em (j = i)).elim (fun h => Or.inl (h ▸ hj)) (fun h => Or.inr ⟨j, h, hj⟩),
      fun h => h.elim (fun h => ⟨i, h⟩) (fun ⟨j, _, hj⟩ => ⟨j, hj⟩)⟩)
    (fun _ _ hxy ⟨j, hj, hy⟩ => ⟨j, hj, hxy.trans hy⟩) (anchor_le p i)
    (fun _ hzi ⟨j, hj, hzj⟩ => (le_inf hzi hzj).trans
      (Finset.le_sup (f := fun j => p i ⊓ p j) (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)))
    nw s hs hgs n hU hend

end Mordor.Crossing

namespace Mordor.Crossing
open Mordor.Laminar Mordor.FGTwo

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] [WellFoundedLT α] {ι : Type*} [DecidableEq ι]

/-- A bag `S` *closes* (for `F` and the cut `⋃ᵢ ↓pᵢ`) if, for every anchor `r` below its generators whose cross meets
with the outside lie below `r`, the `F r`-orbit of `⊤` does not enter `D` inside `⋃_{i∈S} ↓pᵢ`. -/
def Closes (F : α → α → α) (p : ι → α) (S : Finset ι) : Prop :=
  ∀ r, (∀ i ∈ S, r ≤ p i) → (∀ i ∈ S, ∀ j, j ∉ S → ∀ z, z ≤ p i → z ≤ p j → z ≤ r) →
    ¬ Ends (F r) (fun x => ∃ i, x ≤ p i) (fun x => ∃ i ∈ S, x ≤ p i) ⊤

/-- Separator trees: bags at the leaves, and unions whose cross meets lie below the meet of the union. -/
inductive Tree (p : ι → α) (Bag : Finset ι → Prop) : Finset ι → Prop
  | leaf (S : Finset ι) : Bag S → S.Nonempty → Tree p Bag S
  | split (S₁ S₂ : Finset ι) : Tree p Bag S₁ → Tree p Bag S₂ →
      (∀ i ∈ S₁, ∀ j ∈ S₂, ∀ z, z ≤ p i → z ≤ p j → z ≤ (S₁ ∪ S₂).inf p) → Tree p Bag (S₁ ∪ S₂)

theorem Tree.nonempty {p : ι → α} {Bag} {S : Finset ι} (h : Tree p Bag S) : S.Nonempty := by
  induction h with
  | leaf S _ hne => exact hne
  | split S₁ S₂ _ _ _ ih₁ _ => exact ih₁.mono Finset.subset_union_left

/-- **Composition along a separator tree.** If every bag closes, every node of the tree closes: `Laminar.transport`
carries the orbit end from the anchor of a node to the meet of its union, and from there into one child. -/
theorem tree_closes {F : α → α → α} {p : ι → α} {Bag : Finset ι → Prop}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (htop : ¬ ∃ i, ⊤ ≤ p i)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (hbag : ∀ S, Bag S → Closes F p S) {S : Finset ι} (hS : Tree p Bag S) : Closes F p S := by
  induction hS with
  | leaf S hb _ => exact hbag S hb
  | split S₁ S₂ h₁ h₂ hlam ih₁ ih₂ =>
    intro r hrS hcross hE
    set r' := (S₁ ∪ S₂).inf p
    obtain ⟨i₀, hi₀⟩ := (Tree.split S₁ S₂ h₁ h₂ hlam).nonempty
    have hrr : r ≤ r' := Finset.le_inf (fun i hi => hrS i hi)
    obtain ⟨n, hU, i, hi, hle⟩ := transport (InD := fun x => ∃ i, x ≤ p i)
      (Q := fun x => ∃ i ∈ S₁ ∪ S₂, x ≤ p i) (Q' := fun x => ∃ j, j ∉ S₁ ∪ S₂ ∧ x ≤ p j) hF
      (fun x => ⟨fun ⟨i, hi⟩ => (em (i ∈ S₁ ∪ S₂)).elim (fun h => Or.inl ⟨i, h, hi⟩) (fun h => Or.inr ⟨i, h, hi⟩),
        fun h => h.elim (fun ⟨i, _, hi⟩ => ⟨i, hi⟩) (fun ⟨j, _, hj⟩ => ⟨j, hj⟩)⟩)
      (fun _ _ hxy ⟨i, hi, hy⟩ => ⟨i, hi, hxy.trans hy⟩) (fun _ _ hxy ⟨j, hj, hy⟩ => ⟨j, hj, hxy.trans hy⟩)
      hrr ⟨i₀, hrS i₀ hi₀⟩ ⟨i₀, Finset.inf_le hi₀⟩ (fun z ⟨i, hi, hzi⟩ ⟨j, hj, hzj⟩ => hcross i hi j hj z hzi hzj)
      nw ⊤ htop le_top hE
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

/-- Singletons close (`FGTwo.sandwich`), so laminar families are the trees with singleton bags. -/
theorem singleton_closes {F : α → α → α} {p : ι → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (htop : ¬ ∃ i, ⊤ ≤ p i)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (i : ι) :
    Closes F p {i} := by
  intro r hrS hcross ⟨n, hU, i', hi', hle⟩
  rw [Finset.mem_singleton] at hi'; subst hi'
  exact sandwich (InD := fun x => ∃ i, x ≤ p i) (InB := fun x => ∃ j, j ≠ i' ∧ x ≤ p j) (a := p i') hF
    (fun _ => ⟨fun ⟨i, hi⟩ => (em (i = i')).elim (fun h => Or.inl (h ▸ hi)) (fun h => Or.inr ⟨i, h, hi⟩),
      fun h => h.elim (fun h => ⟨i', h⟩) (fun ⟨j, _, hj⟩ => ⟨j, hj⟩)⟩)
    (fun _ _ hxy ⟨j, hj, hy⟩ => ⟨j, hj, hxy.trans hy⟩) (hrS i' (Finset.mem_singleton_self i'))
    (fun z hza ⟨j, hj, hzj⟩ => hcross i' (Finset.mem_singleton_self i') j (by simpa using hj) z hza hzj)
    nw ⊤ htop le_top n hU hle

/-- **Reduction to bags.** For a finite family with a separator tree over the whole index set, the cut has a witness as
soon as every bag closes. -/
theorem cut_of_tree [Fintype ι] [Nonempty ι] {F : α → α → α} {Bag : Finset ι → Prop}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α) (htree : Tree p Bag Finset.univ)
    (htop : ¬ ∃ i, ⊤ ≤ p i)
    (hbag : (∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) →
      ∀ S, Bag S → Closes F p S) :
    ∃ x, (∃ i, x ≤ p i) ∧ ∃ y, ¬ (∃ i, y ≤ p i) ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  have nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y :=
    fun x hx y hy => ⟨fun h => hno ⟨x, hx, y, hy, Or.inl h⟩, fun h => hno ⟨x, hx, y, hy, Or.inr h⟩⟩
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨n, hU, i, hi⟩ := orbit_end (InD := fun x => ∃ i, x ≤ p i) hF ⟨i₀, Finset.inf_le (Finset.mem_univ i₀)⟩
    nw ⊤ htop le_top
  exact tree_closes hF htop nw (hbag nw) htree (Finset.univ.inf p) (fun i _ => Finset.inf_le (Finset.mem_univ i))
    (fun i _ j hj => absurd (Finset.mem_univ j) hj) ⟨n, hU, i, Finset.mem_univ i, hi⟩

end Mordor.Crossing
