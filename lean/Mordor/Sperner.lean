import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.ZMod.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Data.List.InsertIdx

/-!
# A product Sperner lemma (log §34.3n)

Cells are pairs `(A, B)`, `∅ ≠ A ⊆ P`, `∅ ≠ B ⊆ Q`. A maximal chain of cells is a *word*: an ordering of `P ⊔ Q`
that starts in `Q` and ends in `P` (`Valid`). Its cells are those of its proper prefixes: `A` is the `P`-letters
not yet read, `B` the `Q`-letters read (`cells`). Given Sperner labellings `f1 c ∈ c.1` and `f2 c ∈ c.2`, a word
is *good* when `f1` is a bijection onto `P` on its first `|P|` cells and `f2` a bijection onto `Q` on its last
`|Q|` cells (`Good`; the `|P|`-th cell is shared).

**`odd_goods`: the number of good words is odd.** Proof: door counting.
- `removal`, `doors`: the per-chain door parity.
- `cells_sw`: the adjacent swap is the pseudomanifold involution.
- `boundary`, `reduce`: the boundary doors are the good words of `(P ∖ i0, Q)`.
- `base`: `({i}, Q)` has exactly one good word.
-/

namespace Mordor.Sperner
open Finset Classical
set_option linter.unusedSectionVars false

section Removal
variable {α : Type*}

theorem cons_eq_iff {x : α} {L M : Multiset α} : x ::ₘ L = M ↔ x ∈ M ∧ L = M.erase x := by
  constructor
  · rintro rfl; simp
  · rintro ⟨h, rfl⟩; exact Multiset.cons_erase h

/-- **Removal parity.** Deleting one letter of `a` leaves the multiset `M` an odd number of times iff
`a = M + {y}` for some `y ∉ M`. -/
theorem removal (a : List α) (M : Multiset α) (hM : M.Nodup) :
    (∑ u ∈ range a.length, if ((a.eraseIdx u : List α) : Multiset α) = M then (1 : ZMod 2) else 0) =
      if ∃ y, y ∉ M ∧ (a : Multiset α) = y ::ₘ M then 1 else 0 := by
  induction a generalizing M with
  | nil => simp
  | cons x a ih =>
    rw [List.length_cons, sum_range_succ']
    simp only [List.eraseIdx_cons_succ, List.eraseIdx_cons_zero]
    have nd : ∀ {N : Multiset α}, N.Nodup → x ∉ N.erase x := fun {N} hN hm => by
      have := Multiset.count_erase_self x N
      have := Multiset.count_pos.2 hm
      have := Multiset.nodup_iff_count_le_one.1 hN x
      omega
    by_cases hx : x ∈ M
    · have hs : (∑ u ∈ range a.length, if ((x :: a.eraseIdx u : List α) : Multiset α) = M then (1 : ZMod 2)
          else 0) = ∑ u ∈ range a.length, if ((a.eraseIdx u : List α) : Multiset α) = M.erase x then 1 else 0 := by
        refine sum_congr rfl fun u _ => ?_
        rw [← Multiset.cons_coe]; simp only [cons_eq_iff, hx, true_and]
      rw [hs, ih (M.erase x) (hM.erase x)]
      have key : (∃ y, y ∉ M.erase x ∧ (a : Multiset α) = y ::ₘ M.erase x) ↔
          ((a : Multiset α) = M ∨ ∃ y, y ∉ M ∧ (a : Multiset α) = y ::ₘ M.erase x) := by
        constructor
        · rintro ⟨y, hy, h⟩
          by_cases hyx : y = x
          · subst hyx; left; rw [h, Multiset.cons_erase hx]
          · right; exact ⟨y, fun hyM => hy ((Multiset.mem_erase_of_ne hyx).2 hyM), h⟩
        · rintro (h | ⟨y, hy, h⟩)
          · exact ⟨x, nd hM, by rw [h, Multiset.cons_erase hx]⟩
          · exact ⟨y, fun hm => hy (Multiset.mem_of_mem_erase hm), h⟩
      have excl : (a : Multiset α) = M → ¬ ∃ y, y ∉ M ∧ (a : Multiset α) = y ::ₘ M.erase x := by
        rintro h ⟨y, hy, h'⟩
        have hxa : x ∈ (a : Multiset α) := h ▸ hx
        rw [h'] at hxa
        rcases Multiset.mem_cons.1 hxa with rfl | hm
        · exact hy hx
        · exact nd hM hm
      have target : (∃ y, y ∉ M ∧ ((x :: a : List α) : Multiset α) = y ::ₘ M) ↔
          ∃ y, y ∉ M ∧ (a : Multiset α) = y ::ₘ M.erase x := by
        refine exists_congr fun y => and_congr_right fun hy => ?_
        have hyx : y ≠ x := fun e => hy (e ▸ hx)
        rw [← Multiset.cons_coe, cons_eq_iff, Multiset.erase_cons_tail _ hyx]
        simp [hx]
      rw [key, target]
      by_cases h1 : (a : Multiset α) = M
      · rw [if_pos (Or.inl h1), if_pos h1, if_neg (excl h1)]; decide
      · simp only [h1, false_or, if_false, add_zero]
    · have hs : (∑ u ∈ range a.length, if ((x :: a.eraseIdx u : List α) : Multiset α) = M then (1 : ZMod 2)
          else 0) = 0 := by
        refine sum_eq_zero fun u _ => ?_
        rw [← Multiset.cons_coe]; simp only [cons_eq_iff, hx, false_and, if_false]
      rw [hs, zero_add]
      have target : (∃ y, y ∉ M ∧ ((x :: a : List α) : Multiset α) = y ::ₘ M) ↔ (a : Multiset α) = M := by
        constructor
        · rintro ⟨y, hy, h⟩
          rw [← Multiset.cons_coe] at h
          by_cases hyx : y = x
          · subst hyx; exact (Multiset.cons_inj_right _).1 h
          · have : x ∈ y ::ₘ M := h ▸ Multiset.mem_cons_self x _
            exact absurd ((Multiset.mem_cons.1 this).resolve_left (Ne.symm hyx)) hx
        · intro h; exact ⟨x, hx, by rw [← Multiset.cons_coe, h]⟩
      rw [target]
      split_ifs <;> rfl

end Removal

section PerChain
variable {α β X : Type*}

/-- Indicator in `ZMod 2`. -/
noncomputable abbrev ind (p : Prop) : ZMod 2 := if p then 1 else 0

theorem ite_iff {p q : Prop} {_ : Decidable p} {_ : Decidable q} (h : p ↔ q) :
    (if p then (1 : ZMod 2) else 0) = if q then 1 else 0 := by simp [h]

theorem ind_and (p q : Prop) : ind (p ∧ q) = ind p * ind q := by
  unfold ind; split_ifs <;> simp_all

theorem neg_two (y : ZMod 2) : -y = y := by revert y; decide

theorem removal_P (P : Finset α) (i0 : α) (hi0 : i0 ∈ P) (a : List α) (ha : ∀ x ∈ a, x ∈ P) :
    (∑ u ∈ range a.length, ind (((a.eraseIdx u : List α) : Multiset α) = (P.erase i0).val)) =
      ind ((a : Multiset α) = P.val) := by
  unfold ind
  refine Eq.trans (b := if ∃ y, y ∉ (P.erase i0).val ∧ (a : Multiset α) = y ::ₘ (P.erase i0).val then (1 : ZMod 2)
    else 0) (by convert removal a _ (P.erase i0).nodup) (ite_iff ?_)
  have hP : P.val = i0 ::ₘ (P.erase i0).val := by
    rw [Finset.erase_val, Multiset.cons_erase (by simpa using hi0)]
  constructor
  · rintro ⟨y, hy, h⟩
    have hyP : y ∈ P := ha y (by rw [← Multiset.mem_coe, h]; exact Multiset.mem_cons_self _ _)
    have : y = i0 := by
      by_contra hne; exact hy (Finset.mem_erase.2 ⟨hne, hyP⟩)
    rw [h, this, ← hP]
  · intro h
    exact ⟨i0, fun hm => (Finset.mem_erase.1 hm).1 rfl, by rw [h, hP]⟩

theorem removal_Q (Q : Finset β) (b : List β) (hb : ∀ x ∈ b, x ∈ Q) :
    (∑ u ∈ range b.length, ind (((b.eraseIdx u : List β) : Multiset β) = Q.val)) = 0 := by
  unfold ind
  refine Eq.trans (b := if ∃ y, y ∉ Q.val ∧ (b : Multiset β) = y ::ₘ Q.val then (1 : ZMod 2) else 0)
    (by convert removal b _ Q.nodup) ?_
  rw [if_neg]
  rintro ⟨y, hy, h⟩
  exact hy (by simpa using hb y (by rw [← Multiset.mem_coe, h]; exact Multiset.mem_cons_self _ _))

theorem drop_eraseIdx (L : List X) (t d : ℕ) : (L.eraseIdx t).drop d = (L.drop d).eraseIdx (t - d) := by
  induction L generalizing t d with
  | nil => simp
  | cons x L ih =>
    cases d with
    | zero => simp
    | succ d =>
      cases t with
      | zero => simp [List.tail_drop]
      | succ t => simp [ih]

theorem take_eraseIdx (L : List X) (t j : ℕ) (hj : j + 1 ≤ L.length) :
    (L.eraseIdx t).take j = (L.take (j + 1)).eraseIdx (min t j) := by
  induction L generalizing t j with
  | nil => simp at hj
  | cons x L ih =>
    cases j with
    | zero => simp
    | succ j =>
      cases t with
      | zero => simp
      | succ t =>
        simp only [List.eraseIdx_cons_succ, List.take_succ_cons, Nat.succ_min_succ]
        rw [ih t j (by simp at hj; omega)]

variable (f1 : X → α) (f2 : X → β)

/-- A chain is *good* for `(P, Q)`: `f1` is a bijection onto `P` on its first `|P|` cells and `f2` a bijection
onto `Q` on its last `|Q|` cells. -/
def Good (P : Finset α) (Q : Finset β) (cs : List X) : Prop :=
  (((cs.take P.card).map f1 : List α) : Multiset α) = P.val ∧
    (((cs.drop (P.card - 1)).map f2 : List β) : Multiset β) = Q.val

/-- **Per-chain door count.** The facets of a chain that are good for `(P ∖ i0, Q)` number an odd count iff
the chain is good for `(P, Q)`. -/
theorem doors (P : Finset α) (Q : Finset β) (i0 : α) (hi0 : i0 ∈ P) (cs : List X)
    (hk : 2 ≤ P.card) (hl : 1 ≤ Q.card) (hlen : cs.length = P.card + Q.card - 1)
    (h1 : ∀ c ∈ cs, f1 c ∈ P) (h2 : ∀ c ∈ cs, f2 c ∈ Q) :
    (∑ t ∈ range cs.length, ind (Good f1 f2 (P.erase i0) Q (cs.eraseIdx t))) = ind (Good f1 f2 P Q cs) := by
  set k := P.card with hkdef
  set l := Q.card
  have hk' : (P.erase i0).card = k - 1 := Finset.card_erase_of_mem hi0
  set a := (cs.take k).map f1 with ha
  set b := (cs.drop (k - 2)).map f2 with hb
  have hal : a.length = k := by simp [ha]; omega
  have hbl : b.length = l + 1 := by simp [hb]; omega
  have hA : ∀ t, t < cs.length → (((cs.eraseIdx t).take (k - 1)).map f1 : List α) = a.eraseIdx (min t (k - 1)) := by
    intro t ht
    rw [take_eraseIdx cs t (k - 1) (by omega), show k - 1 + 1 = k by omega, ha, List.eraseIdx_map]
  have hB : ∀ t, (((cs.eraseIdx t).drop (k - 2)).map f2 : List β) = b.eraseIdx (t - (k - 2)) := by
    intro t
    rw [drop_eraseIdx, hb, List.eraseIdx_map]
  have hgood : ∀ t, t < cs.length → (Good f1 f2 (P.erase i0) Q (cs.eraseIdx t) ↔
      (((a.eraseIdx (min t (k - 1)) : List α) : Multiset α) = (P.erase i0).val ∧
        ((b.eraseIdx (t - (k - 2)) : List β) : Multiset β) = Q.val)) := by
    intro t ht
    unfold Good
    rw [hk', hA t ht, show k - 1 - 1 = k - 2 by omega, hB t]
  rw [sum_congr rfl fun t ht => by rw [hgood t (Finset.mem_range.1 ht)]]
  simp only [ind_and]
  rw [hlen, show k + l - 1 = (k - 1) + l by omega, sum_range_add]
  have e1 : ∀ x ∈ range (k - 1), ind (((a.eraseIdx (min x (k - 1)) : List α) : Multiset α) = (P.erase i0).val) *
      ind (((b.eraseIdx (x - (k - 2)) : List β) : Multiset β) = Q.val) =
      ind (((a.eraseIdx x : List α) : Multiset α) = (P.erase i0).val) *
      ind (((b.eraseIdx 0 : List β) : Multiset β) = Q.val) := by
    intro x hx
    have := Finset.mem_range.1 hx
    rw [min_eq_left (by omega), show x - (k - 2) = 0 by omega]
  have e2 : ∀ x ∈ range l, ind (((a.eraseIdx (min (k - 1 + x) (k - 1)) : List α) : Multiset α) = (P.erase i0).val) *
      ind (((b.eraseIdx (k - 1 + x - (k - 2)) : List β) : Multiset β) = Q.val) =
      ind (((a.eraseIdx (k - 1) : List α) : Multiset α) = (P.erase i0).val) *
      ind (((b.eraseIdx (x + 1) : List β) : Multiset β) = Q.val) := by
    intro x _
    rw [min_eq_right (by omega), show k - 1 + x - (k - 2) = x + 1 by omega]
  rw [sum_congr rfl e1, sum_congr rfl e2, ← sum_mul, ← mul_sum]
  have rq := removal_Q Q b (by
    intro y hy; rw [hb, List.mem_map] at hy; obtain ⟨c, hc, rfl⟩ := hy; exact h2 c (List.mem_of_mem_drop hc))
  rw [hbl, sum_range_succ'] at rq
  have rq' : (∑ x ∈ range l, ind (((b.eraseIdx (x + 1) : List β) : Multiset β) = Q.val)) =
      ind (((b.eraseIdx 0 : List β) : Multiset β) = Q.val) := by
    rw [← neg_two (ind _)]; exact eq_neg_of_add_eq_zero_left rq
  rw [rq']
  have rp := removal_P P i0 hi0 a (by
    intro y hy; rw [ha, List.mem_map] at hy; obtain ⟨c, hc, rfl⟩ := hy; exact h1 c (List.mem_of_mem_take hc))
  rw [hal, show k = (k - 1) + 1 by omega, sum_range_succ] at rp
  have hb0 : (b.eraseIdx 0 : List β) = (cs.drop (k - 1)).map f2 := by
    rw [hb, List.eraseIdx_zero, ← List.map_tail, List.tail_drop, show k - 2 + 1 = k - 1 by omega]
  unfold Good
  rw [ind_and, ← hb0, mul_comm (ind ((a : Multiset α) = P.val)), ← rp, mul_add]
  ac_rfl

end PerChain

section Words
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The cell of a prefix `S`: the generators of `P` not yet removed, the generators of `Q` already added. -/
noncomputable def cellOf (P : Finset ι) (Q : Finset κ) (S : Finset (ι ⊕ κ)) : Finset ι × Finset κ :=
  (P.filter fun a => Sum.inl a ∉ S, Q.filter fun b => Sum.inr b ∈ S)

/-- The letters of `w` at positions `≤ t`. -/
noncomputable def pre {n : ℕ} (w : Fin n → ι ⊕ κ) (t : ℕ) : Finset (ι ⊕ κ) :=
  (univ.filter fun s : Fin n => s.val ≤ t).image w

theorem mem_pre {n : ℕ} {w : Fin n → ι ⊕ κ} {t : ℕ} {x : ι ⊕ κ} :
    x ∈ pre w t ↔ ∃ s : Fin n, s.val ≤ t ∧ w s = x := by
  simp [pre]

/-- The maximal chain of cells spelled by the word `w`: the cells of its prefixes of length `1, …, n - 1`. -/
noncomputable def cells (P : Finset ι) (Q : Finset κ) {n : ℕ} (w : Fin n → ι ⊕ κ) : List (Finset ι × Finset κ) :=
  (List.range (n - 1)).map fun t => cellOf P Q (pre w t)

theorem cells_length (P : Finset ι) (Q : Finset κ) {n : ℕ} (w : Fin n → ι ⊕ κ) :
    (cells P Q w).length = n - 1 := by simp [cells]

theorem cells_getElem (P : Finset ι) (Q : Finset κ) {n : ℕ} (w : Fin n → ι ⊕ κ) (t : ℕ)
    (h : t < (cells P Q w).length) : (cells P Q w)[t] = cellOf P Q (pre w t) := by simp [cells]

/-- A word for `(P, Q)`: an enumeration of `P ⊔ Q` starting in `Q` and ending in `P`. Words are the maximal
chains of the cell poset. -/
structure Valid (P : Finset ι) (Q : Finset κ) {n : ℕ} (w : Fin n → ι ⊕ κ) : Prop where
  inj : Function.Injective w
  mem : ∀ s, w s ∈ P.disjSum Q
  first : ∀ s : Fin n, s.val = 0 → (w s).isRight
  last : ∀ s : Fin n, s.val + 1 = n → (w s).isLeft

noncomputable def words (P : Finset ι) (Q : Finset κ) (n : ℕ) : Finset (Fin n → ι ⊕ κ) :=
  univ.filter (Valid P Q)

theorem left_of_isLeft {P : Finset ι} {Q : Finset κ} {x : ι ⊕ κ} (hx : x ∈ P.disjSum Q) (h : x.isLeft) :
    ∃ a ∈ P, x = Sum.inl a := by
  rcases x with a | b
  · exact ⟨a, by simpa using hx, rfl⟩
  · simp at h

theorem right_of_isRight {P : Finset ι} {Q : Finset κ} {x : ι ⊕ κ} (hx : x ∈ P.disjSum Q) (h : x.isRight) :
    ∃ b ∈ Q, x = Sum.inr b := by
  rcases x with a | b
  · simp at h
  · exact ⟨b, by simpa using hx, rfl⟩

/-- Every cell of a word is a cell: `∅ ≠ A ⊆ P`, `∅ ≠ B ⊆ Q`. -/
theorem cell_props {P : Finset ι} {Q : Finset κ} {n : ℕ} {w : Fin n → ι ⊕ κ} (hw : Valid P Q w) {t : ℕ}
    (ht : t + 1 < n) :
    (cellOf P Q (pre w t)).1 ⊆ P ∧ (cellOf P Q (pre w t)).1.Nonempty ∧
      (cellOf P Q (pre w t)).2 ⊆ Q ∧ (cellOf P Q (pre w t)).2.Nonempty := by
  refine ⟨filter_subset _ _, ?_, filter_subset _ _, ?_⟩
  · obtain ⟨a, ha, he⟩ := left_of_isLeft (hw.mem ⟨n - 1, by omega⟩) (hw.last _ (by simp; omega))
    refine ⟨a, mem_filter.2 ⟨ha, fun hm => ?_⟩⟩
    obtain ⟨s, hs, hse⟩ := mem_pre.1 hm
    have := hw.inj (hse.trans he.symm)
    rw [Fin.ext_iff] at this; simp at this; omega
  · obtain ⟨b, hb, he⟩ := right_of_isRight (hw.mem ⟨0, by omega⟩) (hw.first _ rfl)
    exact ⟨b, mem_filter.2 ⟨hb, mem_pre.2 ⟨⟨0, by omega⟩, Nat.zero_le _, he⟩⟩⟩

theorem mem_cells {P : Finset ι} {Q : Finset κ} {n : ℕ} {w : Fin n → ι ⊕ κ} {c : Finset ι × Finset κ} :
    c ∈ cells P Q w ↔ ∃ t, t + 1 < n ∧ c = cellOf P Q (pre w t) := by
  simp only [cells, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, by omega, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, by omega, rfl⟩

/-! ### The adjacent transposition -/

noncomputable def sw (n t : ℕ) : Equiv.Perm (Fin n) :=
  if h : t + 1 < n then Equiv.swap ⟨t, by omega⟩ ⟨t + 1, h⟩ else Equiv.refl _

theorem sw_val {n t : ℕ} (h : t + 1 < n) (r : Fin n) :
    (sw n t r).val = if r.val = t then t + 1 else if r.val = t + 1 then t else r.val := by
  simp only [sw, dif_pos h, Equiv.swap_apply_def]
  by_cases h1 : r.val = t
  · have : r = ⟨t, by omega⟩ := Fin.ext h1
    simp [this]
  · by_cases h2 : r.val = t + 1
    · have : r = ⟨t + 1, h⟩ := Fin.ext h2
      simp [this]
    · have e1 : r ≠ ⟨t, by omega⟩ := fun e => h1 (by rw [e])
      have e2 : r ≠ ⟨t + 1, h⟩ := fun e => h2 (by rw [e])
      simp [e1, e2, h1, h2]

theorem sw_sw (n t : ℕ) (r : Fin n) : sw n t (sw n t r) = r := by
  unfold sw; split_ifs <;> simp

theorem sw_le_iff {n t s : ℕ} (hst : s ≠ t) (r : Fin n) : (sw n t r).val ≤ s ↔ r.val ≤ s := by
  by_cases h : t + 1 < n
  · rw [sw_val h]; split_ifs <;> omega
  · simp [sw, dif_neg h]

theorem pre_sw {n : ℕ} (w : Fin n → ι ⊕ κ) {s t : ℕ} (hst : s ≠ t) : pre (w ∘ sw n t) s = pre w s := by
  ext x
  simp only [mem_pre, Function.comp]
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨sw n t r, (sw_le_iff hst r).2 hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩; exact ⟨sw n t r, (sw_le_iff hst (sw n t r)).1 (by rw [sw_sw]; exact hr), by simp [sw_sw]⟩

/-- Swapping the letters at `t`, `t + 1` changes exactly the cell at `t`: the facet is shared. -/
theorem cells_sw (P : Finset ι) (Q : Finset κ) {n : ℕ} (w : Fin n → ι ⊕ κ) (t : ℕ) :
    (cells P Q (w ∘ sw n t)).eraseIdx t = (cells P Q w).eraseIdx t := by
  apply List.ext_getElem
  · simp [List.length_eraseIdx, cells_length]
  · intro i h1 h2
    rw [List.getElem_eraseIdx, List.getElem_eraseIdx]
    split_ifs with hi
    · rw [cells_getElem, cells_getElem, pre_sw w (by omega)]
    · rw [cells_getElem, cells_getElem, pre_sw w (by omega)]

end Words

section Reduce
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The swap at `t` stays a word: at `t = 0` the new first letter must be in `Q`, at `t = n - 2` the new last
letter in `P`. -/
def SV {n : ℕ} (w : Fin n → ι ⊕ κ) (t : ℕ) : Prop :=
  (t = 0 → ∀ s : Fin n, s.val = 1 → (w s).isRight) ∧ (t + 2 = n → ∀ s : Fin n, s.val = t → (w s).isLeft)

variable {P : Finset ι} {Q : Finset κ}

theorem valid_sw {n t : ℕ} {w : Fin n → ι ⊕ κ} (hw : Valid P Q w) (ht : t + 1 < n) (hsv : SV w t) :
    Valid P Q (w ∘ sw n t) where
  inj := hw.inj.comp (sw n t).injective
  mem s := hw.mem _
  first s hs := by
    have := sw_val ht s
    by_cases h0 : t = 0
    · exact hsv.1 h0 _ (by rw [this]; split_ifs <;> omega)
    · exact hw.first _ (by rw [this]; split_ifs <;> omega)
  last s hs := by
    have := sw_val ht s
    by_cases h0 : t + 2 = n
    · exact hsv.2 h0 _ (by rw [this]; split_ifs <;> omega)
    · exact hw.last _ (by rw [this]; split_ifs <;> omega)

theorem sv_sw {n t : ℕ} {w : Fin n → ι ⊕ κ} (hw : Valid P Q w) (ht : t + 1 < n) : SV (w ∘ sw n t) t :=
  ⟨fun h0 s hs => hw.first _ (by rw [sw_val ht]; split_ifs <;> omega),
   fun h0 s hs => hw.last _ (by rw [sw_val ht]; split_ifs <;> omega)⟩

theorem sw_ne {n t : ℕ} {w : Fin n → ι ⊕ κ} (hw : Valid P Q w) (ht : t + 1 < n) : w ∘ sw n t ≠ w := by
  intro h
  have := congrFun h ⟨t, by omega⟩
  simp only [Function.comp] at this
  have := congrArg Fin.val (hw.inj this)
  rw [sw_val ht] at this; simp at this

theorem mem_eraseIdx_cells {n : ℕ} {w : Fin n → ι ⊕ κ} {t : ℕ} {c : Finset ι × Finset κ}
    (hc : c ∈ (cells P Q w).eraseIdx t) : ∃ t', t' ≠ t ∧ t' + 1 < n ∧ c = cellOf P Q (pre w t') := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hl := cells_length P Q w
  rw [List.getElem_eraseIdx]
  split_ifs with h
  · refine ⟨i, by omega, ?_, cells_getElem _ _ _ _ _⟩
    have := List.length_eraseIdx_le (cells P Q w) t; omega
  · refine ⟨i + 1, by omega, ?_, cells_getElem _ _ _ _ _⟩
    rw [List.length_eraseIdx] at hi; split_ifs at hi <;> omega

/-! ### Deleting / inserting the letter at position 1 -/

def i1 (m : ℕ) (i : Fin (m + 1)) : Fin (m + 2) := ⟨if i.val = 0 then 0 else i.val + 1, by split_ifs <;> (try contradiction) <;> omega⟩
def j1 (m : ℕ) (j : Fin (m + 2)) : Fin (m + 1) := ⟨if j.val = 0 then 0 else j.val - 1, by split_ifs <;> (try contradiction) <;> omega⟩
theorem i1_val (m : ℕ) (i : Fin (m + 1)) : (i1 m i).val = if i.val = 0 then 0 else i.val + 1 := rfl
theorem j1_val (m : ℕ) (j : Fin (m + 2)) : (j1 m j).val = if j.val = 0 then 0 else j.val - 1 := rfl

def del1 {X : Type*} {m : ℕ} (w : Fin (m + 2) → X) : Fin (m + 1) → X := fun i => w (i1 m i)

def ins1 {X : Type*} {m : ℕ} (x : X) (v : Fin (m + 1) → X) : Fin (m + 2) → X :=
  fun j => if j.val = 1 then x else v (j1 m j)

theorem app_eq {X : Type*} {n : ℕ} (f : Fin n → X) {a b : Fin n} (h : a.val = b.val) : f a = f b :=
  congrArg f (Fin.ext h)

theorem del1_ins1 {X : Type*} {m : ℕ} (x : X) (v : Fin (m + 1) → X) : del1 (ins1 x v) = v := by
  funext i
  simp only [del1, ins1]
  rw [if_neg]
  · apply app_eq; rw [j1_val, i1_val]; split_ifs <;> (try contradiction) <;> omega
  · rw [i1_val]; by_cases h : (i : ℕ) = 0 <;> simp [h]

theorem ins1_del1 {X : Type*} {m : ℕ} {x : X} (w : Fin (m + 2) → X) (h : w ⟨1, by omega⟩ = x) :
    ins1 x (del1 w) = w := by
  funext j
  simp only [del1, ins1]
  by_cases h1 : j.val = 1
  · rw [if_pos h1, ← h]; exact app_eq w (by simp [h1])
  · rw [if_neg h1]; apply app_eq; rw [i1_val, j1_val]; split_ifs <;> (try contradiction) <;> omega

theorem pre_ins1 {m : ℕ} (x : ι ⊕ κ) (v : Fin (m + 1) → ι ⊕ κ) (t : ℕ) :
    pre (ins1 x v) (t + 1) = insert x (pre v t) := by
  ext y
  simp only [mem_pre, mem_insert]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases h1 : j.val = 1
    · left; simp [ins1, h1]
    · right
      exact ⟨j1 m j, by rw [j1_val]; split_ifs <;> (try contradiction) <;> omega, by simp [ins1, h1]⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨⟨1, by omega⟩, by simp, by simp [ins1]⟩
    · refine ⟨i1 m i, by rw [i1_val]; split_ifs <;> (try contradiction) <;> omega, ?_⟩
      simp only [ins1]
      rw [if_neg]
      · apply app_eq; rw [j1_val, i1_val]; split_ifs <;> (try contradiction) <;> omega
      · rw [i1_val]; by_cases h : (i : ℕ) = 0 <;> simp [h]

theorem cellOf_insert (P : Finset ι) (Q : Finset κ) (i0 : ι) (S : Finset (ι ⊕ κ)) :
    cellOf P Q (insert (Sum.inl i0) S) = cellOf (P.erase i0) Q S := by
  simp only [cellOf, Prod.mk.injEq]
  constructor
  · ext a; simp only [mem_filter, mem_insert, Sum.inl.injEq, mem_erase]; tauto
  · ext b; simp

theorem cells_ins1 (P : Finset ι) (Q : Finset κ) (i0 : ι) {m : ℕ} (v : Fin (m + 1) → ι ⊕ κ) :
    cells P Q (ins1 (Sum.inl i0) v) = cellOf P Q (pre (ins1 (Sum.inl i0) v) 0) :: cells (P.erase i0) Q v := by
  simp only [cells, show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega, List.range_succ_eq_map,
    List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp only [Function.comp, pre_ins1, cellOf_insert]

theorem valid_del1 {P : Finset ι} {Q : Finset κ} {i0 : ι} {m : ℕ} (hm : 1 ≤ m) {w : Fin (m + 2) → ι ⊕ κ}
    (hw : Valid P Q w) (h1 : w ⟨1, by omega⟩ = Sum.inl i0) : Valid (P.erase i0) Q (del1 w) where
  inj i j h := by
    have := congrArg Fin.val (hw.inj h)
    rw [i1_val, i1_val] at this
    ext; split_ifs at this <;> (try contradiction) <;> omega
  mem i := by
    have hne : w (i1 m i) ≠ Sum.inl i0 := by
      rw [← h1]; intro e
      have : (i1 m i).val = 1 := congrArg Fin.val (hw.inj e)
      rw [i1_val] at this; split_ifs at this <;> (try contradiction) <;> omega
    have := hw.mem (i1 m i)
    simp only [del1]
    revert hne this
    generalize w (i1 m i) = y
    rcases y with a | b
    · intro hne h; simp only [inl_mem_disjSum, mem_erase] at h ⊢; exact ⟨fun e => hne (by rw [e]), h⟩
    · intro _ h; simpa using h
  first i hi := hw.first _ (by rw [i1_val]; split_ifs <;> (try contradiction) <;> omega)
  last i hi := hw.last _ (by rw [i1_val]; split_ifs <;> (try contradiction) <;> omega)

theorem valid_ins1 {P : Finset ι} {Q : Finset κ} {i0 : ι} (hi0 : i0 ∈ P) {m : ℕ} (hm : 1 ≤ m)
    {v : Fin (m + 1) → ι ⊕ κ} (hv : Valid (P.erase i0) Q v) : Valid P Q (ins1 (Sum.inl i0) v) where
  inj i j h := by
    have nin : ∀ k, v k ≠ Sum.inl i0 := fun k e => by
      have := hv.mem k; rw [e, inl_mem_disjSum] at this; simp at this
    simp only [ins1] at h
    by_cases hi : i.val = 1 <;> by_cases hj : j.val = 1
    · ext; omega
    · rw [if_pos hi, if_neg hj] at h; exact absurd h.symm (nin _)
    · rw [if_neg hi, if_pos hj] at h; exact absurd h (nin _)
    · rw [if_neg hi, if_neg hj] at h
      have := congrArg Fin.val (hv.inj h); rw [j1_val, j1_val] at this
      ext; split_ifs at this <;> (try contradiction) <;> omega
  mem j := by
    simp only [ins1]
    split_ifs
    · simpa using hi0
    · have := hv.mem (j1 m j)
      revert this; generalize v (j1 m j) = y
      rcases y with a | b
      · intro h; simp only [inl_mem_disjSum, mem_erase] at h ⊢; exact h.2
      · intro h; simpa using h
  first j hj := by
    simp only [ins1]; rw [if_neg (by omega)]; exact hv.first _ (by rw [j1_val]; split_ifs <;> (try contradiction) <;> omega)
  last j hj := by
    simp only [ins1]; rw [if_neg (by omega)]; exact hv.last _ (by rw [j1_val]; split_ifs <;> (try contradiction) <;> omega)

end Reduce

section Count
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (f1 : Finset ι × Finset κ → ι) (f2 : Finset ι × Finset κ → κ)
  (hs1 : ∀ c : Finset ι × Finset κ, c.1.Nonempty → c.2.Nonempty → f1 c ∈ c.1)
  (hs2 : ∀ c : Finset ι × Finset κ, c.1.Nonempty → c.2.Nonempty → f2 c ∈ c.2)
include hs1 hs2

theorem labels_mem {P : Finset ι} {Q : Finset κ} {n : ℕ} {w : Fin n → ι ⊕ κ} (hw : Valid P Q w) :
    ∀ c ∈ cells P Q w, f1 c ∈ P ∧ f2 c ∈ Q := by
  intro c hc
  obtain ⟨t, ht, rfl⟩ := mem_cells.1 hc
  obtain ⟨h1, h2, h3, h4⟩ := cell_props hw ht
  exact ⟨h1 (hs1 _ h2 h4), h3 (hs2 _ h2 h4)⟩

/-- A boundary door is the deletion of the first cell of a word whose second letter is `i0`. -/
theorem boundary {P : Finset ι} {Q : Finset κ} {i0 : ι} {m : ℕ} {w : Fin (m + 2) → ι ⊕ κ}
    (hw : Valid P Q w) {t : ℕ} (ht : t < m + 1)
    (hd : Good f1 f2 (P.erase i0) Q ((cells P Q w).eraseIdx t)) (hsv : ¬ SV w t) :
    t = 0 ∧ w ⟨1, by omega⟩ = Sum.inl i0 := by
  unfold SV at hsv
  by_cases hA : t = 0 → ∀ s : Fin (m + 2), s.val = 1 → (w s).isRight
  · exfalso
    have hB : ¬ (t + 2 = m + 2 → ∀ s : Fin (m + 2), s.val = t → (w s).isLeft) := fun hB => hsv ⟨hA, hB⟩
    push_neg at hB
    obtain ⟨htm, s, hs, hsl⟩ := hB
    obtain ⟨q, hq, hwq⟩ := right_of_isRight (hw.mem s) (by simpa using hsl)
    have hqm : q ∈ (((((cells P Q w).eraseIdx t).drop ((P.erase i0).card - 1)).map f2 : List κ) :
        Multiset κ) := by rw [hd.2]; simpa using hq
    obtain ⟨c, hc, hcq⟩ := List.mem_map.1 (Multiset.mem_coe.1 hqm)
    obtain ⟨t', ht't, ht', rfl⟩ := mem_eraseIdx_cells (List.mem_of_mem_drop hc)
    obtain ⟨-, h2, -, h4⟩ := cell_props hw ht'
    have := hs2 _ h2 h4
    rw [hcq] at this
    obtain ⟨s', hs', hs'e⟩ := mem_pre.1 (mem_filter.1 this).2
    have := congrArg Fin.val (hw.inj (hs'e.trans hwq.symm))
    omega
  · push_neg at hA
    obtain ⟨ht0, s, hs, hsr⟩ := hA
    obtain ⟨a, ha, hwa⟩ := left_of_isLeft (hw.mem s) (by simpa using hsr)
    have hs1' : s = ⟨1, by omega⟩ := Fin.ext hs
    refine ⟨ht0, ?_⟩
    rw [← hs1', hwa]
    by_contra hne
    have hai : a ≠ i0 := fun e => hne (by rw [e])
    have ham : a ∈ (((((cells P Q w).eraseIdx t).take (P.erase i0).card).map f1 : List ι) : Multiset ι) := by
      rw [hd.1]; exact Finset.mem_erase.2 ⟨hai, ha⟩
    obtain ⟨c, hc, hca⟩ := List.mem_map.1 (Multiset.mem_coe.1 ham)
    obtain ⟨t', ht't, ht', rfl⟩ := mem_eraseIdx_cells (List.mem_of_mem_take hc)
    obtain ⟨-, h2, -, h4⟩ := cell_props hw ht'
    have := hs1 _ h2 h4
    rw [hca] at this
    exact (mem_filter.1 this).2 (mem_pre.2 ⟨s, by omega, hwa⟩)

/-- The good words of `(P, Q)`. -/
noncomputable def goods (P : Finset ι) (Q : Finset κ) (n : ℕ) : Finset (Fin n → ι ⊕ κ) :=
  (words P Q n).filter fun w => Good f1 f2 P Q (cells P Q w)

/-- **Reduction.** The number of good words of `(P, Q)` and of `(P ∖ i0, Q)` agree mod 2. -/
theorem reduce (P : Finset ι) (Q : Finset κ) (i0 : ι) (hi0 : i0 ∈ P) (hk : 2 ≤ P.card) (hl : 1 ≤ Q.card)
    (m : ℕ) (hm : m + 2 = P.card + Q.card) :
    ((goods f1 f2 P Q (m + 2)).card : ZMod 2) = ((goods f1 f2 (P.erase i0) Q (m + 1)).card : ZMod 2) := by
  have hm1 : 1 ≤ m := by omega
  set S := ((words P Q (m + 2)) ×ˢ range (m + 1)).filter
    (fun x => Good f1 f2 (P.erase i0) Q ((cells P Q x.1).eraseIdx x.2)) with hS
  -- (A) double counting against the per-chain door lemma
  have hA : (S.card : ZMod 2) = ((goods f1 f2 P Q (m + 2)).card : ZMod 2) := by
    rw [hS, goods, natCast_card_filter, natCast_card_filter, sum_product]
    refine sum_congr rfl fun w hw => ?_
    have hwv : Valid P Q w := (mem_filter.1 hw).2
    have := doors f1 f2 P Q i0 hi0 (cells P Q w) hk hl (by rw [cells_length]; omega)
      (fun c hc => (labels_mem f1 f2 hs1 hs2 hwv c hc).1) (fun c hc => (labels_mem f1 f2 hs1 hs2 hwv c hc).2)
    rw [cells_length, show m + 2 - 1 = m + 1 by omega] at this
    simpa [ind] using this
  -- (B) the interior doors pair off under the adjacent swap
  have hint : (((S.filter fun x => SV x.1 x.2)).card : ZMod 2) = 0 := by
    rw [card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    refine sum_involution (fun x _ => (x.1 ∘ sw (m + 2) x.2, x.2)) ?_ ?_ ?_ ?_
    · intro _ _; decide
    · intro x hx _ he
      simp only [mem_filter, mem_product, words, mem_univ, true_and, mem_range, hS] at hx
      exact sw_ne hx.1.1.1 (by omega) (congrArg Prod.fst he)
    · intro x hx
      simp only [mem_filter, mem_product, words, mem_univ, true_and, mem_range, hS] at hx ⊢
      exact ⟨⟨⟨valid_sw hx.1.1.1 (by omega) hx.2, hx.1.1.2⟩, by rw [cells_sw]; exact hx.1.2⟩,
        sv_sw hx.1.1.1 (by omega)⟩
    · intro x _
      ext1
      · funext s; simp [sw_sw]
      · rfl
  -- (C) the boundary doors are the good words of `(P ∖ i0, Q)`
  have hbd : (S.filter fun x => ¬ SV x.1 x.2).card = (goods f1 f2 (P.erase i0) Q (m + 1)).card := by
    apply card_nbij' (fun x => del1 x.1) (fun v => (ins1 (Sum.inl i0) v, 0))
    · intro x hx
      simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_product, words, mem_univ, true_and,
        mem_range, hS] at hx
      obtain ⟨⟨⟨hw, ht⟩, hd⟩, hsv⟩ := hx
      obtain ⟨h0, h1⟩ := boundary f1 f2 hs1 hs2 hw ht hd hsv
      rw [h0] at hd
      have hw' := ins1_del1 x.1 h1
      simp only [coe_filter, Set.mem_setOf_eq, goods, mem_filter, words, mem_univ, true_and]
      refine ⟨valid_del1 hm1 hw h1, ?_⟩
      rw [← hw', cells_ins1, List.eraseIdx_zero, List.tail_cons] at hd
      simpa only [del1_ins1] using hd
    · intro v hv
      simp only [coe_filter, Set.mem_setOf_eq, goods, mem_filter, words, mem_univ, true_and] at hv
      simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_product, words, mem_univ, true_and,
        mem_range, hS]
      refine ⟨⟨⟨valid_ins1 hi0 hm1 hv.1, by omega⟩, ?_⟩, ?_⟩
      · rw [cells_ins1, List.eraseIdx_zero, List.tail_cons]; exact hv.2
      · intro h
        have := h.1 rfl ⟨1, by omega⟩ rfl
        simp [ins1] at this
    · intro x hx
      simp only [coe_filter, Set.mem_setOf_eq, mem_filter, mem_product, words, mem_univ, true_and,
        mem_range, hS] at hx
      obtain ⟨⟨⟨hw, ht⟩, hd⟩, hsv⟩ := hx
      obtain ⟨h0, h1⟩ := boundary f1 f2 hs1 hs2 hw ht hd hsv
      ext1
      · exact ins1_del1 x.1 h1
      · exact h0.symm
    · intro v _
      exact del1_ins1 _ v
  have hsplit := card_filter_add_card_filter_not (s := S) (fun x => SV x.1 x.2)
  rw [← hA, ← hsplit, Nat.cast_add, hint, zero_add, hbd]

end Count

section Base
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem valid_surj {P : Finset ι} {Q : Finset κ} {n : ℕ} {w : Fin n → ι ⊕ κ} (hw : Valid P Q w)
    (hn : n = P.card + Q.card) {x : ι ⊕ κ} (hx : x ∈ P.disjSum Q) : ∃ s, w s = x := by
  have hsub : univ.image w ⊆ P.disjSum Q := fun y hy => by
    obtain ⟨s, -, rfl⟩ := mem_image.1 hy; exact hw.mem s
  have heq := eq_of_subset_of_card_le hsub (by
    rw [card_image_of_injective _ hw.inj, card_univ, Fintype.card_fin, card_disjSum, hn])
  rw [← heq] at hx
  obtain ⟨s, -, hs⟩ := mem_image.1 hx
  exact ⟨s, hs⟩

/-! ### Deleting / inserting the letter at position `m` of a word of length `m + 2` -/

def iL (m : ℕ) (i : Fin (m + 1)) : Fin (m + 2) := ⟨if i.val < m then i.val else i.val + 1, by split_ifs <;> omega⟩
def jL (m : ℕ) (j : Fin (m + 2)) : Fin (m + 1) := ⟨if j.val < m then j.val else j.val - 1, by split_ifs <;> omega⟩
theorem iL_val (m : ℕ) (i : Fin (m + 1)) : (iL m i).val = if i.val < m then i.val else i.val + 1 := rfl
theorem jL_val (m : ℕ) (j : Fin (m + 2)) : (jL m j).val = if j.val < m then j.val else j.val - 1 := rfl

def delL {X : Type*} {m : ℕ} (w : Fin (m + 2) → X) : Fin (m + 1) → X := fun i => w (iL m i)

def insL {X : Type*} {m : ℕ} (x : X) (v : Fin (m + 1) → X) : Fin (m + 2) → X :=
  fun j => if j.val = m then x else v (jL m j)

theorem delL_insL {X : Type*} {m : ℕ} (x : X) (v : Fin (m + 1) → X) : delL (insL x v) = v := by
  funext i
  simp only [delL, insL]
  rw [if_neg]
  · apply app_eq; rw [jL_val, iL_val]; split_ifs <;> (try contradiction) <;> omega
  · rw [iL_val]; split_ifs <;> omega

theorem insL_delL {X : Type*} {m : ℕ} {x : X} (w : Fin (m + 2) → X) (h : w ⟨m, by omega⟩ = x) :
    insL x (delL w) = w := by
  funext j
  simp only [delL, insL]
  by_cases h1 : j.val = m
  · rw [if_pos h1, ← h]; exact app_eq w (by simp [h1])
  · rw [if_neg h1]; apply app_eq; rw [iL_val, jL_val]; split_ifs <;> (try contradiction) <;> omega

theorem pre_insL {m : ℕ} (x : ι ⊕ κ) (v : Fin (m + 1) → ι ⊕ κ) {t : ℕ} (ht : t < m) :
    pre (insL x v) t = pre v t := by
  ext y
  simp only [mem_pre]
  constructor
  · rintro ⟨j, hj, rfl⟩
    refine ⟨jL m j, by rw [jL_val]; split_ifs <;> omega, ?_⟩
    simp only [insL]; rw [if_neg (by omega)]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨iL m i, by rw [iL_val]; split_ifs <;> omega, ?_⟩
    simp only [insL]
    rw [if_neg]
    · apply app_eq; rw [jL_val, iL_val]; split_ifs <;> (try contradiction) <;> omega
    · rw [iL_val]; split_ifs <;> omega

theorem cellOf_erase (P : Finset ι) (Q : Finset κ) (y : κ) (S : Finset (ι ⊕ κ)) (hy : Sum.inr y ∉ S) :
    cellOf P Q S = cellOf P (Q.erase y) S := by
  simp only [cellOf, Prod.mk.injEq, true_and]
  ext b; simp only [mem_filter, mem_erase]
  constructor
  · rintro ⟨hb, hbS⟩; exact ⟨⟨fun e => hy (e ▸ hbS), hb⟩, hbS⟩
  · rintro ⟨⟨-, hb⟩, hbS⟩; exact ⟨hb, hbS⟩

theorem cells_insL (P : Finset ι) (Q : Finset κ) (y : κ) {m : ℕ} (v : Fin (m + 1) → ι ⊕ κ)
    (hv : ∀ s, v s ≠ Sum.inr y) :
    cells P Q (insL (Sum.inr y) v) = cells P (Q.erase y) v ++ [cellOf P Q (pre (insL (Sum.inr y) v) m)] := by
  simp only [cells, show m + 2 - 1 = m + 1 by omega, show m + 1 - 1 = m by omega, List.range_succ,
    List.map_append, List.map_cons, List.map_nil]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  rw [pre_insL _ _ ht, cellOf_erase P Q y _ (fun hm => by
    obtain ⟨s, -, hs⟩ := mem_pre.1 hm; exact hv s hs)]

theorem valid_delL {P : Finset ι} {Q : Finset κ} {y : κ} {m : ℕ} (hm : 1 ≤ m) {w : Fin (m + 2) → ι ⊕ κ}
    (hw : Valid P Q w) (h1 : w ⟨m, by omega⟩ = Sum.inr y) : Valid P (Q.erase y) (delL w) where
  inj i j h := by
    have := congrArg Fin.val (hw.inj h)
    rw [iL_val, iL_val] at this
    ext; split_ifs at this <;> omega
  mem i := by
    have hne : w (iL m i) ≠ Sum.inr y := by
      rw [← h1]; intro e
      have : (iL m i).val = m := congrArg Fin.val (hw.inj e)
      rw [iL_val] at this; split_ifs at this <;> omega
    have := hw.mem (iL m i)
    simp only [delL]
    revert hne this
    generalize w (iL m i) = z
    rcases z with a | b
    · intro _ h; simpa using h
    · intro hne h; simp only [inr_mem_disjSum, mem_erase] at h ⊢; exact ⟨fun e => hne (by rw [e]), h⟩
  first i hi := hw.first _ (by rw [iL_val]; split_ifs <;> omega)
  last i hi := hw.last _ (by rw [iL_val]; split_ifs <;> omega)

theorem valid_insL {P : Finset ι} {Q : Finset κ} {y : κ} (hy : y ∈ Q) {m : ℕ} (hm : 1 ≤ m)
    {v : Fin (m + 1) → ι ⊕ κ} (hv : Valid P (Q.erase y) v) : Valid P Q (insL (Sum.inr y) v) where
  inj i j h := by
    have nin : ∀ k, v k ≠ Sum.inr y := fun k e => by
      have := hv.mem k; rw [e, inr_mem_disjSum] at this; simp at this
    simp only [insL] at h
    by_cases hi : i.val = m <;> by_cases hj : j.val = m
    · ext; omega
    · rw [if_pos hi, if_neg hj] at h; exact absurd h.symm (nin _)
    · rw [if_neg hi, if_pos hj] at h; exact absurd h (nin _)
    · rw [if_neg hi, if_neg hj] at h
      have := congrArg Fin.val (hv.inj h); rw [jL_val, jL_val] at this
      ext; split_ifs at this <;> omega
  mem j := by
    simp only [insL]
    split_ifs
    · simpa using hy
    · have := hv.mem (jL m j)
      revert this; generalize v (jL m j) = z
      rcases z with a | b
      · intro h; simpa using h
      · intro h; simp only [inr_mem_disjSum, mem_erase] at h ⊢; exact h.2
  first j hj := by
    simp only [insL]; rw [if_neg (by omega)]; exact hv.first _ (by rw [jL_val]; split_ifs <;> omega)
  last j hj := by
    simp only [insL]; rw [if_neg (by omega)]; exact hv.last _ (by rw [jL_val]; split_ifs <;> omega)

theorem top_cell {i : ι} {Q : Finset κ} {m : ℕ} {w : Fin (m + 2) → ι ⊕ κ} (hw : Valid {i} Q w)
    (hn : m + 2 = 1 + Q.card) : cellOf {i} Q (pre w m) = ({i}, Q) := by
  simp only [cellOf, Prod.mk.injEq]
  constructor
  · ext a
    simp only [mem_filter, mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl
      refine ⟨rfl, fun hm => ?_⟩
      obtain ⟨s, hs, hse⟩ := mem_pre.1 hm
      obtain ⟨a', ha', he⟩ := left_of_isLeft (hw.mem ⟨m + 1, by omega⟩) (hw.last _ rfl)
      rw [mem_singleton] at ha'; subst ha'
      have : s.val = m + 1 := congrArg Fin.val (hw.inj (hse.trans he.symm))
      omega
  · ext b
    simp only [mem_filter, and_iff_left_iff_imp]
    intro hb
    obtain ⟨s, hs⟩ := valid_surj hw (by simpa using hn) (inr_mem_disjSum.2 hb)
    refine mem_pre.2 ⟨s, ?_, hs⟩
    by_contra hlt
    have := hw.last s (by omega)
    rw [hs] at this; simp at this

variable (f1 : Finset ι × Finset κ → ι) (f2 : Finset ι × Finset κ → κ)
  (hs1 : ∀ c : Finset ι × Finset κ, c.1.Nonempty → c.2.Nonempty → f1 c ∈ c.1)
  (hs2 : ∀ c : Finset ι × Finset κ, c.1.Nonempty → c.2.Nonempty → f2 c ∈ c.2)
include hs1 hs2

/-- On `({i}, Q)` the `P`-condition of goodness is automatic. -/
theorem good_single {i : ι} {Q : Finset κ} {n : ℕ} {w : Fin n → ι ⊕ κ} (hw : Valid {i} Q w) (hn : 2 ≤ n) :
    Good f1 f2 {i} Q (cells {i} Q w) ↔ ((((cells {i} Q w).map f2) : List κ) : Multiset κ) = Q.val := by
  unfold Good
  rw [card_singleton, Nat.sub_self, List.drop_zero, and_iff_right_iff_imp]
  intro _
  obtain ⟨c, cs, hc⟩ : ∃ c cs, cells {i} Q w = c :: cs := by
    cases h : cells {i} Q w with
    | nil => have := cells_length {i} Q w; rw [h] at this; simp at this; omega
    | cons c cs => exact ⟨c, cs, rfl⟩
  rw [hc]
  have hcm : c ∈ cells {i} Q w := by rw [hc]; exact List.mem_cons_self
  have := (labels_mem f1 f2 hs1 hs2 hw c hcm).1
  rw [mem_singleton] at this
  simp [this]

/-- **Base case.** `({i}, Q)` has exactly one good word. -/
theorem base (i : ι) : ∀ (l : ℕ) (Q : Finset κ), Q.card = l + 1 → (goods f1 f2 {i} Q (l + 2)).card = 1 := by
  intro l
  induction l with
  | zero =>
    intro Q hQ
    obtain ⟨q, rfl⟩ := card_eq_one.1 hQ
    let w0 : Fin 2 → ι ⊕ κ := fun s => if s.val = 0 then Sum.inr q else Sum.inl i
    have hw0 : Valid {i} {q} w0 := by
      refine ⟨fun a b h => ?_, fun s => ?_, fun s hs => ?_, fun s hs => ?_⟩
      · simp only [w0] at h; ext; split_ifs at h with h1 h2 h2 <;> simp_all <;> omega
      · simp only [w0]; split_ifs <;> simp
      · have : s = 0 := Fin.ext hs
        simp [w0, this]
      · have : s = 1 := Fin.ext (by simp; omega)
        simp [w0, this]
    rw [card_eq_one]
    refine ⟨w0, ?_⟩
    ext w
    simp only [goods, words, mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro ⟨hw, -⟩
      funext s
      obtain ⟨b, hb, hwb⟩ := right_of_isRight (hw.mem ⟨0, by omega⟩) (hw.first _ rfl)
      obtain ⟨a, ha, hwa⟩ := left_of_isLeft (hw.mem ⟨1, by omega⟩) (hw.last _ rfl)
      rw [mem_singleton] at ha hb
      subst ha hb
      match s with
      | ⟨0, _⟩ => simpa [w0] using hwb
      | ⟨1, _⟩ => simpa [w0] using hwa
    · rintro rfl
      refine ⟨hw0, (good_single f1 f2 hs1 hs2 hw0 le_rfl).2 ?_⟩
      obtain ⟨c, hc⟩ : ∃ c, cells {i} {q} w0 = [c] := List.length_eq_one_iff.1 (by rw [cells_length])
      have hcm : c ∈ cells {i} {q} w0 := by rw [hc]; exact List.mem_singleton_self c
      have := (labels_mem f1 f2 hs1 hs2 hw0 c hcm).2
      rw [mem_singleton] at this
      simp [hc, this]
  | succ l ih =>
    intro Q hQ
    set y := f2 ({i}, Q) with hy
    have hQne : Q.Nonempty := card_pos.1 (by omega)
    have hyQ : y ∈ Q := hs2 _ (singleton_nonempty i) hQne
    suffices h : (goods f1 f2 {i} Q (l + 1 + 2)).card = (goods f1 f2 {i} (Q.erase y) (l + 2)).card by
      rw [h]; exact ih (Q.erase y) (by rw [card_erase_of_mem hyQ]; omega)
    have key : ∀ w : Fin (l + 1 + 2) → ι ⊕ κ, Valid {i} Q w → Good f1 f2 {i} Q (cells {i} Q w) →
        w ⟨l + 1, by omega⟩ = Sum.inr y ∧ Valid {i} (Q.erase y) (delL w) ∧
          Good f1 f2 {i} (Q.erase y) (cells {i} (Q.erase y) (delL w)) := by
      intro w hw hg
      -- the letter at position `l + 1` is some `q ∈ Q`
      obtain ⟨q, hqQ, hwq⟩ : ∃ q ∈ Q, w ⟨l + 1, by omega⟩ = Sum.inr q := by
        obtain ⟨a, ha, hwa⟩ := left_of_isLeft (hw.mem ⟨l + 2, by omega⟩) (hw.last _ rfl)
        rcases hz : w ⟨l + 1, by omega⟩ with a' | b
        · have := hw.mem ⟨l + 1, by omega⟩; rw [hz, inl_mem_disjSum, mem_singleton] at this
          rw [mem_singleton] at ha; subst this ha
          have : (⟨l + 1, by omega⟩ : Fin (l + 1 + 2)).val = (⟨l + 2, by omega⟩ : Fin (l + 1 + 2)).val :=
            congrArg Fin.val (hw.inj (hz.trans hwa.symm))
          simp at this
        · have := hw.mem ⟨l + 1, by omega⟩; rw [hz, inr_mem_disjSum] at this; exact ⟨b, this, rfl⟩
      have hv := valid_delL (by omega) hw hwq
      have hw' := insL_delL w hwq
      have hgood := (good_single f1 f2 hs1 hs2 hw (by omega)).1 hg
      rw [← hw', cells_insL {i} Q q _ (fun s e => by
        have := hv.mem s; rw [e, inr_mem_disjSum] at this; simp at this), hw',
        top_cell hw (by omega)] at hgood
      simp only [List.map_append, List.map_cons, List.map_nil, ← Multiset.coe_add] at hgood
      have hqy : q = y := by
        by_contra hne
        have hqm : q ∈ (((cells {i} (Q.erase q) (delL w)).map f2 : List κ) : Multiset κ) +
            ((([f2 ({i}, Q)]) : List κ) : Multiset κ) := by rw [hgood]; exact hqQ
        rcases Multiset.mem_add.1 hqm with h | h
        · obtain ⟨c, hc, hcq⟩ := List.mem_map.1 (Multiset.mem_coe.1 h)
          have := (labels_mem f1 f2 hs1 hs2 hv c hc).2
          rw [hcq] at this; simp at this
        · simp at h; exact hne h
      subst hqy
      refine ⟨hwq, hv, (good_single f1 f2 hs1 hs2 hv (by omega)).2 ?_⟩
      rw [erase_val, ← hgood, Multiset.coe_singleton, Multiset.add_comm, Multiset.singleton_add,
        Multiset.erase_cons_head]
    apply card_nbij' (fun w => delL w) (fun v => insL (Sum.inr y) v)
    · intro w hw
      simp only [coe_filter, Set.mem_setOf_eq, goods, words, mem_filter, mem_univ, true_and] at hw ⊢
      exact (key w hw.1 hw.2).2
    · intro v hv
      simp only [coe_filter, Set.mem_setOf_eq, goods, words, mem_filter, mem_univ, true_and] at hv ⊢
      obtain ⟨hv, hg⟩ := hv
      have hw := valid_insL hyQ (by omega) hv
      refine ⟨hw, (good_single f1 f2 hs1 hs2 hw (by omega)).2 ?_⟩
      have hgood := (good_single f1 f2 hs1 hs2 hv (by omega)).1 hg
      rw [cells_insL {i} Q y _ (fun s e => by
        have := hv.mem s; rw [e, inr_mem_disjSum] at this; simp at this), top_cell hw (by omega)]
      simp only [List.map_append, List.map_cons, List.map_nil, ← Multiset.coe_add, hgood, ← hy]
      rw [erase_val, Multiset.coe_singleton, Multiset.add_comm, Multiset.singleton_add,
        Multiset.cons_erase (by simpa using hyQ)]
    · intro w hw
      simp only [coe_filter, Set.mem_setOf_eq, goods, words, mem_filter, mem_univ, true_and] at hw
      exact insL_delL w (key w hw.1 hw.2).1
    · intro v _
      exact delL_insL _ v

end Base

section Main
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable (f1 : Finset ι × Finset κ → ι) (f2 : Finset ι × Finset κ → κ)
  (hs1 : ∀ c : Finset ι × Finset κ, c.1.Nonempty → c.2.Nonempty → f1 c ∈ c.1)
  (hs2 : ∀ c : Finset ι × Finset κ, c.1.Nonempty → c.2.Nonempty → f2 c ∈ c.2)
include hs1 hs2

/-- **Product Sperner lemma (parity form).** The number of good words is odd. -/
theorem odd_goods : ∀ (k : ℕ) (P : Finset ι) (Q : Finset κ) (n : ℕ), P.card = k + 1 → 1 ≤ Q.card →
    n = P.card + Q.card → ((goods f1 f2 P Q n).card : ZMod 2) = 1 := by
  intro k
  induction k with
  | zero =>
    intro P Q n hP hQ hn
    obtain ⟨i, rfl⟩ := card_eq_one.1 hP
    obtain ⟨l, hl⟩ : ∃ l, Q.card = l + 1 := ⟨Q.card - 1, by omega⟩
    have : n = l + 2 := by rw [hn, card_singleton]; omega
    subst this
    rw [base f1 f2 hs1 hs2 i l Q hl, Nat.cast_one]
  | succ k ih =>
    intro P Q n hP hQ hn
    obtain ⟨i0, hi0⟩ := card_pos.1 (show 0 < P.card by omega)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [reduce f1 f2 hs1 hs2 P Q i0 hi0 (by omega) hQ m hn]
    exact ih (P.erase i0) Q (m + 1) (by rw [card_erase_of_mem hi0]; omega) hQ
      (by rw [card_erase_of_mem hi0]; omega)

/-- **Product Sperner lemma.** Some word is good. -/
theorem exists_good (P : Finset ι) (Q : Finset κ) (hP : P.Nonempty) (hQ : Q.Nonempty) :
    ∃ w : Fin (P.card + Q.card) → ι ⊕ κ, Valid P Q w ∧ Good f1 f2 P Q (cells P Q w) := by
  have h := odd_goods f1 f2 hs1 hs2 (P.card - 1) P Q (P.card + Q.card) (by have := card_pos.2 hP; omega)
    (card_pos.2 hQ) rfl
  obtain ⟨w, hw⟩ : (goods f1 f2 P Q (P.card + Q.card)).Nonempty := by
    rw [← card_pos]; by_contra h0; rw [show (goods f1 f2 P Q (P.card + Q.card)).card = 0 by omega] at h
    exact absurd h (by decide)
  simp only [goods, words, mem_filter, mem_univ, true_and] at hw
  exact ⟨w, hw⟩

end Main

/-! ### Cells increase along a word -/

theorem pre_mono {ι κ : Type*} [Fintype ι] [Fintype κ] {n : ℕ} (w : Fin n → ι ⊕ κ) {t t' : ℕ} (h : t ≤ t') : pre w t ⊆ pre w t' := by
  intro x hx
  obtain ⟨s, hs, rfl⟩ := mem_pre.1 hx
  exact mem_pre.2 ⟨s, by omega, rfl⟩

theorem cellOf_mono {ι κ : Type*} [Fintype ι] [Fintype κ] (P : Finset ι) (Q : Finset κ) {S S' : Finset (ι ⊕ κ)} (h : S ⊆ S') :
    (cellOf P Q S').1 ⊆ (cellOf P Q S).1 ∧ (cellOf P Q S).2 ⊆ (cellOf P Q S').2 := by
  constructor
  · intro a ha; simp only [cellOf, mem_filter] at ha ⊢; exact ⟨ha.1, fun hm => ha.2 (h hm)⟩
  · intro b hb; simp only [cellOf, mem_filter] at hb ⊢; exact ⟨hb.1, h hb.2⟩

end Mordor.Sperner
