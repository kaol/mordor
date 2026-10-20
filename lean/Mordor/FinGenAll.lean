import Mordor.Sperner
import Mordor.FinGenWidth

/-!
# The Cut Lemma for every finitely generated cut, and CL on every finite lattice (log §34.3n)

A counterexample `Cx F D p u` on a `k × l`-generated cut labels each cell `(A, B)` with a generator `i ∈ A` such
that `z(A, B) = F (⋀ p_A) (⋁ u_B) ≰ p i` and a generator `j ∈ B` with `u j ≰ z(A, B)` (no witness at the cell).
These are Sperner labellings, so `Sperner.exists_good` gives a maximal chain whose first `k` cells carry every
`i` and whose last `l` cells carry every `j`. Cells grow along the chain, so its `k`-th cell `c*` has
`z(c*) ≰ p i` for all `i` and `u j ≰ z(c*)` for all `j`: `z(c*)` is in neither `D` nor its complement.

No chain condition, no width bound, no SAT certificate: the axioms are the standard three.
-/

namespace Mordor.FinGen
open Finset Classical

variable {α : Type*} [Lattice α] [BoundedOrder α] {k l : ℕ}

/-- **The labelling lemma, for all `k, l ≥ 1`.** A finitely generated cut of a bounded lattice has a witness. -/
theorem lab {F : α → α → α} {D : Set α} {p : Fin k → α} {u : Fin l → α} (hk : 0 < k) (hl : 0 < l)
    (H : Cx F D p u) : False := by
  let z : Finset (Fin k) × Finset (Fin l) → α := fun c => F (c.1.inf p) (c.2.sup u)
  let f1 : Finset (Fin k) × Finset (Fin l) → Fin k := fun c =>
    if h : ∃ i ∈ c.1, ¬ z c ≤ p i then h.choose else ⟨0, hk⟩
  let f2 : Finset (Fin k) × Finset (Fin l) → Fin l := fun c =>
    if h : ∃ j ∈ c.2, ¬ u j ≤ z c then h.choose else ⟨0, hl⟩
  have e1 : ∀ c : Finset (Fin k) × Finset (Fin l), c.1.Nonempty → c.2.Nonempty →
      f1 c ∈ c.1 ∧ ¬ z c ≤ p (f1 c) := by
    intro c hA hB
    have h : ∃ i ∈ c.1, ¬ z c ≤ p i := by
      by_contra hn; push_neg at hn; exact nwD H hA hB hn
    simp only [f1, dif_pos h]; exact h.choose_spec
  have e2 : ∀ c : Finset (Fin k) × Finset (Fin l), c.1.Nonempty → c.2.Nonempty →
      f2 c ∈ c.2 ∧ ¬ u (f2 c) ≤ z c := by
    intro c hA hB
    have h : ∃ j ∈ c.2, ¬ u j ≤ z c := by
      by_contra hn; push_neg at hn; exact nwU H hA hB hn
    simp only [f2, dif_pos h]; exact h.choose_spec
  obtain ⟨w, hw, hg⟩ := Sperner.exists_good f1 f2 (fun c hA hB => (e1 c hA hB).1)
    (fun c hA hB => (e2 c hA hB).1) (univ : Finset (Fin k)) (univ : Finset (Fin l))
    ⟨⟨0, hk⟩, mem_univ _⟩ ⟨⟨0, hl⟩, mem_univ _⟩
  have hn : k + l = (univ : Finset (Fin k)).card + (univ : Finset (Fin l)).card := by simp
  set cs := Sperner.cells (univ : Finset (Fin k)) (univ : Finset (Fin l)) w with hcs
  set cstar := Sperner.cellOf (univ : Finset (Fin k)) (univ : Finset (Fin l)) (Sperner.pre w (k - 1))
  have hlen : cs.length = (univ : Finset (Fin k)).card + (univ : Finset (Fin l)).card - 1 :=
    Sperner.cells_length _ _ _
  rw [card_univ, card_univ, Fintype.card_fin, Fintype.card_fin] at hlen
  -- the cell at index `t` and its comparison with the pivot
  have hcell : ∀ t (ht : t < cs.length), Sperner.cellOf univ univ (Sperner.pre w t) = cs[t] := fun t ht =>
    (Sperner.cells_getElem _ _ _ t ht).symm
  have zmono : ∀ t t', t ≤ t' → z (Sperner.cellOf univ univ (Sperner.pre w t)) ≤
      z (Sperner.cellOf univ univ (Sperner.pre w t')) := by
    intro t t' htt
    obtain ⟨h1, h2⟩ := Sperner.cellOf_mono (univ : Finset (Fin k)) (univ : Finset (Fin l))
      (Sperner.pre_mono w htt)
    exact H.mono _ _ _ _ (Finset.inf_mono h1) (Finset.sup_mono h2)
  have hA : ∀ i, ¬ z cstar ≤ p i := by
    intro i hi
    have him : i ∈ (((cs.take (univ : Finset (Fin k)).card).map f1 : List (Fin k)) : Multiset (Fin k)) := by
      rw [hg.1]; exact mem_univ i
    obtain ⟨c, hc, hci⟩ := List.mem_map.1 (Multiset.mem_coe.1 him)
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.1 hc
    rw [List.length_take, card_univ, Fintype.card_fin] at ht
    rw [List.getElem_take, ← hcell t (by omega)] at hci
    obtain ⟨-, hA1, -, hB1⟩ := Sperner.cell_props hw (show t + 1 < (univ : Finset (Fin k)).card +
      (univ : Finset (Fin l)).card by simp; omega)
    have := (e1 _ hA1 hB1).2
    rw [hci] at this
    exact this ((zmono t (k - 1) (by omega)).trans hi)
  have hB : ∀ j, ¬ u j ≤ z cstar := by
    intro j hj
    have hjm : j ∈ (((cs.drop ((univ : Finset (Fin k)).card - 1)).map f2 : List (Fin l)) :
        Multiset (Fin l)) := by
      rw [hg.2]; exact mem_univ j
    obtain ⟨c, hc, hcj⟩ := List.mem_map.1 (Multiset.mem_coe.1 hjm)
    obtain ⟨s, hs, rfl⟩ := List.mem_iff_getElem.1 hc
    have hku : (univ : Finset (Fin k)).card = k := by simp
    have hs' : (univ : Finset (Fin k)).card - 1 + s < cs.length := by
      rw [List.length_drop] at hs; omega
    rw [List.getElem_drop, ← hcell _ hs'] at hcj
    obtain ⟨-, hA1, -, hB1⟩ := Sperner.cell_props hw
      (show (univ : Finset (Fin k)).card - 1 + s + 1 < (univ : Finset (Fin k)).card +
        (univ : Finset (Fin l)).card by omega)
    have := (e2 _ hA1 hB1).2
    rw [hcj] at this
    exact this (hj.trans (zmono (k - 1) _ (by omega)))
  by_cases hz : z cstar ∈ D
  · obtain ⟨i, hi⟩ := H.genD _ hz; exact hA i hi
  · obtain ⟨j, hj⟩ := H.genU _ hz; exact hB j hj

/-- **The Cut Lemma for finitely generated cuts.** If `D = ↓{p i}` and its complement is `↑{u j}`, some cell of
`D × Dᶜ` is a witness. No chain condition. -/
theorem cut_fingen {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) {p : Fin k → α} {u : Fin l → α}
    (hpD : ∀ i, p i ∈ D) (huD : ∀ j, u j ∉ D) (hgD : ∀ x ∈ D, ∃ i, x ≤ p i) (hgU : ∀ y, y ∉ D → ∃ j, u j ≤ y)
    (hk : 0 < k) (hl : 0 < l) : ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  exact lab hk hl ⟨hF, hD, hpD, huD, hgD, hgU, fun x hx y hy => ⟨fun h => (hno x hx y hy).1 h,
    fun h => (hno x hx y hy).2 h⟩⟩

/-- **The Cut Lemma on every finite lattice.** -/
theorem cut_finite [Finite α] (F : α → α → α) (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (D : Set α) (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  haveI := Fintype.ofFinite α
  have hw : ∀ s : Finset α, IsAntichain (· ≤ ·) (s : Set α) → s.card ≤ Fintype.card α :=
    fun s _ => Finset.card_le_univ s
  obtain ⟨k, hk0, -, p, hpD, hgD⟩ := gens hw D ⟨⊥, hbot⟩
  obtain ⟨l, hl0, -, u, huU, hgU⟩ :=
    gens (β := αᵒᵈ) (w := Fintype.card α) (fun s _ => Finset.card_le_univ s) (Dᶜ : Set α)
      ⟨OrderDual.toDual (⊤ : α), htop⟩
  exact cut_fingen hF hD hpD huU hgD hgU hk0 hl0

end Mordor.FinGen

namespace Mordor
open FinGen

variable {α : Type*} [CompleteLattice α] [Finite α]

/-- The Cut Lemma in the form of `Cut.lean`, on every finite lattice. -/
theorem cutCells_finite (F : α →o α →o α) : CutCells F := by
  intro D hD ⟨d, hd⟩ ⟨u, hu⟩
  exact cut_finite (fun x y => F x y) (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) D
    (fun x y h hy => hD h hy) (hD bot_le hd) (fun ht => hu (hD le_top ht))

/-- **Semi-CL on every finite lattice.** -/
theorem semi_finite (F : α →o α →o α) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F :=
  semi_of_cut (cutMaps_of_cells (cutCells_finite F)) hsemi

/-- **The Commutation Lemma on every finite lattice.** -/
theorem cl_finite (F : α →o α →o α) (hcomm : ∀ x, b F (a F x) = a F (b F x)) : m F = n F :=
  semi_finite F fun x => (hcomm x).le

end Mordor
