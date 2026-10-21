import Mordor.Plane

/-!
# Layer merging: Cut on `Q × C₂` from Cut on `Q`, for cuts crossing at most one layer (log §34.3z⁵)

Let `Q` be any complete lattice on which the Cut Lemma holds. A bifunction on `Q × C₂` (`C₂ = Fin 2`) gives one on
`Q` by reading the layer-`0` rows against the layer-`0` columns; where that value sits in layer `1`, it is joined with
the value at the column anchor `(⊥, 1)`. When `(⊥, 1) ∉ D` this merged bifunction is monotone, and every witness for it
yields a witness for the original one (`cut_prod_two_of_bot`). Dually when `(⊤, 0) ∈ D` (`cut_prod_two_of_top`), with
rows of layer `1`, a meet, and the row anchor `(⊤, 0)`. Equal slices are direct (`cut_prod_two_of_eq`). What remains are *thick* cuts: both layers crossed, with a nonempty gap
`{p | (p, 0) ∈ D, (p, 1) ∉ D}`.
-/

namespace Mordor.Merge
open Classical

variable {Q : Type*} [CompleteLattice Q]

private lemma fin2 (k : Fin 2) : k = 0 ∨ k = 1 := by
  rcases k with ⟨v, hv⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hv with h | h
  · left; exact Fin.ext (by simp; omega)
  · right; exact Fin.ext (by simp; omega)
private lemma zero_le' (k : Fin 2) : (0 : Fin 2) ≤ k := Fin.zero_le _
private lemma le_one' (k : Fin 2) : k ≤ 1 := Fin.le_last _
private lemma one_le_iff (k : Fin 2) : (1 : Fin 2) ≤ k ↔ k = 1 := ⟨fun h => le_antisymm (le_one' _) h, fun h => h ▸ le_rfl⟩
private lemma le_zero_iff' (k : Fin 2) : k ≤ 0 ↔ k = 0 := ⟨fun h => le_antisymm h (zero_le' _), fun h => h ▸ le_rfl⟩

/-- Cut on `Q`, for every monotone bifunction and every cut. -/
def CutHolds (Q : Type*) [CompleteLattice Q] : Prop :=
  ∀ (G : Q → Q → Q) (E : Set Q), (∀ p p' q q', p ≤ p' → q ≤ q' → G p q ≤ G p' q') →
    (∀ p q, p ≤ q → q ∈ E → p ∈ E) → ⊥ ∈ E → ⊤ ∉ E → ∃ p ∈ E, ∃ q, q ∉ E ∧ (G p q ≤ p ∨ q ≤ G p q)

theorem cut_prod_two_of_bot (hQ : CutHolds Q) {F : Q × Fin 2 → Q × Fin 2 → Q × Fin 2} {D : Set (Q × Fin 2)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (h1 : ((⊥ : Q), (1 : Fin 2)) ∉ D) : ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  have nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y := by push_neg at hno; exact hno
  apply hno
  let s1 : Q × Fin 2 := (⊥, 1)
  -- the value at the column anchor is in layer 0 and escapes its row
  have hB : ∀ p : Q, (p, (0 : Fin 2)) ∈ D → (F (p, 0) s1).2 = 0 ∧ ¬ (F (p, 0) s1).1 ≤ p := by
    intro p hp
    have h0 := nw _ hp s1 h1
    have e : (F (p, 0) s1).2 = 0 := by
      rcases fin2 (F (p, 0) s1).2 with e | e
      · exact e
      · exact absurd (Prod.mk_le_mk.2 ⟨bot_le, (one_le_iff _).2 e⟩) h0.2
    exact ⟨e, fun h => h0.1 (Prod.mk_le_mk.2 ⟨h, by rw [e]⟩)⟩
  by_cases htop0 : ((⊤ : Q), (0 : Fin 2)) ∈ D
  · exact absurd (Prod.mk_le_mk.2 ⟨le_top, by rw [(hB ⊤ htop0).1]⟩) (nw _ htop0 s1 h1).1
  let A : Q → Q → Q × Fin 2 := fun p q => F (p, 0) (q, 0)
  let G : Q → Q → Q := fun p q => if (A p q).2 = 0 then (A p q).1 else (A p q).1 ⊔ (F (p, 0) s1).1
  let E : Set Q := {p | (p, (0 : Fin 2)) ∈ D}
  have hA : ∀ p p' q q', p ≤ p' → q ≤ q' → A p q ≤ A p' q' := fun p p' q q' hp hq =>
    hF _ _ _ _ (Prod.mk_le_mk.2 ⟨hp, le_rfl⟩) (Prod.mk_le_mk.2 ⟨hq, le_rfl⟩)
  have hGm : ∀ p p' q q', p ≤ p' → q ≤ q' → G p q ≤ G p' q' := by
    intro p p' q q' hp hq
    have h := Prod.le_def.1 (hA _ _ _ _ hp hq)
    have hb : (F (p, 0) s1).1 ≤ (F (p', 0) s1).1 :=
      (Prod.le_def.1 (hF _ _ _ _ (Prod.mk_le_mk.2 ⟨hp, le_rfl⟩) le_rfl)).1
    by_cases e' : (A p' q').2 = 0
    · have e : (A p q).2 = 0 := (le_zero_iff' _).1 (e' ▸ h.2)
      simp only [G, e, e', if_true]; exact h.1
    · by_cases e : (A p q).2 = 0
      · simp only [G, e, e', if_true, if_false]; exact h.1.trans le_sup_left
      · simp only [G, e, e', if_false]; exact sup_le_sup h.1 hb
  obtain ⟨p, hp, q, hq, hw⟩ := hQ G E hGm (fun a b h hb => hD _ _ (Prod.mk_le_mk.2 ⟨h, le_rfl⟩) hb)
    (by simpa [E] using hD _ _ bot_le hbot) htop0
  have hp' : (p, (0 : Fin 2)) ∈ D := hp
  have hq0 : (q, (0 : Fin 2)) ∉ D := hq
  have hq1 : (q, (1 : Fin 2)) ∉ D := fun h => hq0 (hD _ _ (Prod.mk_le_mk.2 ⟨le_rfl, zero_le' _⟩) h)
  by_cases e : (A p q).2 = 0
  · simp only [G, e, if_true] at hw
    rcases hw with h | h
    · exact ⟨_, hp', _, hq0, Or.inl (Prod.mk_le_mk.2 ⟨h, by simp only [A] at e ⊢; rw [e]⟩)⟩
    · exact ⟨_, hp', _, hq0, Or.inr (Prod.mk_le_mk.2 ⟨h, zero_le' _⟩)⟩
  · simp only [G, e, if_false] at hw
    rcases hw with h | h
    · exact absurd (le_sup_right.trans h) (hB p hp').2
    · -- the layer-1 column above both is a witness
      have e1 : (A p q).2 = 1 := (fin2 _).resolve_left e
      have hBq : F (p, 0) (q, 0) ≤ F (p, 0) (q, 1) := hF _ _ _ _ le_rfl (Prod.mk_le_mk.2 ⟨le_rfl, zero_le' _⟩)
      have hBs : F (p, 0) s1 ≤ F (p, 0) (q, 1) := hF _ _ _ _ le_rfl (Prod.mk_le_mk.2 ⟨bot_le, le_rfl⟩)
      refine ⟨_, hp', _, hq1, Or.inr (Prod.mk_le_mk.2 ⟨h.trans (sup_le (Prod.le_def.1 hBq).1
        (Prod.le_def.1 hBs).1), ?_⟩)⟩
      have := (Prod.le_def.1 hBq).2
      simp only [A] at e1
      rw [e1] at this; exact this

theorem cut_prod_two_of_top (hQ : CutHolds Q) {F : Q × Fin 2 → Q × Fin 2 → Q × Fin 2} {D : Set (Q × Fin 2)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (htop : ⊤ ∉ D) (h0 : ((⊤ : Q), (0 : Fin 2)) ∈ D) : ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  have nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y := by push_neg at hno; exact hno
  apply hno
  let t0 : Q × Fin 2 := (⊤, 0)
  have hT : ∀ q : Q, (q, (1 : Fin 2)) ∉ D → (F t0 (q, 1)).2 = 1 ∧ ¬ q ≤ (F t0 (q, 1)).1 := by
    intro q hq
    have h' := nw _ h0 _ hq
    have e : (F t0 (q, 1)).2 = 1 := by
      rcases fin2 (F t0 (q, 1)).2 with e | e
      · exact absurd (Prod.mk_le_mk.2 ⟨le_top, by rw [e]⟩) h'.1
      · exact e
    exact ⟨e, fun h => h'.2 (Prod.mk_le_mk.2 ⟨h, by rw [e]⟩)⟩
  by_cases hbot1 : ((⊥ : Q), (1 : Fin 2)) ∉ D
  · exact absurd (Prod.mk_le_mk.2 ⟨bot_le, by rw [(hT ⊥ hbot1).1]⟩) (nw _ h0 _ hbot1).2
  push_neg at hbot1
  let C : Q → Q → Q × Fin 2 := fun p q => F (p, 1) (q, 1)
  let G : Q → Q → Q := fun p q => if (C p q).2 = 1 then (C p q).1 else (C p q).1 ⊓ (F t0 (q, 1)).1
  let E : Set Q := {p | (p, (1 : Fin 2)) ∈ D}
  have hC : ∀ p p' q q', p ≤ p' → q ≤ q' → C p q ≤ C p' q' := fun p p' q q' hp hq =>
    hF _ _ _ _ (Prod.mk_le_mk.2 ⟨hp, le_rfl⟩) (Prod.mk_le_mk.2 ⟨hq, le_rfl⟩)
  have hGm : ∀ p p' q q', p ≤ p' → q ≤ q' → G p q ≤ G p' q' := by
    intro p p' q q' hp hq
    have h := Prod.le_def.1 (hC _ _ _ _ hp hq)
    have hb : (F t0 (q, 1)).1 ≤ (F t0 (q', 1)).1 :=
      (Prod.le_def.1 (hF _ _ _ _ le_rfl (Prod.mk_le_mk.2 ⟨hq, le_rfl⟩))).1
    by_cases e : (C p q).2 = 1
    · have e' : (C p' q').2 = 1 := (one_le_iff _).1 (e ▸ h.2)
      simp only [G, e, e', if_true]; exact h.1
    · by_cases e' : (C p' q').2 = 1
      · simp only [G, e, e', if_true, if_false]; exact inf_le_left.trans h.1
      · simp only [G, e, e', if_false]; exact inf_le_inf h.1 hb
  obtain ⟨p, hp, q, hq, hw⟩ := hQ G E hGm (fun a b h hb => hD _ _ (Prod.mk_le_mk.2 ⟨h, le_rfl⟩) hb)
    hbot1 (fun h => htop (by simpa [E] using h))
  have hp1 : (p, (1 : Fin 2)) ∈ D := hp
  have hq1 : (q, (1 : Fin 2)) ∉ D := hq
  have hp0 : (p, (0 : Fin 2)) ∈ D := hD _ _ (Prod.mk_le_mk.2 ⟨le_rfl, zero_le' _⟩) hp1
  by_cases e : (C p q).2 = 1
  · simp only [G, e, if_true] at hw
    rcases hw with h | h
    · exact ⟨_, hp1, _, hq1, Or.inl (Prod.mk_le_mk.2 ⟨h, le_one' _⟩)⟩
    · exact ⟨_, hp1, _, hq1, Or.inr (Prod.mk_le_mk.2 ⟨h, by simp only [C] at e ⊢; rw [e]⟩)⟩
  · simp only [G, e, if_false] at hw
    rcases hw with h | h
    · -- the layer-0 row below both is a witness
      have e0 : (C p q).2 = 0 := (fin2 _).resolve_right e
      have hBp : F (p, 0) (q, 1) ≤ F (p, 1) (q, 1) := hF _ _ _ _ (Prod.mk_le_mk.2 ⟨le_rfl, zero_le' _⟩) le_rfl
      have hBt : F (p, 0) (q, 1) ≤ F t0 (q, 1) := hF _ _ _ _ (Prod.mk_le_mk.2 ⟨le_top, le_rfl⟩) le_rfl
      refine ⟨_, hp0, _, hq1, Or.inl (Prod.mk_le_mk.2 ⟨(le_inf (Prod.le_def.1 hBp).1
        (Prod.le_def.1 hBt).1).trans h, ?_⟩)⟩
      have := (Prod.le_def.1 hBp).2
      simp only [C] at e0
      rw [e0] at this; exact this
    · exact absurd (h.trans inf_le_right) (hT q hq1).2

/-- Equal slices (`(p, 0) ∈ D ↔ (p, 1) ∈ D`): read layer-`1` rows against layer-`0` columns. -/
theorem cut_prod_two_of_eq (hQ : CutHolds Q) {F : Q × Fin 2 → Q × Fin 2 → Q × Fin 2} {D : Set (Q × Fin 2)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (heq : ∀ p : Q, (p, (0 : Fin 2)) ∈ D ↔ (p, (1 : Fin 2)) ∈ D) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  let G : Q → Q → Q := fun p q => (F (p, 1) (q, 0)).1
  have hGm : ∀ p p' q q', p ≤ p' → q ≤ q' → G p q ≤ G p' q' := fun p p' q q' hp hq =>
    (Prod.le_def.1 (hF _ _ _ _ (Prod.mk_le_mk.2 ⟨hp, le_rfl⟩) (Prod.mk_le_mk.2 ⟨hq, le_rfl⟩))).1
  obtain ⟨p, hp, q, hq, hw⟩ := hQ G {p | (p, (0 : Fin 2)) ∈ D} hGm
    (fun a b h hb => hD _ _ (Prod.mk_le_mk.2 ⟨h, le_rfl⟩) hb) (by simpa using hD _ _ bot_le hbot)
    (fun h => htop ((heq ⊤).1 h))
  refine ⟨_, (heq p).1 hp, _, hq, hw.imp (fun h => Prod.mk_le_mk.2 ⟨h, le_one' _⟩)
    (fun h => Prod.mk_le_mk.2 ⟨h, zero_le' _⟩)⟩

end Mordor.Merge
