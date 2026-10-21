import Mordor.Plane

/-!
# The layer pass (log §34.3z⁵)

`Q × K`, any complete lattices. Lower every cell all of whose lower cells carry a value that can be lowered in the
layer coordinate (`z.2 ≰ x.2`) to `(⊥, z.2)`, raise every remaining cell all of whose upper cells carry a value that can
be raised (`y.2 ≰ z.2`) to `(⊤, z.2)`, keep the rest. The result is monotone and witness-free on cells, and every kept
value `z` sits in a *plane sandwich* `e ≤ z ≤ r`, `e ≤ h ≤ r`, `e.1 ≠ ⊥`, `r.1 ≠ ⊤`, around a base corner
`h = F (⊥, k) (⊤, k')` whose layers `k, k'` are layers of cell values. For `Q = L₁ × L₂` this reduces the plane
theorem relative to finitely many layers (G1) to finitely many plane-type sandwiches.
-/

namespace Mordor.KPass
open Classical

variable {Q K : Type*} [CompleteLattice Q] [CompleteLattice K]

theorem kpass {F : Q × K → Q × K → Q × K} {D : Set (Q × K)}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) :
    ∃ H : Q × K → Q × K → Q × K,
      (∀ x x' y y', x ∈ D → x' ∈ D → y ∉ D → y' ∉ D → x ≤ x' → y ≤ y' → H x y ≤ H x' y') ∧
      (∀ x ∈ D, ∀ y, y ∉ D → ¬ H x y ≤ x ∧ ¬ y ≤ H x y) ∧
      (∀ x ∈ D, ∀ y, y ∉ D → H x y = ((⊥ : Q), (F x y).2) ∨ H x y = ((⊤ : Q), (F x y).2) ∨
        (H x y = F x y ∧ ∃ x₁ y₁ x₂ y₂, x₁ ∈ D ∧ y₁ ∉ D ∧ x₂ ∈ D ∧ y₂ ∉ D ∧
          ((⊥ : Q), (F x₁ y₁).2) ∈ D ∧ ((⊤ : Q), (F x₂ y₂).2) ∉ D ∧
          ∃ e r, e ≤ F x y ∧ F x y ≤ r ∧ e ≤ F (⊥, (F x₁ y₁).2) (⊤, (F x₂ y₂).2) ∧
            F (⊥, (F x₁ y₁).2) (⊤, (F x₂ y₂).2) ≤ r ∧ e.1 ≠ ⊥ ∧ r.1 ≠ ⊤)) := by
  let Lw : Q × K → Q × K → Prop := fun x y =>
    ∀ x' y', x' ≤ x → y' ≤ y → x' ∈ D → y' ∉ D → ¬ (F x' y').2 ≤ x'.2
  let Rs : Q × K → Q × K → Prop := fun x y =>
    ∀ x' y', x ≤ x' → y ≤ y' → x' ∈ D → y' ∉ D → ¬ y'.2 ≤ (F x' y').2
  let H : Q × K → Q × K → Q × K := fun x y =>
    if Lw x y then ((⊥ : Q), (F x y).2) else if Rs x y then ((⊤ : Q), (F x y).2) else F x y
  have Lw_down : ∀ x x' y y', x ≤ x' → y ≤ y' → Lw x' y' → Lw x y :=
    fun x x' y y' hx hy h a b ha hb => h a b (ha.trans hx) (hb.trans hy)
  have Rs_up : ∀ x x' y y', x ≤ x' → y ≤ y' → Rs x y → Rs x' y' :=
    fun x x' y y' hx hy h a b ha hb => h a b (hx.trans ha) (hy.trans hb)
  have botle : ∀ z : Q × K, ((⊥ : Q), z.2) ≤ z := fun z => Prod.mk_le_mk.2 ⟨bot_le, le_rfl⟩
  have letop : ∀ z : Q × K, z ≤ ((⊤ : Q), z.2) := fun z => Prod.mk_le_mk.2 ⟨le_top, le_rfl⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x x' y y' hx hx' hy hy' hxx hyy
    have hzz := hF _ _ _ _ hxx hyy
    have h2 := (Prod.le_def.1 hzz).2
    by_cases l2 : Lw x' y'
    · have l1 := Lw_down _ _ _ _ hxx hyy l2
      simp only [H, l1, l2, if_true]; exact Prod.mk_le_mk.2 ⟨le_rfl, h2⟩
    · by_cases l1 : Lw x y
      · simp only [H, l1, l2, if_true, if_false]
        split_ifs
        · exact Prod.mk_le_mk.2 ⟨bot_le, h2⟩
        · exact (Prod.mk_le_mk.2 ⟨bot_le, h2⟩ : ((⊥ : Q), (F x y).2) ≤ ((⊥ : Q), (F x' y').2)).trans (botle _)
      · by_cases r1 : Rs x y
        · have r2 := Rs_up _ _ _ _ hxx hyy r1
          simp only [H, l1, l2, r1, r2, if_true, if_false]; exact Prod.mk_le_mk.2 ⟨le_rfl, h2⟩
        · simp only [H, l1, l2, r1, if_false]
          split_ifs
          · exact hzz.trans (letop _)
          · exact hzz
  · intro x hx y hy
    have h0 := nw x hx y hy
    by_cases l : Lw x y
    · simp only [H, l, if_true]
      exact ⟨fun h => l x y le_rfl le_rfl hx hy (Prod.le_def.1 h).2, fun h => h0.2 (h.trans (botle _))⟩
    · by_cases r : Rs x y
      · simp only [H, l, r, if_true, if_false]
        exact ⟨fun h => h0.1 ((letop _).trans h), fun h => r x y le_rfl le_rfl hx hy (Prod.le_def.1 h).2⟩
      · simp only [H, l, r, if_false]; exact h0
  · intro x hx y hy
    by_cases l : Lw x y
    · left; simp only [H, l, if_true]
    · by_cases r : Rs x y
      · right; left; simp only [H, l, r, if_true, if_false]
      · right; right
        refine ⟨by simp only [H, l, r, if_false], ?_⟩
        simp only [Lw, Rs, not_forall, not_not] at l r
        obtain ⟨x₁, y₁, hx₁, hy₁, hx₁D, hy₁D, hk₁⟩ := l
        obtain ⟨x₂, y₂, hx₂, hy₂, hx₂D, hy₂D, hk₂⟩ := r
        set k := (F x₁ y₁).2
        set k' := (F x₂ y₂).2
        have hs : ((⊥ : Q), k) ≤ x₁ := Prod.mk_le_mk.2 ⟨bot_le, hk₁⟩
        have ht : y₂ ≤ ((⊤ : Q), k') := Prod.mk_le_mk.2 ⟨le_top, hk₂⟩
        have hsD : ((⊥ : Q), k) ∈ D := hD _ _ hs hx₁D
        have htD : ((⊤ : Q), k') ∉ D := fun h => hy₂D (hD _ _ ht h)
        refine ⟨x₁, y₁, x₂, y₂, hx₁D, hy₁D, hx₂D, hy₂D, hsD, htD, F (⊥, k) y₁, F x₂ (⊤, k'), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · exact (hF _ _ _ _ hs le_rfl).trans (hF _ _ _ _ hx₁ hy₁)
        · exact (hF _ _ _ _ hx₂ hy₂).trans (hF _ _ _ _ le_rfl ht)
        · exact hF _ _ _ _ le_rfl ((hy₁.trans hy₂).trans ht)
        · exact hF _ _ _ _ ((hs.trans hx₁).trans hx₂) le_rfl
        · intro h0
          have he2 : (F (⊥, k) y₁).2 ≤ k := (Prod.le_def.1 (hF _ _ _ _ hs le_rfl)).2
          exact (nw _ hsD y₁ hy₁D).1 (Prod.mk_le_mk.2 ⟨h0.le, he2⟩)
        · intro h1
          have hr2 : k' ≤ (F x₂ (⊤, k')).2 := (Prod.le_def.1 (hF _ _ _ _ le_rfl ht)).2
          exact (nw x₂ hx₂D _ htD).2 (Prod.mk_le_mk.2 ⟨h1.ge, hr2⟩)

end Mordor.KPass
