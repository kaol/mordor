import Mordor.RelativeCut
import Mordor.CrossCell

/-!
# Finite faithful images (round 26, §34.3z¹¹⁹)

ChatGPT brief "finite-model property and faithful quotients", Work Package A.

* `faithful_image_impossible`: no witness-free `F` admits a finite bounded poset `Q` with a monotone `G`, a down-set
  `D̄ ∋ ⊥`, `⊤ ∉ D̄`, such that every cross pair of `Q` lifts to a cross pair of `L` on which a `G`-witness gives an
  `F`-witness. (Immediate from `RelativeCut.cut_finite`; it is the whole "finite-model" implication, and it needs no
  lattice structure on `Q`.)
* `finite_cut_faithful_quotient_impossible` (the brief's A3): a surjective lattice homomorphism `π : A → Q` onto a
  finite bounded lattice, with `π ∘ F = F̄ ∘ (π × π)`, `D = π⁻¹ D̄` (saturation) and cut-separation
  `π(F a b ⊓ a) ≠ π(F a b)`, `π(F a b ⊔ b) ≠ π(F a b)` on cross pairs, cannot exist under no witness. Monotonicity of
  `F̄`, the down-set property of `D̄` and the bounds are derived, not assumed.
* `separating_family_witness` (**half-filtration**): if a finite meet-closed `T ∋ ⊥, ⊤` *separates* every cross pair
  `x ∈ T ∩ D`, `y ∈ T ∖ D` — some `s ∈ T` has `F x y ≤ s` and `y ≰ s` — then `F` has a witness. With
  `F̄ = cl_T ∘ F` (`cl_T` the closure onto `T`), the half `F̄ x y ≤ x` of a witness transfers to `L` for free; the
  separation hypothesis is exactly what the other half needs. Cross-closure (`F x y ∈ T`, as in `RelativeCut.cut_cross`)
  is the special case `s = F x y`. `separating_family_witness_dual`: the order dual (join-closed `T`, interior map,
  separators `s ≤ F x y` with `s ≰ x`).
* `omega_witness_free`, `omega_no_faithful_image`: `ω + 1` with `D = ℕ`, `F x y = x + 1` is witness-free (DCC holds,
  ACC fails), so it has no finite faithful image: the finite-separation conjecture is false without ACC, and any
  proof of it must use the chain conditions.
* `omega_two_class_congruence`: there the coarsest `D`-saturated congruence (the syntactic congruence of `D`) has two
  classes, i.e. finite index, and Q3 fails on it. Finite observational types are not the obstruction; cut-separation is.
-/

namespace Mordor.FiniteQuotient
open Finset

set_option linter.unusedSectionVars false

/-- **Finite faithful images are impossible.** -/
theorem faithful_image_impossible {α Q : Type*} [Preorder α] [Fintype Q] [PartialOrder Q] [BoundedOrder Q]
    {F : α → α → α} {D : Set α} (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (G : Q → Q → Q) (hG : ∀ a a' b b', a ≤ a' → b ≤ b' → G a b ≤ G a' b') (Dq : Set Q)
    (hDq : ∀ a b, a ≤ b → b ∈ Dq → a ∈ Dq) (hbot : ⊥ ∈ Dq) (htop : ⊤ ∉ Dq)
    (lift : ∀ u ∈ Dq, ∀ v ∉ Dq, ∃ x ∈ D, ∃ y ∉ D, (G u v ≤ u → F x y ≤ x) ∧ (v ≤ G u v → y ≤ F x y)) : False := by
  obtain ⟨u, hu, v, hv, hw⟩ := Mordor.RelativeCut.cut_finite Dq hDq htop hbot G hG
  obtain ⟨x, hx, y, hy, h1, h2⟩ := lift u hu v hv
  rcases hw with h | h
  · exact (nw x hx y hy).1 (h1 h)
  · exact (nw x hx y hy).2 (h2 h)

/-- **A finite-cut-faithful quotient is impossible** (brief A3). -/
theorem finite_cut_faithful_quotient_impossible {A Q : Type*} [Lattice A] [BoundedOrder A] [Lattice Q]
    [BoundedOrder Q] [Fintype Q] (π : LatticeHom A Q) (hπ : Function.Surjective π) {F : A → A → A}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set A} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (Fq : Q → Q → Q) (hFq : ∀ a b, π (F a b) = Fq (π a) (π b)) (Dq : Set Q)
    (hsat : ∀ a, a ∈ D ↔ π a ∈ Dq)
    (sep : ∀ a ∈ D, ∀ b ∉ D, π (F a b ⊓ a) ≠ π (F a b) ∧ π (F a b ⊔ b) ≠ π (F a b)) : False := by
  have hmono : Monotone π := OrderHomClass.mono π
  have hπbot : π ⊥ = ⊥ := by
    obtain ⟨a, ha⟩ := hπ ⊥; exact le_antisymm (ha ▸ hmono bot_le) bot_le
  have hπtop : π ⊤ = ⊤ := by
    obtain ⟨a, ha⟩ := hπ ⊤; exact le_antisymm le_top (ha ▸ hmono le_top)
  refine faithful_image_impossible (F := F) (D := D) (fun x hx y hy => ⟨fun h => ?_, fun h => ?_⟩)
    Fq ?_ Dq ?_ (hπbot ▸ (hsat ⊥).1 hbot) (fun h => htop ((hsat ⊤).2 (hπtop ▸ h))) ?_
  · exact (sep x hx y hy).1 (by rw [inf_eq_left.2 h])
  · exact (sep x hx y hy).2 (by rw [sup_eq_left.2 h])
  · intro u u' v v' hu hv
    obtain ⟨a, rfl⟩ := hπ u; obtain ⟨a', rfl⟩ := hπ u'; obtain ⟨b, rfl⟩ := hπ v; obtain ⟨b', rfl⟩ := hπ v'
    have e1 : π (a ⊓ a') = π a := by rw [map_inf, inf_eq_left.2 hu]
    have e2 : π (b ⊓ b') = π b := by rw [map_inf, inf_eq_left.2 hv]
    rw [← e1, ← e2, ← hFq, ← hFq]
    exact hmono (hF _ _ _ _ inf_le_right inf_le_right)
  · intro u v huv hv
    obtain ⟨a, rfl⟩ := hπ u; obtain ⟨b, rfl⟩ := hπ v
    have e : π (a ⊓ b) = π a := by rw [map_inf, inf_eq_left.2 huv]
    rw [← e]; exact (hsat _).1 (hD _ _ inf_le_right ((hsat b).2 hv))
  · intro u hu v hv
    obtain ⟨a, rfl⟩ := hπ u; obtain ⟨b, rfl⟩ := hπ v
    refine ⟨a, (hsat a).2 hu, b, fun h => hv ((hsat b).1 h), fun h => ?_, fun h => ?_⟩
    · rw [← hFq] at h
      exact absurd (by rw [map_inf, inf_eq_left.2 h]) (sep a ((hsat a).2 hu) b (fun h' => hv ((hsat b).1 h'))).1
    · rw [← hFq] at h
      exact absurd (by rw [map_sup, sup_eq_left.2 h]) (sep a ((hsat a).2 hu) b (fun h' => hv ((hsat b).1 h'))).2

section Filtration

variable {α : Type*} [Lattice α] [BoundedOrder α] [DecidableEq α] [DecidableLE α]

theorem inf_mem_of_closed {T : Finset α} (htT : ⊤ ∈ T) (hcl : ∀ a ∈ T, ∀ b ∈ T, a ⊓ b ∈ T) :
    ∀ U : Finset α, U ⊆ T → U.inf id ∈ T := by
  intro U
  induction U using Finset.induction_on with
  | empty => intro _; simpa using htT
  | insert a U ha ih =>
    intro hU
    rw [Finset.inf_insert]
    exact hcl _ (hU (Finset.mem_insert_self a U)) _ (ih ((Finset.subset_insert a U).trans hU))

/-- The closure onto `T`: the meet of the members of `T` above `z`. -/
def cl (T : Finset α) (z : α) : α := (T.filter (z ≤ ·)).inf id

theorem le_cl (T : Finset α) (z : α) : z ≤ cl T z := Finset.le_inf fun _ hs => (Finset.mem_filter.1 hs).2

theorem cl_le {T : Finset α} {z s : α} (hs : s ∈ T) (hzs : z ≤ s) : cl T z ≤ s :=
  Finset.inf_le (Finset.mem_filter.2 ⟨hs, hzs⟩)

theorem cl_mono (T : Finset α) {z z' : α} (h : z ≤ z') : cl T z ≤ cl T z' :=
  Finset.le_inf fun _ hs => cl_le (Finset.mem_filter.1 hs).1 (h.trans (Finset.mem_filter.1 hs).2)

/-- **Half-filtration.** A finite meet-closed family that separates every cross pair forces a witness. -/
theorem separating_family_witness {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {T : Finset α} (hbT : ⊥ ∈ T) (htT : ⊤ ∈ T)
    (hcl : ∀ a ∈ T, ∀ b ∈ T, a ⊓ b ∈ T)
    (hsep : ∀ x ∈ T, x ∈ D → ∀ y ∈ T, y ∉ D → ∃ s ∈ T, F x y ≤ s ∧ ¬ y ≤ s) : False := by
  let Q := {x : α // x ∈ T}
  letI : OrderBot Q := Subtype.orderBot (p := (· ∈ T)) hbT
  letI : OrderTop Q := Subtype.orderTop (p := (· ∈ T)) htT
  letI : BoundedOrder Q := { }
  have hmem : ∀ z, cl T z ∈ T := fun z => inf_mem_of_closed htT hcl _ (Finset.filter_subset _ _)
  let G : Q → Q → Q := fun a b => ⟨cl T (F a.1 b.1), hmem _⟩
  refine faithful_image_impossible (α := α) (F := F) (D := D) nw G
    (fun a a' b b' ha hb => cl_mono T (hF _ _ _ _ ha hb)) {a : Q | a.1 ∈ D}
    (fun a b hab hb => hD _ _ hab hb) hbot htop ?_
  intro u hu v hv
  refine ⟨u.1, hu, v.1, hv, fun h => (le_cl T _).trans h, fun h => ?_⟩
  obtain ⟨s, hs, hFs, hvs⟩ := hsep u.1 u.2 hu v.1 v.2 hv
  exact absurd ((show v.1 ≤ cl T (F u.1 v.1) from h).trans (cl_le hs hFs)) hvs

theorem sup_mem_of_closed {T : Finset α} (hbT : ⊥ ∈ T) (hcl : ∀ a ∈ T, ∀ b ∈ T, a ⊔ b ∈ T) :
    ∀ U : Finset α, U ⊆ T → U.sup id ∈ T := by
  intro U
  induction U using Finset.induction_on with
  | empty => intro _; simpa using hbT
  | insert a U ha ih =>
    intro hU
    rw [Finset.sup_insert]
    exact hcl _ (hU (Finset.mem_insert_self a U)) _ (ih ((Finset.subset_insert a U).trans hU))

/-- The interior onto `T`: the join of the members of `T` below `z`. -/
def int (T : Finset α) (z : α) : α := (T.filter (· ≤ z)).sup id

theorem int_le (T : Finset α) (z : α) : int T z ≤ z := Finset.sup_le fun _ hs => (Finset.mem_filter.1 hs).2

theorem le_int {T : Finset α} {z s : α} (hs : s ∈ T) (hsz : s ≤ z) : s ≤ int T z :=
  Finset.le_sup (f := id) (Finset.mem_filter.2 ⟨hs, hsz⟩)

theorem int_mono (T : Finset α) {z z' : α} (h : z ≤ z') : int T z ≤ int T z' :=
  Finset.sup_le fun _ hs => le_int (Finset.mem_filter.1 hs).1 ((Finset.mem_filter.1 hs).2.trans h)

/-- **Dual half-filtration.** A finite join-closed family `T ∋ ⊥, ⊤` with, for every cross pair, some `s ∈ T`
with `s ≤ F x y` and `s ≰ x`, forces a witness (`F̄ = int_T ∘ F`; now the half `y ≤ F̄ x y` transfers for free). -/
theorem separating_family_witness_dual {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D)
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {T : Finset α} (hbT : ⊥ ∈ T) (htT : ⊤ ∈ T)
    (hcl : ∀ a ∈ T, ∀ b ∈ T, a ⊔ b ∈ T)
    (hsep : ∀ x ∈ T, x ∈ D → ∀ y ∈ T, y ∉ D → ∃ s ∈ T, s ≤ F x y ∧ ¬ s ≤ x) : False := by
  let Q := {x : α // x ∈ T}
  letI : OrderBot Q := Subtype.orderBot (p := (· ∈ T)) hbT
  letI : OrderTop Q := Subtype.orderTop (p := (· ∈ T)) htT
  letI : BoundedOrder Q := { }
  have hmem : ∀ z, int T z ∈ T := fun z => sup_mem_of_closed hbT hcl _ (Finset.filter_subset _ _)
  let G : Q → Q → Q := fun a b => ⟨int T (F a.1 b.1), hmem _⟩
  refine faithful_image_impossible (α := α) (F := F) (D := D) nw G
    (fun a a' b b' ha hb => int_mono T (hF _ _ _ _ ha hb)) {a : Q | a.1 ∈ D}
    (fun a b hab hb => hD _ _ hab hb) hbot htop ?_
  intro u hu v hv
  refine ⟨u.1, hu, v.1, hv, fun h => ?_, fun h => (show v.1 ≤ int T (F u.1 v.1) from h).trans (int_le T _)⟩
  obtain ⟨s, hs, hsF, hsu⟩ := hsep u.1 u.2 hu v.1 v.2 hv
  exact absurd ((le_int hs hsF).trans (show int T (F u.1 v.1) ≤ u.1 from h)) hsu

end Filtration

section Omega

/-- **Witness-free without ACC.** On `ω + 1 = WithTop ℕ`, `D = ℕ` and `F x y = x + 1` is monotone and has no witness. -/
theorem omega_witness_free :
    ∀ x ∈ {z : WithTop ℕ | z ≠ ⊤}, ∀ y ∉ {z : WithTop ℕ | z ≠ ⊤}, ¬ x + 1 ≤ x ∧ ¬ y ≤ x + 1 := by
  intro x hx y hy
  simp only [Set.mem_setOf_eq, not_not] at hx hy
  subst hy
  obtain ⟨n, rfl⟩ := WithTop.ne_top_iff_exists.1 hx
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact lt_irrefl _ (lt_of_lt_of_le (WithTop.coe_lt_coe.2 (Nat.lt_succ_self n)) h)
  · exact WithTop.coe_ne_top (a := n + 1) (top_le_iff.1 h)

/-- **Minimal obstruction to the finite-separation conjecture without chain conditions.** The witness-free structure
of `omega_witness_free` has no finite faithful image (in particular no finite-cut-faithful congruence): a proof of
the finite-separation conjecture must use ACC. -/
theorem omega_no_faithful_image {Q : Type*} [Fintype Q] [PartialOrder Q] [BoundedOrder Q] (G : Q → Q → Q)
    (hG : ∀ a a' b b', a ≤ a' → b ≤ b' → G a b ≤ G a' b') (Dq : Set Q) (hDq : ∀ a b, a ≤ b → b ∈ Dq → a ∈ Dq)
    (hbot : ⊥ ∈ Dq) (htop : ⊤ ∉ Dq)
    (lift : ∀ u ∈ Dq, ∀ v ∉ Dq, ∃ x ∈ {z : WithTop ℕ | z ≠ ⊤}, ∃ y ∉ {z : WithTop ℕ | z ≠ ⊤},
      (G u v ≤ u → x + 1 ≤ x) ∧ (v ≤ G u v → y ≤ x + 1)) : False :=
  faithful_image_impossible (F := fun x (_ : WithTop ℕ) => x + 1) omega_witness_free G hG Dq hDq hbot htop lift

theorem omega_sup_eq_top {a b : WithTop ℕ} : a ⊔ b = ⊤ ↔ a = ⊤ ∨ b = ⊤ := by
  rcases le_total a b with h | h
  · rw [sup_eq_right.2 h]
    exact ⟨Or.inr, fun h' => h'.elim (fun ha => top_le_iff.1 (ha ▸ h)) id⟩
  · rw [sup_eq_left.2 h]
    exact ⟨Or.inl, fun h' => h'.elim id (fun hb => top_le_iff.1 (hb ▸ h))⟩

/-- **Finite index is not the obstruction.** On `ω + 1` with `F x y = x + 1`, "both finite or both `⊤`" (the relation
`a = ⊤ ↔ b = ⊤`) is a congruence for `⊓`, `⊔`, `F`; it saturates `D = ℕ` by definition, has two classes (so it is the
coarsest `D`-saturated congruence), and Q3 fails on it: `F n ⊤ ⊓ n = n` is congruent to `F n ⊤ = n + 1`. -/
theorem omega_two_class_congruence :
    (∀ a a' b b' : WithTop ℕ, (a = ⊤ ↔ a' = ⊤) → (b = ⊤ ↔ b' = ⊤) →
      (a ⊓ b = ⊤ ↔ a' ⊓ b' = ⊤) ∧ (a ⊔ b = ⊤ ↔ a' ⊔ b' = ⊤) ∧ (a + 1 = ⊤ ↔ a' + 1 = ⊤)) ∧
    ∀ n : ℕ, (((n : WithTop ℕ) + 1) ⊓ (n : WithTop ℕ) = ⊤ ↔ (n : WithTop ℕ) + 1 = ⊤) := by
  refine ⟨fun a a' b b' ha hb => ⟨?_, ?_, ?_⟩, fun n => ?_⟩
  · rw [inf_eq_top_iff, inf_eq_top_iff, ha, hb]
  · rw [omega_sup_eq_top, omega_sup_eq_top, ha, hb]
  · rw [WithTop.add_eq_top, WithTop.add_eq_top, ha]
  · constructor <;> intro h
    · exact absurd (inf_eq_top_iff.1 h).2 (WithTop.coe_ne_top (a := n))
    · exact absurd h (WithTop.coe_ne_top (a := n + 1))

end Omega

end Mordor.FiniteQuotient
