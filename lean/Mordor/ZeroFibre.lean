import Mordor.Stable

/-!
# The stable zero-fibre program in normal form (round 26, §34.3z⁶²)

Response to an outside brief proposing to exclude the normal-form counterexample through the derived maps alone:
`Z = {y | b y = ⊥}`, `b⁻¹ Z = Z`, `a = ⊥` on `Z`, a minimal non-`Z` point `c` with `b c ≤ c`, and its Kleene
"first exit".

* `exists_min_b_closed`: the brief's preliminary lemma, in general. Under DCC, if `Z` is `b⁻¹`-closed and `⊤ ∉ Z`,
  then a minimal `c ∉ Z` with `b c ≤ c` is a fixed point of `b`.
* `normalize_out`, `normalize_b_out`, `normalize_a_out`: **in normal form the derived maps are indicators.** For
  `G = normalize F (R F)`, `b G = a G = ⊥` on `R F` and `= ⊤` off it.
* `normal_form_S`: hence `{x | x ∉ R ∧ b G x ≤ x} = {⊤}`. The minimal point is `c = ⊤`, and the first-exit
  configuration (`F (x, c) = c`, `b x ≰ x`, `b x ≤ c`, `b x ∉ Z`) holds for *every* `x ∉ R`. It carries no information.
* `normal_conj_iff`: the conjoint step in normal form: for `p ∈ R` (and `R ≠ L`), `b G q ≤ p ↔ q ∈ R`. So the
  "conjoint fork" is join-closure of `R` verbatim.
* `joinClosed_iff_directed`, `principal_of_directed`: the filteredness reading. For down-sets, join-closed iff
  directed; under ACC a nonempty directed down-set is principal.
-/

namespace Mordor
variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

/-- **The minimal `b`-closed point outside a `b⁻¹`-closed set is a `b`-fixed point** (DCC). -/
theorem exists_min_b_closed [WellFoundedLT α] {Z : Set α} (hZ : ∀ y, b F y ∈ Z → y ∈ Z) (htop : (⊤ : α) ∉ Z) :
    ∃ c, c ∉ Z ∧ b F c = c ∧ ∀ x, x ∉ Z → b F x ≤ x → ¬ x < c := by
  obtain ⟨c, ⟨hcZ, hbc⟩, hmin⟩ :=
    (wellFounded_lt (α := α)).has_min {x | x ∉ Z ∧ b F x ≤ x} ⟨⊤, htop, le_top⟩
  have hbZ : b F c ∉ Z := fun h => hcZ (hZ c h)
  have hmem : b F c ∈ {x | x ∉ Z ∧ b F x ≤ x} := ⟨hbZ, (b F).monotone hbc⟩
  exact ⟨c, hcZ, eq_of_le_of_not_lt hbc (hmin _ hmem), fun x hx hbx hxc => hmin x ⟨hx, hbx⟩ hxc⟩

open Classical in
theorem normalize_out {D : Set α} (hD : IsDown D) {x : α} (hx : x ∉ D) (y : α) :
    normalize F D hD x y = ⊤ := by
  show (if x ∈ D then (if y ∈ D then ⊥ else F x y) else ⊤) = ⊤; rw [if_neg hx]

/-- In normal form `b` is `⊤` off `R(F)`. -/
theorem normalize_b_out {y : α} (hy : y ∉ R F) : b (normalize F (R F) R_closed.1) y = ⊤ := by
  set G := normalize F (R F) R_closed.1
  have hRG : R G = R F := (R_normalize (F := F)).1
  have hb : b G y ∉ R F := fun h => hy (hRG ▸ (R_closed (F := G)).2.2.2 y (hRG ▸ h))
  have h1 : G (b G y) y = b G y := col_b y
  rw [normalize_out _ hb] at h1
  exact h1.symm

/-- In normal form `a` is `⊤` off `R(F)`. -/
theorem normalize_a_out {x : α} (hx : x ∉ R F) : a (normalize F (R F) R_closed.1) x = ⊤ := by
  have h1 : normalize F (R F) R_closed.1 x (a (normalize F (R F) R_closed.1) x) =
      a (normalize F (R F) R_closed.1) x := row_a x
  rw [normalize_out _ hx] at h1
  exact h1.symm

/-- In normal form `b` is `⊥` on `R(F)`. -/
theorem normalize_b_in {y : α} (hy : y ∈ R F) : b (normalize F (R F) R_closed.1) y = ⊥ := by
  have h := (R_normalize (F := F)).2
  have : y ∈ {y | b (normalize F (R F) R_closed.1) y ≤ ⊥} := h ▸ hy
  exact le_bot_iff.1 this

/-- **The brief's set `S` is `{⊤}` in normal form.** -/
theorem normal_form_S :
    {x | x ∉ R F ∧ b (normalize F (R F) R_closed.1) x ≤ x} = {x | x ∉ R F ∧ x = ⊤} := by
  ext x
  constructor
  · rintro ⟨hx, hb⟩; rw [normalize_b_out hx] at hb; exact ⟨hx, top_le_iff.1 hb⟩
  · rintro ⟨hx, rfl⟩; exact ⟨hx, le_top⟩

/-- **The conjoint step in normal form**: from `p ∈ R(F)`, the step `b q ≤ p` reaches exactly `R(F)`. -/
theorem normal_conj_iff (htop : (⊤ : α) ∉ R F) {p q : α} (hp : p ∈ R F) :
    b (normalize F (R F) R_closed.1) q ≤ p ↔ q ∈ R F := by
  constructor
  · intro h; by_contra hq
    rw [normalize_b_out hq] at h
    exact htop (top_le_iff.1 h ▸ hp)
  · intro hq; rw [normalize_b_in hq]; exact bot_le

/-- For down-sets, join-closed iff directed. -/
theorem joinClosed_iff_directed {D : Set α} (hD : IsDown D) :
    (∀ x ∈ D, ∀ y ∈ D, x ⊔ y ∈ D) ↔ DirectedOn (· ≤ ·) D :=
  ⟨fun h x hx y hy => ⟨x ⊔ y, h x hx y hy, le_sup_left, le_sup_right⟩,
   fun h x hx y hy => by obtain ⟨z, hz, hxz, hyz⟩ := h x hx y hy; exact hD (sup_le hxz hyz) hz⟩

/-- Under ACC a nonempty directed down-set is principal (its category of elements has a terminal object). -/
theorem principal_of_directed [WellFoundedGT α] {D : Set α} (hD : IsDown D) (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) : ∃ r, D = Set.Iic r := by
  obtain ⟨r, hr, hmax⟩ := (wellFounded_gt (α := α)).has_min D hne
  refine ⟨r, Set.Subset.antisymm (fun x hx => ?_) (fun x hx => hD hx hr)⟩
  obtain ⟨z, hz, hxz, hrz⟩ := hdir x hx r hr
  have : z = r := by
    by_contra hne; exact hmax z hz (lt_of_le_of_ne hrz (Ne.symm hne))
  exact this ▸ hxz

end Mordor
