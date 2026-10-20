import Mordor.Localize

/-!
# Finite cell values, end-finite lattices, and pinning (log §34.3r)

* `cut_of_values_in_finite`: if (under no witness) all cell values lie in a finite set, there is a witness.
* `cut_of_end_finite`: if every principal ideal `↓g` (`g ≠ ⊤`) and every principal filter `↑g` (`g ≠ ⊥`) is finite,
  the Cut Lemma holds: cell values lie below `F x ⊤ ∈ ↑F(⊥, ⊤) \ {⊤}`. This generalizes `cut_of_finite_nbhd`, since
  `↑c ∪ ↓c ⊆ N(c) ∪ {⊥, ⊤}`.
* `pin_coatom`: if `F x₀ y₀ ⊔ F ⊥ ⊤` is a coatom `t`, then `F x ⊤ = t` for every `x ∈ D` above `x₀`. With finite
  principal ideals this bounds every cell value with `x ≥ x₀`; it settles the stuck family `S∞′` of §34.3p.
-/

namespace Mordor.Pin
open Finset Classical Localize
set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {F : α → α → α} {D : Set α}
variable (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D)
include hF hD

/-- **Finite cell values ⟹ witness.** -/
theorem cut_of_values_in_finite (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (S : Set α) (hS : S.Finite)
    (hval : (∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) → ∀ x ∈ D, ∀ y, y ∉ D → F x y ∈ S) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  have hv := hval fun x hx y hy => hno x hx y hy
  refine capture_contra hF hD (insert ⊥ (hS.toFinset.filter (· ∈ D))) (insert ⊤ (hS.toFinset.filter (· ∉ D)))
    ?_ ?_ (insert_nonempty _ _) (insert_nonempty _ _) D {y | y ∉ D} ?_ ?_ ?_ ?_ ?_ ?_
  · intro p hp; rcases mem_insert.1 hp with rfl | hp; exacts [hbot, (mem_filter.1 hp).2]
  · intro u hu; rcases mem_insert.1 hu with rfl | hu; exacts [htop, (mem_filter.1 hu).2]
  · intro p hp; rcases mem_insert.1 hp with rfl | hp; exacts [hbot, (mem_filter.1 hp).2]
  · intro u hu; rcases mem_insert.1 hu with rfl | hu; exacts [htop, (mem_filter.1 hu).2]
  · exact fun a ha b _ => hD _ _ inf_le_left ha
  · exact fun a ha b _ h => ha (hD _ _ le_sup_left h)
  · intro x hx y hy _ hyD
    have hz := hv x hx y hyD
    refine ⟨fun h => ⟨_, mem_insert_of_mem (mem_filter.2 ⟨hS.mem_toFinset.2 hz, h⟩), le_rfl⟩,
      fun h => ⟨_, mem_insert_of_mem (mem_filter.2 ⟨hS.mem_toFinset.2 hz, h⟩), le_rfl⟩⟩
  · exact fun x hx y _ _ hyD => hno x hx y hyD

/-- **End-finite lattices.** Finite proper principal ideals and filters force the Cut Lemma. -/
theorem cut_of_end_finite (hI : ∀ g : α, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : α, g ≠ ⊥ → (Set.Ici g).Finite)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) : ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_cases hc : F ⊥ ⊤ = ⊥
  · exact ⟨⊥, hbot, ⊤, htop, Or.inl hc.le⟩
  by_cases hc' : F ⊥ ⊤ = ⊤
  · exact ⟨⊥, hbot, ⊤, htop, Or.inr hc'.ge⟩
  let T := Set.Ici (F ⊥ ⊤) \ {⊤}
  have hT : T.Finite := (hJ _ hc).subset Set.diff_subset
  have hS : (⋃ g ∈ T, Set.Iic g).Finite :=
    hT.biUnion fun g hg => hI g fun h => hg.2 (Set.mem_singleton_iff.2 h)
  refine cut_of_values_in_finite hF hD hbot htop _ hS fun hno x hx y hy => ?_
  refine Set.mem_biUnion (x := F x ⊤) ⟨hF _ _ _ _ bot_le le_rfl, fun h => ?_⟩ (hF _ _ _ _ le_rfl le_top)
  exact (hno x hx ⊤ htop).2 (Set.mem_singleton_iff.1 h).ge

/-- **Orbit capture** (ideal-finite lattices). If a finite `T ⊆ D`, closed under `⊓`, contains `⊥`, and every element
of `D` below some `F x ⊤` (`x ∈ T`) lies below an element of `T`, there is a witness. Cell values with `x ∈ T` lie
in the finite set `⋃ ↓F x ⊤`; the `U`-valued ones capture themselves and the `D`-valued ones are captured by `T`.
A ratchet argument (such as `pin_coatom`) must end here: the orbit `x ↦ ↓F x ⊤ ∩ D` has to close. -/
theorem cut_of_orbit_capture (htop : ⊤ ∉ D) (hI : ∀ g : α, g ≠ ⊤ → (Set.Iic g).Finite)
    (T : Finset α) (hT : ∀ x ∈ T, x ∈ D) (hT0 : ⊥ ∈ T) (hTm : ∀ a ∈ T, ∀ b ∈ T, a ⊓ b ∈ T)
    (hcl : ∀ x ∈ T, ∀ z, z ∈ D → z ≤ F x ⊤ → ∃ p ∈ T, z ≤ p) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  have hne : ∀ x ∈ D, F x ⊤ ≠ ⊤ := fun x hx h => (hno x hx ⊤ htop).2 h.ge
  have hS : (⋃ x ∈ (T : Set α), Set.Iic (F x ⊤)).Finite :=
    T.finite_toSet.biUnion fun x hx => hI _ (hne x (hT x hx))
  refine capture_contra hF hD T (insert ⊤ (hS.toFinset.filter (· ∉ D))) hT ?_ ⟨⊥, hT0⟩
    (insert_nonempty _ _) (T : Set α) {y | y ∉ D} (fun p hp => hp) ?_ (fun a ha b hb => hTm a ha b hb)
    (fun a ha b _ h => ha (hD _ _ le_sup_left h)) ?_ (fun x _ y _ hxD hyD => hno x hxD y hyD)
  · intro u hu; rcases mem_insert.1 hu with rfl | hu; exacts [htop, (mem_filter.1 hu).2]
  · intro u hu; rcases mem_insert.1 hu with rfl | hu; exacts [htop, (mem_filter.1 hu).2]
  · intro x hx y hy hxD hyD
    have hle : F x y ≤ F x ⊤ := hF _ _ _ _ le_rfl le_top
    refine ⟨fun h => hcl x hx _ h hle, fun h => ⟨F x y, mem_insert_of_mem (mem_filter.2
      ⟨hS.mem_toFinset.2 (Set.mem_biUnion (x := x) hx hle), h⟩), le_rfl⟩⟩

/-- **Pinning.** If `t = F x₀ y₀ ⊔ F ⊥ ⊤` has only `t` and `⊤` above it, every `x ∈ D` above `x₀` has
`F x ⊤ = t` (otherwise `(x, ⊤)` is a witness). -/
theorem pin_coatom (hno : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (htop : ⊤ ∉ D)
    {x₀ y₀ : α} (ht : ∀ z, F x₀ y₀ ⊔ F ⊥ ⊤ ≤ z → z = F x₀ y₀ ⊔ F ⊥ ⊤ ∨ z = ⊤)
    {x : α} (hx : x ∈ D) (hx₀ : x₀ ≤ x) : F x ⊤ = F x₀ y₀ ⊔ F ⊥ ⊤ := by
  rcases ht (F x ⊤) (sup_le (hF _ _ _ _ hx₀ le_top) (hF _ _ _ _ bot_le le_rfl)) with h | h
  · exact h
  · exact absurd h.ge (hno x hx ⊤ htop).2

/-- **The hub theorem.** Shape hypotheses (all hold in `S∞′`, §34.3r): proper principal ideals are finite; only
`⊥, d, e, c` have infinite principal filters; every element is `⊥`, `e` or above `d`; `↓e = {⊥, e}`,
`↓c ⊆ ↓d ∪ {e, c}`, `↑e ⊆ {e} ∪ ↑c`, `e ≰ d`; the elements strictly between `c` and `⊤` are coatoms, and below such a coatom
`w` every element is below `c`, equal to `w`, or has only `⊥, d` (of `⊥, d, e, c`) beneath it.
Then every cut has a witness. The proof pins `F x ⊤` for `x ≥ d` through one anchor cell `(d, y)`; when no
anchor leaves `{⊥, d, e, c}`, the cells `(d, c)`, `(e, c)` or `(c, w)`, `(d, w)` are forced into a witness. -/
theorem cut_hub (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (d e c : α)
    (hI : ∀ g : α, g ≠ ⊤ → (Set.Iic g).Finite)
    (hJ : ∀ g : α, g ≠ ⊥ → g ≠ d → g ≠ e → g ≠ c → (Set.Ici g).Finite)
    (hcov : ∀ x : α, x = ⊥ ∨ x = e ∨ d ≤ x) (hed : ¬ e ≤ d) (hdc : d ≤ c) (hec : e ≤ c)
    (he_down : ∀ z, z ≤ e → z = ⊥ ∨ z = e) (hc_down : ∀ z, z ≤ c → z ≤ d ∨ z = e ∨ z = c)
    (he_up : ∀ z, e ≤ z → z = e ∨ c ≤ z)
    (hc_up : ∀ w, c < w → w ≠ ⊤ → ∀ z, w ≤ z → z = w ∨ z = ⊤)
    (hw_down : ∀ w, c < w → w ≠ ⊤ → ∀ z, z ≤ w → z ≤ c ∨ z = w ∨
      ∀ b, b ≤ z → (b = ⊥ ∨ b = d ∨ b = e ∨ b = c) → b ≤ d) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  have nw : ∀ x ∈ D, ∀ y, y ∉ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y := fun x hx y hy => hno x hx y hy
  let B : α → Prop := fun b => b = ⊥ ∨ b = d ∨ b = e ∨ b = c
  -- values below `F x ⊤`, which is never `⊤`
  have hne : ∀ x ∈ D, F x ⊤ ≠ ⊤ := fun x hx h => (nw x hx ⊤ htop).2 h.ge
  -- Case 1: some anchor `(d, y)` leaves `B`
  by_cases hgood : ∃ y, y ∉ D ∧ d ∈ D ∧ ¬ B (F d y)
  · obtain ⟨y₀, hy₀, hdD, hB⟩ := hgood
    have hfin : (Set.Ici (F d y₀)).Finite := by
      simp only [B, not_or] at hB; exact hJ _ hB.1 hB.2.1 hB.2.2.1 hB.2.2.2
    let T : Set α := (Set.Ici (F d y₀) ∪ {F ⊥ ⊤, F e ⊤}) \ {⊤}
    have hT : T.Finite := ((hfin.union (Set.toFinite _))).subset Set.diff_subset
    obtain ⟨x, hx, y, hy, h⟩ := cut_of_values_in_finite hF hD hbot htop (⋃ g ∈ T, Set.Iic g)
      (hT.biUnion fun g hg => hI g fun h => hg.2 (Set.mem_singleton_iff.2 h)) fun _ x hx y hy => by
        refine Set.mem_biUnion (x := F x ⊤) ⟨?_, fun h => hne x hx (Set.mem_singleton_iff.1 h)⟩
          (hF _ _ _ _ le_rfl le_top)
        rcases hcov x with rfl | rfl | hdx
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · exact Or.inl (hF _ _ _ _ hdx le_top)
    exact h.elim (hno x hx y hy).1 (hno x hx y hy).2
  push_neg at hgood
  -- Case 2: `d ∈ D`, and every anchor `(d, y)` stays in `B`. (If `d ∉ D` the corner argument below
  -- needs no `d`-row; we treat `d ∉ D` first.)
  by_cases hdD : d ∈ D
  · have hrow : ∀ y, y ∉ D → B (F d y) := fun y hy => hgood y hy hdD
    -- Claim A: `c ∈ D` with `c ≤ F c ⊤` is contradictory (the cells `(c, w)`, `(d, w)` with `w = F c ⊤`)
    have claimA : c ∈ D → c ≤ F c ⊤ → False := by
      intro hcD hcw
      obtain ⟨w, hw⟩ : ∃ w, F c ⊤ = w := ⟨_, rfl⟩
      rw [hw] at hcw
      have hcw' : c < w := lt_of_le_of_ne hcw fun h => (nw c hcD ⊤ htop).1 (hw.trans h.symm).le
      have hwt : w ≠ ⊤ := hw ▸ hne c hcD
      have hwD : w ∉ D := by
        intro hwD
        have hww : w ≤ F w ⊤ := hw ▸ hF c w ⊤ ⊤ hcw'.le le_rfl
        rcases hc_up w hcw' hwt (F w ⊤) hww with h | h
        · exact (nw w hwD ⊤ htop).1 h.le
        · exact hne w hwD h
      have hv1 := nw c hcD w hwD
      rcases hw_down w hcw' hwt (F c w) (hw ▸ hF c c w ⊤ le_rfl le_top) with h | h | h
      · exact hv1.1 h
      · exact hv1.2 h.ge
      · exact (nw d hdD w hwD).1 (h _ (hF d c w w hdc le_rfl) (hrow w hwD))
    -- `F d ⊤ ∈ {e, c}`
    have h1 := (nw d hdD ⊤ htop).1
    rcases hrow ⊤ htop with h | h | h | h
    · exact h1 (h ▸ bot_le)
    · exact h1 h.le
    · -- `F d ⊤ = e`
      have hbt : F ⊥ ⊤ = e := by
        rcases he_down (F ⊥ ⊤) (h ▸ hF ⊥ d ⊤ ⊤ bot_le le_rfl) with h' | h'
        · exact absurd h'.le (nw ⊥ hbot ⊤ htop).1
        · exact h'
      have heD : e ∈ D := by
        by_contra heD
        rcases he_down (F ⊥ e) ((hF ⊥ ⊥ e ⊤ le_rfl le_top).trans hbt.le) with h' | h'
        · exact (nw ⊥ hbot e heD).1 h'.le
        · exact (nw ⊥ hbot e heD).2 h'.ge
      have hect : c ≤ F e ⊤ := by
        rcases he_up (F e ⊤) (hbt ▸ hF ⊥ e ⊤ ⊤ bot_le le_rfl) with h' | h'
        · exact absurd h'.le (nw e heD ⊤ htop).1
        · exact h'
      by_cases hcD : c ∈ D
      · exact claimA hcD (hect.trans (hF e c ⊤ ⊤ hec le_rfl))
      · have hbc : F ⊥ c = e := by
          rcases he_down (F ⊥ c) ((hF ⊥ d c ⊤ bot_le le_top).trans h.le) with h' | h'
          · exact absurd h'.le (nw ⊥ hbot c hcD).1
          · exact h'
        rcases he_up (F e c) (hbc ▸ hF ⊥ e c c bot_le le_rfl) with h' | h'
        · exact (nw e heD c hcD).1 h'.le
        · exact (nw e heD c hcD).2 h'
    · -- `F d ⊤ = c`
      by_cases hcD : c ∈ D
      · exact claimA hcD (h ▸ hF d c ⊤ ⊤ hdc le_rfl)
      · have hdc' : F d c = e := by
          rcases hc_down (F d c) (h ▸ hF d d c ⊤ le_rfl le_top) with h' | h' | h'
          · exact absurd h' (nw d hdD c hcD).1
          · exact h'
          · exact absurd h'.ge (nw d hdD c hcD).2
        have hbc : F ⊥ c = e := by
          rcases he_down (F ⊥ c) (hdc' ▸ hF ⊥ d c c bot_le le_rfl) with h' | h'
          · exact absurd h'.le (nw ⊥ hbot c hcD).1
          · exact h'
        have heD : e ∈ D := by
          by_contra heD
          rcases he_down (F ⊥ e) ((hF ⊥ ⊥ e c le_rfl hec).trans hbc.le) with h' | h'
          · exact (nw ⊥ hbot e heD).1 h'.le
          · exact (nw ⊥ hbot e heD).2 h'.ge
        rcases he_up (F e c) (hbc ▸ hF ⊥ e c c bot_le le_rfl) with h' | h'
        · exact (nw e heD c hcD).1 h'.le
        · exact (nw e heD c hcD).2 h'
  · -- `d ∉ D`: then `D ⊆ {⊥, e}`, so cell values lie below `F ⊥ ⊤` or `F e ⊤`
    let T : Set α := ({F ⊥ ⊤, F e ⊤} : Set α) \ {⊤}
    have hval : ∀ x ∈ D, ∀ y, y ∉ D → F x y ∈ ⋃ g ∈ T, Set.Iic g := by
      intro x hx y hy
      refine Set.mem_biUnion (x := F x ⊤) ⟨?_, fun h => hne x hx (Set.mem_singleton_iff.1 h)⟩
        (hF _ _ _ _ le_rfl le_top)
      rcases hcov x with rfl | rfl | hdx
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd (hD _ _ hdx hx) hdD
    obtain ⟨x, hx, y, hy, h⟩ := cut_of_values_in_finite hF hD hbot htop (⋃ g ∈ T, Set.Iic g)
      ((Set.toFinite _ |>.subset Set.diff_subset).biUnion fun g hg =>
        hI g fun h => hg.2 (Set.mem_singleton_iff.2 h)) fun _ => hval
    exact h.elim (hno x hx y hy).1 (hno x hx y hy).2

end Mordor.Pin

namespace Mordor
open Pin

/-- **Semi-CL (hence CL) on end-finite complete lattices.** -/
theorem semi_of_end_finite {α : Type*} [CompleteLattice α]
    (hI : ∀ g : α, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : α, g ≠ ⊥ → (Set.Ici g).Finite)
    (F : α →o α →o α) (hsemi : ∀ x, b F (a F x) ≤ a F (b F x)) : m F = n F := by
  refine semi_of_cut (cutMaps_of_cells fun D hD ⟨d, hd⟩ ⟨u, hu⟩ => ?_) hsemi
  exact cut_of_end_finite (F := fun x y => F x y)
    (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy)) (fun x y h hy => hD h hy) hI hJ
    (hD bot_le hd) (fun ht => hu (hD le_top ht))

end Mordor
