import Mordor.Crossing
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod

/-!
# Anchor-entry profiles and ko-transfer chains (round 26, §34.3z⁷⁷)

Response to the brief "global induction invariant via ko-threat accounting". `D = ⋃ᵢ ↓pᵢ` finite, `F` monotone,
no witness, join anchors `cᵢ = anchor p i`, anchor maps `hᵢ = F cᵢ`.

* `entry_exists_below`, `entry_col_mono`, `entry_col_le`: **profile monotonicity** in the column. For `u ≤ v` outside
  `D`, an entering orbit from `v` forces one from `u`, no later, and at equal times below it (so the label of the
  `v`-endpoint is contained in that of the `u`-endpoint).
* `entry_label_single`: **label classification**. If the `hᵢ`-endpoint lies below `pᵢ`, it lies below no other `pⱼ`.
* `entry_label_contracting`: at a `pᵢ`-contracting column (`F pᵢ s ≤ s`, e.g. `⊤`) the `hᵢ`-endpoint is not below `pᵢ`
  (`anchor_sandwich`), so its label is a nonempty subset of `ι \ {i}`.
* `no_anchor_transfer_cycle`: **no transfer cycle at one column.** At a column `u ∉ D` no nonempty set `T` of
  generators has every anchor row `F cₐ u` (`a ∈ T`) below the petal of another generator of `T`. The meet rows
  `⋀_A p` (`A ⊆ T`, `|A| ≥ 2`) lie below every `cₐ`, `a ∈ A`, so their labels form a closed row family.
* `simultaneous_entry`, `contracting_simultaneous`: hence at a column contracting for every generator (e.g. `⊤`) the
  anchor orbits cannot all enter `D` at the first step.
* `no_upward_transfer_cycle`: the same with each anchor row evaluated at any column `v ≥ u`. So the *upward transfer
  digraph* at `u` (`a → k` iff `k ≠ a` and `F cₐ v ≤ pₖ` for some `v ≥ u`) is acyclic.
* `ko_chain_injective`, `ko_chain_finite`: **ko-transfer chains visit distinct generators.** Along weakly descending
  columns `uₙ ∉ D`, a chain of transfers `F c_{iₙ} uₙ₊₁ ≤ p_{iₙ₊₁}`, `iₙ₊₁ ≠ iₙ`, never repeats a generator, so it has
  fewer than `|ι|` steps. No chain condition is used.
* `lastpoints_no_common_lower` (DCC): for a column `s` contracting for every generator (e.g. `⊤`), the last points
  `wᵢ ∉ D` of the anchor orbits of `s` have no common lower bound outside `D`. In a lattice: `⋀ᵢ wᵢ ∈ D`.
* `no_closed_meet_family`: the general closure tool. At `u ∉ D` no nonempty family of meet rows `⋀_A p` has each
  value `F (⋀_A p) u` below another member. Its bounds can come from meets of anchor values at columns above `u`.
* `sink_generator` (DCC): in a counterexample some column `u ∉ D` and generator `j` have no anchor-`j` transfer on
  the comparability cone of `u`, so no column below `u` is `pⱼ`-contracting. This is where every ko accounting stops.
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α]

section Generic
variable {h : α → α} {InD : α → Prop}

/-- An entering orbit from `v` forces an entering orbit from every `u ≤ v` outside `D`. -/
theorem entry_exists_below (hh : Monotone h) (hdown : ∀ x y, x ≤ y → InD y → InD x) {u v : α} (huv : u ≤ v)
    (hu : ¬ InD u) {n' : ℕ} (hE' : EntersAt h InD v n') : ∃ n, EntersAt h InD u n := by
  classical
  have hP : ∃ k, InD (h^[k + 1] u) := ⟨n', hdown _ _ (hh.iterate _ huv) hE'.2⟩
  refine ⟨Nat.find hP, fun k hk => ?_, Nat.find_spec hP⟩
  cases k with
  | zero => simpa using hu
  | succ j => exact Nat.find_min hP (by omega)

/-- **Profile monotonicity, entry time.** -/
theorem entry_col_mono (hh : Monotone h) (hdown : ∀ x y, x ≤ y → InD y → InD x) {u v : α} (huv : u ≤ v)
    {n n' : ℕ} (hE : EntersAt h InD u n) (hE' : EntersAt h InD v n') : n ≤ n' := by
  by_contra hlt
  exact hE.1 (n' + 1) (by omega) (hdown _ _ (hh.iterate _ huv) hE'.2)

/-- **Profile monotonicity, endpoint.** At equal entry times the endpoint from `u` is below that from `v`. -/
theorem entry_col_le (hh : Monotone h) {u v : α} (huv : u ≤ v) (n : ℕ) : h^[n + 1] u ≤ h^[n + 1] v :=
  hh.iterate _ huv

end Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem meet_le_anchor (p : ι → α) {i j : ι} (hij : j ≠ i) : p i ⊓ p j ≤ anchor p i :=
  Finset.le_sup (f := fun j => p i ⊓ p j) (Finset.mem_erase.2 ⟨hij, Finset.mem_univ j⟩)

/-- **Label classification.** An anchor endpoint below its own generator is below no other generator. -/
theorem entry_label_single {F : α → α → α} (p : ι → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (i : ι) {s : α}
    {n : ℕ} (hE : EntersAt (F (anchor p i)) (fun x => ∃ j, x ≤ p j) s n)
    (hi : (F (anchor p i))^[n + 1] s ≤ p i) : ∀ j, j ≠ i → ¬ (F (anchor p i))^[n + 1] s ≤ p j :=
  fun _ hj hle => endpoint_not_le nw ⟨i, anchor_le p i⟩ hE ((le_inf hi hle).trans (meet_le_anchor p hj))

/-- At a `pᵢ`-contracting column the `hᵢ`-endpoint is not below `pᵢ`. -/
theorem entry_label_contracting [WellFoundedLT α] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α) (i : ι)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {s : α} (hs : ¬ ∃ j, s ≤ p j) (hgs : F (p i) s ≤ s) {n : ℕ}
    (hE : EntersAt (F (anchor p i)) (fun x => ∃ j, x ≤ p j) s n) : ¬ (F (anchor p i))^[n + 1] s ≤ p i := by
  rw [Function.iterate_succ_apply']
  exact anchor_sandwich hF p i nw hs hgs n hE.1

/-- **The upward transfer digraph is acyclic.** At a column `u ∉ D`, no nonempty set `T` of generators has, for every
`a ∈ T`, a column `v ≥ u` and a `k ∈ T \ {a}` with `F cₐ v ≤ pₖ`. The meet rows `⋀_A p` (`A ⊆ T`, `|A| ≥ 2`) lie below
`cₐ` for every `a ∈ A`, so at `u` their labels form a closed row family. -/
theorem no_upward_transfer_cycle {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : ι → α) (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {u : α} (hu : ¬ ∃ i, u ≤ p i) (T : Finset ι) (hT : T.Nonempty)
    (htr : ∀ a ∈ T, ∃ k ∈ T, k ≠ a ∧ ∃ v, u ≤ v ∧ F (anchor p a) v ≤ p k) : False := by
  classical
  -- the meet of a set with two distinct members lies below the anchor of each member
  have hmeet : ∀ A : Finset ι, (∃ a ∈ A, ∃ b ∈ A, a ≠ b) → ∀ a ∈ A, A.inf p ≤ anchor p a := by
    rintro A ⟨a₀, ha₀, b₀, hb₀, hab⟩ a ha
    obtain ⟨b, hb, hba⟩ : ∃ b ∈ A, b ≠ a := by
      by_cases h : a = a₀
      · exact ⟨b₀, hb₀, fun e => hab (h ▸ e.symm ▸ rfl)⟩
      · exact ⟨a₀, ha₀, fun e => h e.symm⟩
    exact (le_inf (Finset.inf_le ha) (Finset.inf_le hb)).trans (meet_le_anchor p hba)
  let lab : Finset ι → Finset ι := fun A => T.filter (fun k => F (A.inf p) u ≤ p k)
  have key : ∀ A : Finset ι, A ⊆ T → (∃ a ∈ A, ∃ b ∈ A, a ≠ b) → lab A ⊆ A → False := by
    intro A
    induction A using Finset.strongInduction with
    | H A ih =>
      intro hAT htwo hlab
      obtain ⟨a₀, ha₀, -, -, -⟩ := id htwo
      -- every member of `A` sends its anchor row into another member of `lab A`
      have hsucc : ∀ a ∈ A, ∃ k ∈ lab A, k ≠ a := fun a ha => by
        obtain ⟨k, hkT, hka, v, huv, hk⟩ := htr a (hAT ha)
        exact ⟨k, Finset.mem_filter.2 ⟨hkT, (hF _ _ _ _ (hmeet A htwo a ha) huv).trans hk⟩, hka⟩
      obtain ⟨k₁, hk₁, -⟩ := hsucc a₀ ha₀
      obtain ⟨k₂, hk₂, hk₂₁⟩ := hsucc k₁ (hlab hk₁)
      have hne : lab A ≠ A := by
        intro heq
        have hle : F (A.inf p) u ≤ A.inf p := Finset.le_inf fun k hk => by
          rw [← heq] at hk; exact (Finset.mem_filter.1 hk).2
        exact (nw _ ⟨a₀, Finset.inf_le ha₀⟩ u hu).1 hle
      refine ih (lab A) (Finset.ssubset_iff_subset_ne.2 ⟨hlab, hne⟩) (Finset.filter_subset _ _)
        ⟨k₂, hk₂, k₁, hk₁, hk₂₁⟩ fun k hk => ?_
      obtain ⟨hkT, hkle⟩ := Finset.mem_filter.1 hk
      exact Finset.mem_filter.2 ⟨hkT, (hF _ _ _ _ (Finset.inf_mono hlab) le_rfl).trans hkle⟩
  obtain ⟨a, ha⟩ := hT
  obtain ⟨k, hk, hka, -⟩ := htr a ha
  exact key T (Finset.Subset.refl T) ⟨k, hk, a, ha, hka⟩ (Finset.filter_subset _ _)

/-- **No anchor-transfer cycle at one column** (`v = u`). -/
theorem no_anchor_transfer_cycle {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : ι → α) (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {u : α} (hu : ¬ ∃ i, u ≤ p i) (T : Finset ι) (hT : T.Nonempty)
    (htr : ∀ a ∈ T, ∃ k ∈ T, k ≠ a ∧ F (anchor p a) u ≤ p k) : False :=
  no_upward_transfer_cycle hF p nw hu T hT fun a ha => by
    obtain ⟨k, hk, hka, h⟩ := htr a ha; exact ⟨k, hk, hka, u, le_rfl, h⟩

/-- **Simultaneous entry is impossible**: not every anchor row can take `u` into `D` away from its own petal. -/
theorem simultaneous_entry [Nonempty ι] {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : ι → α) (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {u : α} (hu : ¬ ∃ i, u ≤ p i) (hin : ∀ i, ∃ j, F (anchor p i) u ≤ p j)
    (hout : ∀ i, ¬ F (anchor p i) u ≤ p i) : False := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine no_anchor_transfer_cycle hF p nw hu Finset.univ ⟨i₀, Finset.mem_univ _⟩ fun a _ => ?_
  obtain ⟨k, hk⟩ := hin a
  exact ⟨k, Finset.mem_univ _, fun e => hout a (e ▸ hk), hk⟩

/-- At a column contracting for every generator (e.g. `⊤`), some anchor row stays outside `D`. -/
theorem contracting_simultaneous [WellFoundedLT α] [Nonempty ι] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {u : α} (hu : ¬ ∃ i, u ≤ p i) (hgu : ∀ i, F (p i) u ≤ u) : ∃ i, ¬ ∃ j, F (anchor p i) u ≤ p j := by
  by_contra hall
  push_neg at hall
  exact simultaneous_entry hF p nw hu hall fun i =>
    anchor_sandwich hF p i nw hu (hgu i) 0 (fun k hk => by rw [show k = 0 by omega]; simpa using hu)

/-- **Ko-transfer chains do not repeat a generator.** Along a weakly descending sequence of columns outside `D`, a chain
of anchor transfers `F c_{iₙ} uₙ₊₁ ≤ p_{iₙ₊₁}`, `iₙ₊₁ ≠ iₙ`, visits pairwise distinct generators: a repetition
`i_m = i_{m'}` makes `{i_m, …, i_{m'-1}}` a closed transfer set at the column `u_{m'}`. No chain condition is used. -/
theorem ko_chain_injective {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : ι → α) (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (u : ℕ → α) (i : ℕ → ι) (N : ℕ) (hu : ∀ n ≤ N, ¬ ∃ j, u n ≤ p j) (hdesc : ∀ n, u (n + 1) ≤ u n)
    (hne : ∀ n < N, i (n + 1) ≠ i n) (htr : ∀ n < N, F (anchor p (i n)) (u (n + 1)) ≤ p (i (n + 1))) :
    ∀ m m', m < m' → m' ≤ N → i m ≠ i m' := by
  classical
  have hanti : Antitone u := antitone_nat_of_succ_le hdesc
  intro m m' hmm hm' heq
  let T : Finset ι := ((Finset.range m').filter (m ≤ ·)).image i
  refine no_upward_transfer_cycle hF p nw (hu m' hm') T
    ⟨i m, Finset.mem_image.2 ⟨m, Finset.mem_filter.2 ⟨Finset.mem_range.2 hmm, le_rfl⟩, rfl⟩⟩
    fun a ha => ?_
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨htm', htm⟩ := Finset.mem_filter.1 ht
  rw [Finset.mem_range] at htm'
  refine ⟨i (t + 1), ?_, hne t (by omega), u (t + 1), hanti (by omega), htr t (by omega)⟩
  rcases Nat.lt_or_ge (t + 1) m' with h | h
  · exact Finset.mem_image.2 ⟨t + 1, Finset.mem_filter.2 ⟨Finset.mem_range.2 h, by omega⟩, rfl⟩
  · rw [show t + 1 = m' by omega, ← heq]
    exact Finset.mem_image.2 ⟨m, Finset.mem_filter.2 ⟨Finset.mem_range.2 hmm, le_rfl⟩, rfl⟩

/-- **Ko-transfer chains are finite**: an infinite chain would be an injection `ℕ → ι`. -/
theorem ko_chain_finite {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : ι → α) (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (u : ℕ → α) (i : ℕ → ι) (hu : ∀ n, ¬ ∃ j, u n ≤ p j) (hdesc : ∀ n, u (n + 1) ≤ u n)
    (hne : ∀ n, i (n + 1) ≠ i n) (htr : ∀ n, F (anchor p (i n)) (u (n + 1)) ≤ p (i (n + 1))) : False := by
  have hinj : Function.Injective i := by
    intro m m' h
    by_contra hmm
    rcases Nat.lt_or_gt_of_ne hmm with hlt | hlt
    · exact ko_chain_injective hF p nw u i m' (fun n _ => hu n) hdesc (fun n _ => hne n) (fun n _ => htr n)
        m m' hlt le_rfl h
    · exact ko_chain_injective hF p nw u i m (fun n _ => hu n) hdesc (fun n _ => hne n) (fun n _ => htr n)
        m' m hlt le_rfl h.symm
  exact not_injective_infinite_finite i hinj

/-- **Cut from a common lower bound of the anchor last points.** Let `s ∉ D` be contracting for every generator (e.g.
`⊤`) and `wᵢ` the last point outside `D` of the `F cᵢ`-orbit of `s`. No column `u ∉ D` lies below every `wᵢ`: each
endpoint `F cᵢ wᵢ` avoids `↓pᵢ` (`anchor_sandwich`), so every generator has an upward transfer edge at `u`. -/
theorem lastpoints_no_common_lower [WellFoundedLT α] [Nonempty ι] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {s : α} (hs : ¬ ∃ j, s ≤ p j) (hgs : ∀ i, F (p i) s ≤ s) (n : ι → ℕ)
    (hE : ∀ i, EntersAt (F (anchor p i)) (fun x => ∃ j, x ≤ p j) s (n i))
    {u : α} (hu : ¬ ∃ j, u ≤ p j) (hlow : ∀ i, u ≤ (F (anchor p i))^[n i] s) : False := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine no_upward_transfer_cycle hF p nw hu Finset.univ ⟨i₀, Finset.mem_univ _⟩ fun a _ => ?_
  obtain ⟨k, hk⟩ := (hE a).2
  have hout := entry_label_contracting hF p a nw hs (hgs a) (hE a)
  rw [Function.iterate_succ_apply'] at hk hout
  exact ⟨k, Finset.mem_univ _, fun e => hout (e ▸ hk), _, hlow a, hk⟩

/-- **No closed meet family.** At a column `u ∉ D`, no nonempty family `𝒜` of nonempty generator sets has, for every
`A ∈ 𝒜`, some `B ∈ 𝒜` with `F (⋀_A p) u ≤ ⋀_B p`. This is `no_closed_rows` for the meet rows; the bounds may come
from any source, e.g. `F (⋀_A p) u ≤ ⋀_{a ∈ A} F cₐ vₐ` for columns `vₐ ≥ u` (a meet of anchor values can lie in `D`
although no single one does). -/
theorem no_closed_meet_family {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : ι → α) (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {u : α} (hu : ¬ ∃ i, u ≤ p i) :
    ∀ 𝒜 : Finset (Finset ι), 𝒜.Nonempty → (∀ A ∈ 𝒜, A.Nonempty) →
      ¬ ∀ A ∈ 𝒜, ∃ B ∈ 𝒜, F (A.inf p) u ≤ B.inf p := by
  classical
  intro 𝒜
  induction 𝒜 using Finset.strongInduction with
  | H 𝒜 ih =>
    intro hne hA h𝒜
    set 𝒜' := 𝒜.filter (fun B => ∃ A ∈ 𝒜, F (A.inf p) u ≤ B.inf p) with h𝒜'
    have hsub : 𝒜' ⊆ 𝒜 := Finset.filter_subset _ _
    obtain ⟨A₀, hA₀⟩ := hne
    by_cases heq : 𝒜' = 𝒜
    · have hle : F (𝒜.inf fun A => A.inf p) u ≤ 𝒜.inf fun A => A.inf p := Finset.le_inf fun B hB => by
        have hB' : B ∈ 𝒜' := heq ▸ hB
        obtain ⟨A, hA, hAB⟩ := (Finset.mem_filter.1 hB').2
        exact (hF _ _ _ _ (Finset.inf_le (f := fun A => A.inf p) hA) le_rfl).trans hAB
      obtain ⟨a₀, ha₀⟩ := hA A₀ hA₀
      exact (nw _ ⟨a₀, (Finset.inf_le (f := fun A => A.inf p) hA₀).trans (Finset.inf_le ha₀)⟩ u hu).1 hle
    · have hlt : 𝒜' ⊂ 𝒜 := Finset.ssubset_iff_subset_ne.2 ⟨hsub, heq⟩
      obtain ⟨B₀, hB₀, h₀⟩ := h𝒜 A₀ hA₀
      refine ih 𝒜' hlt ⟨B₀, Finset.mem_filter.2 ⟨hB₀, A₀, hA₀, h₀⟩⟩ (fun A hA' => hA A (hsub hA')) fun A hA' => ?_
      obtain ⟨B, hB, hAB⟩ := h𝒜 A (hsub hA')
      exact ⟨B, Finset.mem_filter.2 ⟨hB, A, hsub hA', hAB⟩, hAB⟩

/-- **Sink generator.** In a counterexample there is a column `u ∉ D` and a generator `j` whose anchor row never
transfers on the comparability cone of `u`: for `v ≥ u`, and for `v ≤ u` outside `D`, `F cⱼ v` lies below no `pₖ`
with `k ≠ j`. Hence no column `v ≤ u` outside `D` is `pⱼ`-contracting. Proof: choose `u` with a maximal upward transfer
digraph (finitely many edges; the digraph only grows downward); it is acyclic, so it has a generator without out-edges,
and a transfer of that generator below `u` would add an edge. -/
theorem sink_generator [WellFoundedLT α] [Nonempty ι] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α) (htop : ¬ ∃ i, ⊤ ≤ p i)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) :
    ∃ u, (¬ ∃ i, u ≤ p i) ∧ ∃ j,
      (∀ v, (u ≤ v ∨ (v ≤ u ∧ ¬ ∃ i, v ≤ p i)) → ∀ k, k ≠ j → ¬ F (anchor p j) v ≤ p k) ∧
      (∀ v, v ≤ u → (¬ ∃ i, v ≤ p i) → ¬ F (p j) v ≤ v) := by
  classical
  let E : α → Finset (ι × ι) := fun u =>
    Finset.univ.filter (fun e => e.2 ≠ e.1 ∧ ∃ v, u ≤ v ∧ F (anchor p e.1) v ≤ p e.2)
  have hEanti : ∀ u u', u' ≤ u → E u ⊆ E u' := fun u u' h e he => by
    obtain ⟨-, hne, v, huv, hv⟩ := Finset.mem_filter.1 he
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hne, v, h.trans huv, hv⟩
  let N := (Finset.univ : Finset (ι × ι)).card
  obtain ⟨_, ⟨u, hu, rfl⟩, hmin⟩ := (wellFounded_lt (α := ℕ)).has_min
    {n | ∃ u, (¬ ∃ i, u ≤ p i) ∧ N - (E u).card = n} ⟨_, ⊤, fun ⟨i, hi⟩ => htop ⟨i, hi⟩, rfl⟩
  have hstab : ∀ v, v ≤ u → (¬ ∃ i, v ≤ p i) → E v = E u := fun v hvu hv => by
    by_contra hne
    have hlt : E u ⊂ E v := Finset.ssubset_iff_subset_ne.2 ⟨hEanti u v hvu, fun h => hne h.symm⟩
    have hc := Finset.card_lt_card hlt
    have hN : (E v).card ≤ N := Finset.card_le_univ _
    exact hmin _ ⟨v, hv, rfl⟩ (by omega)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hsink : ∃ j, ∀ k, k ≠ j → ∀ v, u ≤ v → ¬ F (anchor p j) v ≤ p k := by
    by_contra hall
    push_neg at hall
    exact no_upward_transfer_cycle hF p nw hu Finset.univ ⟨i₀, Finset.mem_univ _⟩ fun a _ => by
      obtain ⟨k, hka, v, huv, hv⟩ := hall a
      exact ⟨k, Finset.mem_univ _, hka, v, huv, hv⟩
  obtain ⟨j, hj⟩ := hsink
  have hcone : ∀ v, (u ≤ v ∨ (v ≤ u ∧ ¬ ∃ i, v ≤ p i)) → ∀ k, k ≠ j → ¬ F (anchor p j) v ≤ p k := by
    rintro v (huv | ⟨hvu, hv⟩) k hkj hle
    · exact hj k hkj v huv hle
    · have he : (j, k) ∈ E v := Finset.mem_filter.2 ⟨Finset.mem_univ _, hkj, v, le_rfl, hle⟩
      rw [hstab v hvu hv] at he
      obtain ⟨-, -, w, huw, hw⟩ := Finset.mem_filter.1 he
      exact hj k hkj w huw hw
  refine ⟨u, hu, j, hcone, fun v hvu hv hgv => ?_⟩
  have hcv : F (anchor p j) v ≤ v := (hF _ _ _ _ (anchor_le p j) le_rfl).trans hgv
  obtain ⟨n, hU, hend⟩ := FGTwo.orbit_end (InD := fun x => ∃ i, x ≤ p i) hF ⟨j, anchor_le p j⟩ nw v hv hcv
  have hout := anchor_sandwich hF p j nw hv hgv n hU
  obtain ⟨k, hk⟩ := hend
  have hkj : k ≠ j := fun e => hout (e ▸ hk)
  have hwv : (F (anchor p j))^[n] v ≤ v :=
    Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) hcv (Nat.zero_le n)
  exact hcone _ (Or.inr ⟨hwv.trans hvu, hU n le_rfl⟩) k hkj hk

end Mordor.Profile
