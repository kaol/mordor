import Mordor.Profile

/-!
# Transfer sets and self-entry sets (round 26, §34.3z⁷⁸)

Continuation of §34.3z⁷⁷. `D = ⋃ᵢ ↓pᵢ` finite, `F` monotone, no witness, join anchors `cₐ = anchor p a`. For a column
`u ∉ D` and a generator `a`:

* `Transfer F p a u`: `F cₐ u` lies below some `pₖ` with `k ≠ a` (the anchor obligation of `a` is passed on at `u`);
* `SelfEntry F p a u`: `F cₐ u ≤ pₐ` (it enters `D` in its own petal; by `entry_label_single` then in no other).

**Correction to §34.3z⁷⁷.** `upward_le` records that the "upward" transfer digraph adds nothing: `v ≥ u` gives
`F cₐ u ≤ F cₐ v`, so an edge witnessed at `v` is already an edge at `u`. `no_upward_transfer_cycle` is equivalent to
its single-column case `no_anchor_transfer_cycle`; the global input in §34.3z⁷⁷ is `anchor_sandwich` and the DCC
choice in `sink_generator`, not the digraph lemma.

* `transfer_down`, `self_down`: both sets are down-closed inside `Dᶜ`, so `D ∪ Transfer a` and `D ∪ SelfEntry a` are
  down-sets of `L` containing `D`.
* `transfer_self_disjoint`: they are disjoint.
* `self_entry_unique`: **at most one generator self-enters at a column** (the meet row `pₐ ⊓ p_b` lies below both
  anchors).
* `no_common_transfer` (`simultaneous_entry`): no column transfers for every generator, i.e. `⋂ₐ (D ∪ Transfer a) = D`.
* `contracting_not_self`: a `pₐ`-contracting column does not self-enter for `a` (`l4`).
* `min_contracting_transfers` (DCC): a minimal `pₐ`-contracting column transfers for `a` at the first step.
* `transfer_nonempty` (DCC): every `Transfer a` is nonempty (the last point of the `F cₐ`-orbit of `⊤`).
* `sink_below` (DCC): **refined sink.** Below any column `s ∉ D` there is `u ∉ D` on whose whole down-cone (in `Dᶜ`)
  every generator's transfer status is constant, and a generator `j` that transfers neither at `s` nor anywhere on
  the cone; no cone column is `pⱼ`-contracting.
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An anchor bound at a higher column is a bound at a lower one. -/
theorem upward_le {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α) {u v : α}
    (huv : u ≤ v) {a k : ι} (h : F (anchor p a) v ≤ p k) : F (anchor p a) u ≤ p k :=
  (hF _ _ _ _ le_rfl huv).trans h

/-- The anchor of `a` passes its obligation on at `u`. -/
def Transfer (F : α → α → α) (p : ι → α) (a : ι) (u : α) : Prop :=
  (¬ ∃ i, u ≤ p i) ∧ ∃ k, k ≠ a ∧ F (anchor p a) u ≤ p k

/-- The anchor of `a` enters `D` at `u` in its own petal. -/
def SelfEntry (F : α → α → α) (p : ι → α) (a : ι) (u : α) : Prop :=
  (¬ ∃ i, u ≤ p i) ∧ F (anchor p a) u ≤ p a

section
variable {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF in
theorem transfer_down {a : ι} {u v : α} (hvu : v ≤ u) (hv : ¬ ∃ i, v ≤ p i) (h : Transfer F p a u) :
    Transfer F p a v :=
  ⟨hv, h.2.elim fun k ⟨hka, hk⟩ => ⟨k, hka, upward_le hF p hvu hk⟩⟩

include hF in
theorem self_down {a : ι} {u v : α} (hvu : v ≤ u) (hv : ¬ ∃ i, v ≤ p i) (h : SelfEntry F p a u) :
    SelfEntry F p a v :=
  ⟨hv, upward_le hF p hvu h.2⟩

include nw in
theorem transfer_self_disjoint {a : ι} {u : α} (ht : Transfer F p a u) (hs : SelfEntry F p a u) : False := by
  obtain ⟨hu, k, hka, hk⟩ := ht
  exact (nw _ ⟨a, anchor_le p a⟩ u hu).1 ((le_inf hs.2 hk).trans (meet_le_anchor p hka))

include hF nw in
/-- **At most one self-entry per column.** -/
theorem self_entry_unique {a b : ι} (hab : a ≠ b) {u : α} (ha : SelfEntry F p a u) (hb : SelfEntry F p b u) :
    False := by
  have h1 : F (p a ⊓ p b) u ≤ p a := (hF _ _ _ _ (meet_le_anchor p hab.symm) le_rfl).trans ha.2
  have h2 : F (p a ⊓ p b) u ≤ p b := by
    have : p a ⊓ p b ≤ anchor p b := inf_comm (p a) (p b) ▸ meet_le_anchor p hab
    exact (hF _ _ _ _ this le_rfl).trans hb.2
  exact (nw _ ⟨a, inf_le_left⟩ u ha.1).1 (le_inf h1 h2)

include hF nw in
/-- **No column transfers for every generator.** -/
theorem no_common_transfer [Nonempty ι] {u : α} (h : ∀ a, Transfer F p a u) : False := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  exact no_anchor_transfer_cycle hF p nw (h i₀).1 Finset.univ ⟨i₀, Finset.mem_univ _⟩ fun a _ => by
    obtain ⟨-, k, hka, hk⟩ := h a; exact ⟨k, Finset.mem_univ _, hka, hk⟩

include hF nw in
theorem contracting_not_self [WellFoundedLT α] {a : ι} {u : α} (hgu : F (p a) u ≤ u) : ¬ SelfEntry F p a u :=
  fun h => anchor_sandwich hF p a nw h.1 hgu 0 (fun k hk => by rw [show k = 0 by omega]; simpa using h.1) h.2

include hF nw in
/-- **A minimal `pₐ`-contracting column transfers for `a` at the first step.** -/
theorem min_contracting_transfers [WellFoundedLT α] {a : ι} {u : α} (hu : ¬ ∃ i, u ≤ p i)
    (hgu : F (p a) u ≤ u) (hmin : ∀ v, v < u → (¬ ∃ i, v ≤ p i) → ¬ F (p a) v ≤ v) : Transfer F p a u := by
  have hin : ∃ i, F (p a) u ≤ p i := by
    by_contra hout
    have hlt : F (p a) u < u := lt_of_le_of_ne hgu fun heq => (nw _ ⟨a, le_rfl⟩ u hu).2 heq.ge
    exact hmin _ hlt hout (hF _ _ _ _ le_rfl hgu)
  obtain ⟨k, hk⟩ := hin
  have hka : k ≠ a := fun e => (nw _ ⟨a, le_rfl⟩ u hu).1 (e ▸ hk)
  exact ⟨hu, k, hka, (hF _ _ _ _ (anchor_le p a) le_rfl).trans hk⟩

include hF nw in
/-- From a `pₐ`-contracting column the `F cₐ`-orbit reaches a transfer column below it. -/
theorem transfer_below_contracting [WellFoundedLT α] {a : ι} {s : α} (hs : ¬ ∃ i, s ≤ p i)
    (hgs : F (p a) s ≤ s) : ∃ w, w ≤ s ∧ Transfer F p a w := by
  have hcs : F (anchor p a) s ≤ s := (hF _ _ _ _ (anchor_le p a) le_rfl).trans hgs
  obtain ⟨n, hU, k, hk⟩ := FGTwo.orbit_end (InD := fun x => ∃ i, x ≤ p i) hF ⟨a, anchor_le p a⟩ nw s hs hcs
  have hout := anchor_sandwich hF p a nw hs hgs n hU
  refine ⟨_, Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) hcs (Nat.zero_le n),
    hU n le_rfl, k, fun e => hout (e ▸ hk), hk⟩

include hF nw in
theorem transfer_nonempty [WellFoundedLT α] (htop : ¬ ∃ i, ⊤ ≤ p i) (a : ι) : ∃ w, Transfer F p a w :=
  (transfer_below_contracting hF p nw htop le_top).elim fun w ⟨_, hw⟩ => ⟨w, hw⟩

include hF nw in
/-- **Refined sink.** -/
theorem sink_below [WellFoundedLT α] [Nonempty ι] {s : α} (hs : ¬ ∃ i, s ≤ p i) :
    ∃ u, u ≤ s ∧ (¬ ∃ i, u ≤ p i) ∧
      (∀ a v, v ≤ u → (¬ ∃ i, v ≤ p i) → (Transfer F p a v ↔ Transfer F p a u)) ∧
      ∃ j, ¬ Transfer F p j s ∧ (∀ v, v ≤ u → ¬ Transfer F p j v) ∧
        (∀ v, v ≤ u → (¬ ∃ i, v ≤ p i) → ¬ F (p j) v ≤ v) := by
  classical
  let E : α → Finset (ι × ι) := fun u => Finset.univ.filter (fun e => e.2 ≠ e.1 ∧ F (anchor p e.1) u ≤ p e.2)
  have hEanti : ∀ u u', u' ≤ u → E u ⊆ E u' := fun u u' h e he => by
    obtain ⟨-, hne, hv⟩ := Finset.mem_filter.1 he
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hne, upward_le hF p h hv⟩
  let N := (Finset.univ : Finset (ι × ι)).card
  obtain ⟨_, ⟨u, ⟨hus, hu⟩, rfl⟩, hmin⟩ := (wellFounded_lt (α := ℕ)).has_min
    {n | ∃ u, (u ≤ s ∧ ¬ ∃ i, u ≤ p i) ∧ N - (E u).card = n} ⟨_, s, ⟨le_rfl, hs⟩, rfl⟩
  have hstab : ∀ v, v ≤ u → (¬ ∃ i, v ≤ p i) → E v = E u := fun v hvu hv => by
    by_contra hne
    have hlt : E u ⊂ E v := Finset.ssubset_iff_subset_ne.2 ⟨hEanti u v hvu, fun h => hne h.symm⟩
    have hc := Finset.card_lt_card hlt
    have hN : (E v).card ≤ N := Finset.card_le_univ _
    exact hmin _ ⟨v, ⟨hvu.trans hus, hv⟩, rfl⟩ (by omega)
  have hTE : ∀ a v, Transfer F p a v ↔ (¬ ∃ i, v ≤ p i) ∧ ∃ k, (a, k) ∈ E v := fun a v =>
    ⟨fun ⟨hv, k, hka, hk⟩ => ⟨hv, k, Finset.mem_filter.2 ⟨Finset.mem_univ _, hka, hk⟩⟩,
     fun ⟨hv, k, hk⟩ => ⟨hv, k, (Finset.mem_filter.1 hk).2⟩⟩
  have hunif : ∀ a v, v ≤ u → (¬ ∃ i, v ≤ p i) → (Transfer F p a v ↔ Transfer F p a u) := fun a v hvu hv => by
    rw [hTE, hTE, hstab v hvu hv]; exact ⟨fun ⟨_, h⟩ => ⟨hu, h⟩, fun ⟨_, h⟩ => ⟨hv, h⟩⟩
  obtain ⟨j, hj⟩ : ∃ j, ¬ Transfer F p j u := by
    by_contra hall; push_neg at hall; exact no_common_transfer hF p nw hall
  have hcone : ∀ v, v ≤ u → ¬ Transfer F p j v := fun v hvu ht => hj ((hunif j v hvu ht.1).1 ht)
  refine ⟨u, hus, hu, hunif, j, fun ht => hj ?_, hcone, fun v hvu hv hgv => ?_⟩
  · obtain ⟨-, k, hka, hk⟩ := ht; exact ⟨hu, k, hka, upward_le hF p hus hk⟩
  · obtain ⟨w, hwv, hw⟩ := transfer_below_contracting hF p nw hv hgv
    exact hcone w (hwv.trans hvu) hw

end
end Mordor.Profile
