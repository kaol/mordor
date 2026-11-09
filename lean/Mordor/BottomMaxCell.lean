import Mordor.OrbitHeight
import Mordor.FGTwo

/-!
# The normalized top-layer cell: audit, common columns, and the atomic case (round 26, §34.3z¹⁴²)

ChatGPT brief "Prove the normalized top-layer cell" (HEAD 41df0c3).

* `R_no_cross_cell` (**audit**): a cell across `R(F)` — `x ∈ R`, `y ∉ R`, `F x y ≤ x` or `y ≤ F x y` — is impossible
  for every `F`. In the normal form `G = normalize F (R F)` with `R(G) = R(F) ≠ L`, the brief's BottomMaxCell
  conclusion (`m ∈ R` of maximal height, `y > m`, `G m y ≤ m`) is such a cell, since `y ∉ R` by maximality and
  `G m y = F m y` (`normalize_cross`). So BottomMaxCell for normalized `G` with `R(G) ≠ L` is not an intermediate
  lemma but the statement that no such `G` exists, i.e. the Cut Lemma itself (`cutMaps_of_bottom`). It is vacuous
  on finite lattices, where `R(G) = L`.
* `common_column` (the brief's five properties, for **every** `m ∈ R` and `y ∉ R`, no normalization or top layer
  needed): with `u = b y` and `x = m ⊓ u`: `u ∉ R`, `F u y = u`, `x ∈ R`, `x < u`, `q = F x y ≤ u`, `q ≰ m`,
  `y ≰ q`.
* `near_cell_of_atomic_over`, `dual_near_cell`: forced near-cells in an interval `[p, ⊤]` over `p ∈ R` (when `R ∩ [p, ⊤]` is
  atomic over `p`, e.g. every atom `p` at `r = 2`) and at a minimal non-member `c` (always, under ACC).
* `orbit_entry_escapes` (§34.3z¹⁴³): in a witness-free cut, the `F a`-orbit of `⊤` enters `D` outside `↓a`.
* `cut_of_atomic` (**the case `r = 1`**): a down-set `D ∋ ⊥`, `⊤ ∉ D`, all of whose elements are `⊥` or atoms (no
  element strictly between `⊥` and a member) has a witness for every monotone `F` under DCC — `D` is a bouquet with
  centre `⊥` (`FGTwo.cut_bouquet`). `cutMaps_of_R_atomic`: if `R(F)` consists of `⊥` and atoms, the Cut Lemma
  holds for `F`; `cutMaps_of_R_height_le_one`: the same at edge-height `≤ H` when every element of `R(F)` has
  height `≤ 1`. So a normalized counterexample has `r ≥ 2`.
-/

namespace Mordor.BottomMaxCell
open Mordor Mordor.Ground Mordor.GapPotential Mordor.OrbitHeight

set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

/-- **No cell across `R(F)`.** -/
theorem R_no_cross_cell {x y : α} (hx : x ∈ R F) (hy : y ∉ R F) : ¬ F x y ≤ x ∧ ¬ y ≤ F x y :=
  ⟨fun h => hy (R_closed.2.2.2 y (R_closed.1 (b_le h) hx)),
   fun h => hy (R_closed.1 (le_a h) (R_closed.2.2.1 x hx))⟩

/-- **The common-column properties.** -/
theorem common_column {m y : α} (hm : m ∈ R F) (hy : y ∉ R F) :
    b F y ∉ R F ∧ F (b F y) y = b F y ∧ m ⊓ b F y ∈ R F ∧ m ⊓ b F y < b F y ∧
      F (m ⊓ b F y) y ≤ b F y ∧ ¬ F (m ⊓ b F y) y ≤ m ∧ ¬ y ≤ F (m ⊓ b F y) y := by
  have hu : b F y ∉ R F := fun h => hy (R_closed.2.2.2 y h)
  have hfix : F (b F y) y = b F y := (col F y).map_lfp
  have hx : m ⊓ b F y ∈ R F := R_closed.1 inf_le_left hm
  have hlt : m ⊓ b F y < b F y := lt_of_le_of_ne inf_le_right (fun e => hu (e ▸ hx))
  have hq : F (m ⊓ b F y) y ≤ b F y := (F.mono (inf_le_right : m ⊓ b F y ≤ b F y) y).trans hfix.le
  refine ⟨hu, hfix, hx, hlt, hq, fun h => ?_, (R_no_cross_cell hx hy).2⟩
  exact (R_no_cross_cell hx hy).1 (le_inf h hq)

end Mordor.BottomMaxCell

namespace Mordor.BottomMaxCell
open Mordor Mordor.Ground Mordor.GapPotential

/-- **The atomic case.** A cut all of whose members are `⊥` or atoms is a bouquet with centre `⊥`. -/
theorem cut_of_atomic {β : Type*} [Lattice β] [BoundedOrder β] [WellFoundedLT β] {F : β → β → β}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set β} (hD : ∀ ⦃x y⦄, x ≤ y → y ∈ D → x ∈ D)
    (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) (hatom : ∀ z ∈ D, ∀ w, w < z → w = ⊥) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  haveI : Nonempty {z // z ∈ D} := ⟨⟨⊥, hbot⟩⟩
  have hmeet : ∀ i j : {z // z ∈ D}, i ≠ j → ∀ z, z ≤ i.1 → z ≤ j.1 → z ≤ ⊥ := by
    intro i j hij z hzi hzj
    rcases eq_or_lt_of_le hzi with e | hlt
    · have hij' : i.1 < j.1 := lt_of_le_of_ne (e ▸ hzj) (fun h => hij (Subtype.ext h))
      exact (e ▸ hatom j.1 j.2 i.1 hij').le
    · exact (hatom i.1 i.2 z hlt).le
  obtain ⟨x, ⟨i, hxi⟩, y, hy, hw⟩ := Mordor.FGTwo.cut_bouquet hF (fun i : {z // z ∈ D} => i.1)
    (fun _ => bot_le) hmeet (fun ⟨i, hi⟩ => htop (hD hi i.2))
  exact ⟨x, hD hxi i.2, y, fun hyD => hy ⟨⟨y, hyD⟩, le_rfl⟩, hw⟩

end Mordor.BottomMaxCell

namespace Mordor.BottomMaxCell
open Mordor Mordor.Ground Mordor.GapPotential

variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

/-- **`R(F)` atomic ⇒ the Cut Lemma for `F`** (DCC). -/
theorem cutMaps_of_R_atomic [WellFoundedLT α] (hatom : ∀ z ∈ R F, ∀ w, w < z → w = ⊥) : CutMaps F := by
  by_cases ht : (⊤ : α) ∈ R F
  · exact cutMaps_iff_R.2 (Set.eq_univ_of_forall fun u => R_closed.1 le_top ht)
  · obtain ⟨x, hx, y, hy, hw⟩ := cut_of_atomic (fun x x' y y' hx hy => (F.mono hx y).trans ((F x').mono hy))
      R_closed.1 R_closed.2.1 ht hatom
    rcases hw with h | h
    · exact absurd h (R_no_cross_cell hx hy).1
    · exact absurd h (R_no_cross_cell hx hy).2

/-- **The case `r ≤ 1`** at edge-height `≤ H`: if every element of `R(F)` has height `≤ 1`, the Cut Lemma holds. -/
theorem cutMaps_of_R_height_le_one [WellFoundedLT α] {H : ℕ} (hH : 1 ≤ H) (hn : NoChain α (H + 1))
    (h1 : ∀ z ∈ R F, height H z ≤ 1) : CutMaps F := by
  refine cutMaps_of_R_atomic fun z hz w hwz => ?_
  by_contra hw
  have hw1 : 1 ≤ height H w := le_height hH ⟨⊥, bot_lt_iff_ne_bot.2 hw, trivial⟩
  have := height_strictMono hn hwz
  have := h1 z hz
  omega

end Mordor.BottomMaxCell

namespace Mordor.BottomMaxCell
open Mordor Mordor.Ground Mordor.GapPotential

variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

/-- **Forced near-cells over an element of `R`** (DCC). If `p ∈ R(F)`, `⊤ ∉ R(F)`, and no member of `R(F)` above `p`
has an element strictly between `p` and itself (the cut `R ∩ [p, ⊤]` is atomic over `p`), then some `x ∈ R` with
`p ≤ x` and `y ∉ R` with `p < y` satisfy `y ≤ p ⊔ F x y`. (The interval `[p, ⊤]` with `p ⊔ F` is an atomic cut;
its lower alternative would be a cell across `R`.) At `r = 2` this applies to every atom `p ∈ R`. -/
theorem near_cell_of_atomic_over [WellFoundedLT α] {p : α} (hp : p ∈ R F) (ht : (⊤ : α) ∉ R F)
    (hatom : ∀ z ∈ R F, p ≤ z → ∀ w, p ≤ w → w < z → w = p) :
    ∃ x ∈ R F, p ≤ x ∧ ∃ y ∉ R F, p < y ∧ y ≤ p ⊔ F x y ∧ ¬ y ≤ F x y := by
  haveI : Fact (p ≤ ⊤) := ⟨le_top⟩
  let G : Set.Icc p ⊤ → Set.Icc p ⊤ → Set.Icc p ⊤ := fun x y => ⟨p ⊔ F x.1 y.1, le_sup_left, le_top⟩
  have hG : ∀ x x' y y' : Set.Icc p ⊤, x ≤ x' → y ≤ y' → G x y ≤ G x' y' := fun x x' y y' hx hy =>
    show p ⊔ F x.1 y.1 ≤ p ⊔ F x'.1 y'.1 from sup_le_sup_left ((F.mono hx y.1).trans ((F x'.1).mono hy)) p
  have hbot : ((⊥ : Set.Icc p ⊤) : α) = p := rfl
  obtain ⟨x, hx, y, hy, hw⟩ := cut_of_atomic (D := {z : Set.Icc p ⊤ | z.1 ∈ R F}) hG
    (fun x y hxy hyD => R_closed.1 (show x.1 ≤ y.1 from hxy) hyD) (show p ∈ R F from hp)
    (fun h => ht h)
    (fun z hz w hwz => Subtype.ext (hatom z.1 hz z.2.1 w.1 w.2.1 hwz))
  have hxR : x.1 ∈ R F := hx
  have hyR : y.1 ∉ R F := hy
  have hpy : p < y.1 := lt_of_le_of_ne y.2.1 (fun e => hyR (e ▸ hp))
  rcases hw with h | h
  · exact absurd ((le_sup_right.trans (show p ⊔ F x.1 y.1 ≤ x.1 from h))) (R_no_cross_cell hxR hyR).1
  · exact ⟨x.1, hxR, x.2.1, y.1, hyR, hpy, h, (R_no_cross_cell hxR hyR).2⟩

end Mordor.BottomMaxCell

namespace Mordor.BottomMaxCell
open Mordor

variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

/-- **Dual near-cell at a minimal non-member** (ACC). If `c ∉ R(F)` and every `w < c` lies in `R(F)`, some `x ∈ R`,
`x < c`, has `c ⊓ F x c ≤ x` while `F x c ≰ x`. (The principal up-cut `cut_principal_up` in `[⊥, c]` for `c ⊓ F`; its
upper alternative would be a cell across `R`.) -/
theorem dual_near_cell [WellFoundedGT α] {c : α} (hc : c ∉ R F) (hmin : ∀ w, w < c → w ∈ R F) :
    ∃ x ∈ R F, x < c ∧ c ⊓ F x c ≤ x ∧ ¬ F x c ≤ x := by
  haveI : Fact ((⊥ : α) ≤ c) := ⟨bot_le⟩
  let G : Set.Icc ⊥ c →o Set.Icc ⊥ c →o Set.Icc ⊥ c :=
    ⟨fun x => ⟨fun y => ⟨c ⊓ F x.1 y.1, bot_le, inf_le_left⟩,
      fun y y' h => show c ⊓ F x.1 y.1 ≤ c ⊓ F x.1 y'.1 from inf_le_inf_left c ((F x.1).mono h)⟩,
     fun x x' h y => show c ⊓ F x.1 y.1 ≤ c ⊓ F x'.1 y.1 from inf_le_inf_left c (F.mono h y.1)⟩
  have hcb : c ≠ ⊥ := fun e => hc (e ▸ R_closed.2.1)
  have hne : (⊤ : Set.Icc ⊥ c) ≠ ⊥ := fun h => hcb (congrArg Subtype.val h)
  obtain ⟨x, hx, y, hy, hw⟩ := cut_principal_up G ⊤ hne
  have hyc : y.1 = c := le_antisymm y.2.2 hy
  have hxc : x.1 < c := lt_of_le_of_ne x.2.2 (fun e => hx (show (⊤ : Set.Icc ⊥ c) ≤ x from
    show c ≤ x.1 from e.ge))
  have hxR : x.1 ∈ R F := hmin _ hxc
  rcases hw with h | h
  · have h' : c ⊓ F x.1 y.1 ≤ x.1 := h
    rw [hyc] at h'
    exact ⟨x.1, hxR, hxc, h', (R_no_cross_cell hxR hc).1⟩
  · have h' : y.1 ≤ c ⊓ F x.1 y.1 := h
    rw [hyc] at h'
    exact absurd (h'.trans inf_le_right) (R_no_cross_cell hxR hc).2

end Mordor.BottomMaxCell

namespace Mordor.BottomMaxCell
open Mordor

/-- **Orbit entry escapes its row** (DCC). In a witness-free proper cut `D`, for every `a ∈ D` the orbit
`⊤, F a ⊤, F a (F a ⊤), …` first enters `D` at an element `e` with `e ≰ a`. (`FGTwo.orbit_end` gives the entry;
`FGTwo.sandwich` with the degenerate petal `r = a`, `InB = D` excludes `e ≤ a`.) For a principal cut `D = ↓a` this is
the principal cut lemma; for a bouquet it is the petal argument of `cut_bouquet`. -/
theorem orbit_entry_escapes {β : Type*} [Lattice β] [BoundedOrder β] [WellFoundedLT β] {F : β → β → β}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set β} (hD : ∀ ⦃x y⦄, x ≤ y → y ∈ D → x ∈ D)
    (htop : ⊤ ∉ D) (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) {a : β} (ha : a ∈ D) :
    ∃ n, (∀ k ≤ n, (F a)^[k] ⊤ ∉ D) ∧ F a ((F a)^[n] ⊤) ∈ D ∧ ¬ F a ((F a)^[n] ⊤) ≤ a := by
  have nw' : ∀ x, x ∈ D → ∀ y, ¬ y ∈ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y := fun x hx y hy => nw x hx y hy
  obtain ⟨n, hU, hend⟩ := Mordor.FGTwo.orbit_end (InD := (· ∈ D)) hF ha nw' ⊤ htop le_top
  refine ⟨n, hU, hend, fun hle => ?_⟩
  exact Mordor.FGTwo.sandwich (InD := (· ∈ D)) (InB := (· ∈ D)) (a := a) (r := a) hF
    (fun x => ⟨fun h => Or.inr h, fun h => h.elim (fun h' => hD h' ha) id⟩) (fun x y hxy hy => hD hxy hy)
    le_rfl (fun z hz _ => hz) nw' ⊤ htop le_top n hU hle

end Mordor.BottomMaxCell
