import Mordor.BottomMaxCell
import Mordor.AsyncMeetGrid

/-!
# Rank-two cuts: incidence structure and isolated petals (round 26, §34.3z¹⁴⁴)

ChatGPT brief "The rank-two overlapping-petal problem" (effective HEAD 17249ec).

A *rank-two* cut is a down-set `D` in which every strict chain below a member has length `≤ 2`
(`IsRankTwo D`: `v < w < z ∈ D → v = ⊥`). Its maximal members are *blocks*, its atoms are *points*.

* `exists_block_above` (ACC): every member lies below a block.
* `block_meet` : distinct blocks meet in `⊥` or in a point (`v < m ⊓ n → v = ⊥`).
* `cut_of_finitely_many_blocks`: finitely many blocks covering `D` give a witness (`AsyncGrid.cut_fingen_dcc`).
* `cut_of_common_centre`: blocks pairwise meeting below one centre `r` below all of them give a witness
  (`FGTwo.cut_bouquet`).
* `petal_entry_escapes` (**isolated petals**, DCC): in a witness-free proper cut, if `a ∈ D`, `r ≤ a`, and every member
  not below `a` meets `a` only below `r`, then the orbit `⊤, F r ⊤, …` first enters `D` outside `↓a`.
  (`FGTwo.orbit_end` + `FGTwo.sandwich` with the petal `↓a` and the rest `B = {x ∈ D | ↓x ∩ ↓a ⊆ ↓r}`.)
  `r = a` is `BottomMaxCell.orbit_entry_escapes`; for a bouquet every petal is isolated with the common centre.
  At rank two: a block whose points shared with other blocks all lie below `r` (`r = ⊥`: a block meeting no other
  block; `r = s`: a block whose only shared point is `s`) is never below the `r`-orbit's first entry.
-/

namespace Mordor.RankTwo
open Mordor

set_option linter.unusedSectionVars false

variable {β : Type*} [Lattice β] [BoundedOrder β]

/-- Every strict chain below a member of `D` has length at most two. -/
def IsRankTwo (D : Set β) : Prop := ∀ z ∈ D, ∀ w, w < z → ∀ v, v < w → v = ⊥

/-- A block: a maximal member of `D`. -/
def IsBlock (D : Set β) (m : β) : Prop := m ∈ D ∧ ∀ n ∈ D, m ≤ n → n = m

theorem exists_block_above [WellFoundedGT β] {D : Set β} {x : β} (hx : x ∈ D) : ∃ m, IsBlock D m ∧ x ≤ m := by
  obtain ⟨m, ⟨hmD, hxm⟩, hmax⟩ := (wellFounded_gt (α := β)).has_min {m | m ∈ D ∧ x ≤ m} ⟨x, hx, le_rfl⟩
  exact ⟨m, ⟨hmD, fun n hn hmn => by
    by_contra hne
    exact hmax n ⟨hn, hxm.trans hmn⟩ (lt_of_le_of_ne hmn (Ne.symm hne))⟩, hxm⟩

/-- **Blocks meet in `⊥` or a point.** -/
theorem block_meet {D : Set β} (h2 : IsRankTwo D) {m n : β} (hm : IsBlock D m) (hn : IsBlock D n) (hne : m ≠ n) :
    ∀ v, v < m ⊓ n → v = ⊥ := by
  intro v hv
  have hlt : m ⊓ n < m := lt_of_le_of_ne inf_le_left (fun e => hne (hm.2 n hn.1 (e ▸ inf_le_right)).symm)
  exact h2 m hm.1 (m ⊓ n) hlt v hv

variable [WellFoundedLT β] {F : β → β → β}

/-- **Finitely many blocks** (`AsyncGrid.cut_fingen_dcc`). -/
theorem cut_of_finitely_many_blocks (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set β}
    (hD : ∀ ⦃x y⦄, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) {k : ℕ} (g : Fin k → β)
    (hg : ∀ i, g i ∈ D) (hcov : ∀ x ∈ D, ∃ i, x ≤ g i) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  obtain ⟨i₀, -⟩ := hcov ⊥ hbot
  have hk : 0 < k := Fin.pos i₀
  obtain ⟨x, ⟨i, hxi⟩, y, hy, hw⟩ := Mordor.AsyncGrid.cut_fingen_dcc hk hF g
    (fun ⟨i, hi⟩ => htop (hD hi (hg i)))
  exact ⟨x, hD hxi (hg i), y, fun hyD => hy (hcov y hyD), hw⟩

/-- **A common centre** (`FGTwo.cut_bouquet`). -/
theorem cut_of_common_centre {ι : Type*} [Nonempty ι] (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {D : Set β} (hD : ∀ ⦃x y⦄, x ≤ y → y ∈ D → x ∈ D) (htop : ⊤ ∉ D) (p : ι → β) (hp : ∀ i, p i ∈ D)
    (hcov : ∀ x ∈ D, ∃ i, x ≤ p i) {r : β} (hrp : ∀ i, r ≤ p i)
    (hmeet : ∀ i j, i ≠ j → ∀ z, z ≤ p i → z ≤ p j → z ≤ r) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  obtain ⟨x, ⟨i, hxi⟩, y, hy, hw⟩ := Mordor.FGTwo.cut_bouquet hF p hrp hmeet
    (fun ⟨i, hi⟩ => htop (hD hi (hp i)))
  exact ⟨x, hD hxi (hp i), y, fun hyD => hy (hcov y hyD), hw⟩

/-- **Isolated petals: the centre's orbit enters outside the petal.** -/
theorem petal_entry_escapes (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set β}
    (hD : ∀ ⦃x y⦄, x ≤ y → y ∈ D → x ∈ D) (htop : ⊤ ∉ D) (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    {a r : β} (ha : a ∈ D) (hra : r ≤ a) (hiso : ∀ x ∈ D, ¬ x ≤ a → ∀ z, z ≤ x → z ≤ a → z ≤ r) :
    ∃ n, (∀ k ≤ n, (F r)^[k] ⊤ ∉ D) ∧ F r ((F r)^[n] ⊤) ∈ D ∧ ¬ F r ((F r)^[n] ⊤) ≤ a := by
  have nw' : ∀ x, x ∈ D → ∀ y, ¬ y ∈ D → ¬ F x y ≤ x ∧ ¬ y ≤ F x y := fun x hx y hy => nw x hx y hy
  have hrD : r ∈ D := hD hra ha
  obtain ⟨n, hU, hend⟩ := Mordor.FGTwo.orbit_end (InD := (· ∈ D)) hF hrD nw' ⊤ htop le_top
  refine ⟨n, hU, hend, fun hle => ?_⟩
  let InB : β → Prop := fun x => x ∈ D ∧ ∀ z, z ≤ x → z ≤ a → z ≤ r
  exact Mordor.FGTwo.sandwich (InD := (· ∈ D)) (InB := InB) (a := a) (r := r) hF
    (fun x => ⟨fun hx => (em (x ≤ a)).elim Or.inl (fun h => Or.inr ⟨hx, hiso x hx h⟩),
      fun h => h.elim (fun h' => hD h' ha) (fun h' => h'.1)⟩)
    (fun x y hxy hy => ⟨hD hxy hy.1, fun z hz hza => hy.2 z (hz.trans hxy) hza⟩)
    hra (fun z hza hz => hz.2 z le_rfl hza) nw' ⊤ htop le_top n hU hle

end Mordor.RankTwo
