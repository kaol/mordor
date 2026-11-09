import Mordor.GapMax

/-!
# General-separator runs and the gap implications (round 26, §34.3z¹³⁶)

The maximal-separator conjectures fail at edge-height 3 (the line-cycle family, `experiments/separation/
cycle_family.py`), while the general-separator form survives. This file makes the general form a route to Cut.

* `Closed T`: every stage is meet-closed and contains `⊥, ⊤`. The gap implications need nothing else:
  `cut_of_gap_parent_closed` and `cut_of_max_gap_drop_closed` hold for *any* closed sequence of finite families.
* `GStep T T'`: `T' = meetClose (T ∪ S)`, every member of `S` a general separator (`F x y ≤ s`, `y ≰ s`) of some bad
  pair of `T`, and every bad pair receiving one. `GRun`: the run built from `GStep`s.
* `step_gstep`, `run_grun`: a maximal-separator run is a general run. `grun_closed`: general runs are closed.
* `cut_of_terminal_grun`: a general run reaching a terminal or stuck stage gives a witness (∃-GSB ⇒ Cut).
* `cut_of_gap_parent_general`, `cut_of_max_gap_drop_general`: a general run with the gap parent property, resp.
  strictly dropping maximum gap (stuck stages exempt), forces a witness.
-/

namespace Mordor.GeneralRun
open Finset Mordor.SeparatorStages Mordor.GapPotential Mordor.MaxGap Mordor.SeparatorAncestry

set_option linter.unusedSectionVars false

variable {β : Type*} [Lattice β] [BoundedOrder β] [DecidableEq β] [DecidableLE β]

/-- Every stage is meet-closed and contains `⊥` and `⊤`. -/
def Closed (T : ℕ → Finset β) : Prop := ∀ n, ⊥ ∈ T n ∧ ⊤ ∈ T n ∧ ∀ a ∈ T n, ∀ b ∈ T n, a ⊓ b ∈ T n

variable (F : β → β → β) (D : Set β)

/-- One stage with general separators. -/
def GStep (T T' : Finset β) : Prop :=
  ∃ S : Finset β, T' = meetClose (T ∪ S) ∧ (∀ s ∈ S, ∃ x y, Bad F D T x y ∧ F x y ≤ s ∧ ¬ y ≤ s) ∧
    ∀ x y, Bad F D T x y → ∃ s ∈ S, F x y ≤ s ∧ ¬ y ≤ s

/-- A run with general separators. -/
def GRun (T : ℕ → Finset β) : Prop :=
  T 0 = {⊥, ⊤} ∧ ∀ n, ((∀ x y, ¬ Bad F D (T n) x y) ∧ T (n + 1) = T n) ∨ GStep F D (T n) (T (n + 1))

variable {F D}

theorem step_gstep {T T' : Finset β} (h : Step F D T T') : GStep F D T T' := by
  obtain ⟨S, he, hS, hcov⟩ := h
  refine ⟨S, he, fun s hs => ?_, fun x y hb => ?_⟩
  · obtain ⟨x, y, hb, hm⟩ := hS s hs; exact ⟨x, y, hb, hm.1, hm.2.1⟩
  · obtain ⟨s, hs, hm⟩ := hcov x y hb; exact ⟨s, hs, hm.1, hm.2.1⟩

theorem run_grun {T : ℕ → Finset β} (h : Run F D T) : GRun F D T :=
  ⟨h.1, fun n => (h.2 n).imp id step_gstep⟩

theorem grun_closed {T : ℕ → Finset β} (hr : GRun F D T) : Closed T := by
  intro n
  induction n with
  | zero =>
    rw [hr.1]
    refine ⟨by simp, by simp, fun a ha b hb => ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb ⊢
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  | succ n ih =>
    rcases hr.2 n with ⟨-, he⟩ | ⟨S, he, -, -⟩
    · rw [he]; exact ih
    · rw [he]
      exact ⟨subset_meetClose _ (Finset.mem_union_left _ ih.1), top_mem_meetClose _, meetClose_closed _⟩

/-- **Existential stage bound ⇒ Cut, for general runs.** A general run reaching a terminal or stuck stage gives a
witness. -/
theorem cut_of_terminal_grun (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) {T : ℕ → Finset β} (hr : GRun F D T)
    {N : ℕ} (hN : (∀ x y, ¬ Bad F D (T N) x y) ∨ ∃ x y, Bad F D (T N) x y ∧ y ≤ F x y) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  obtain ⟨hb, ht, hc⟩ := grun_closed hr N
  rcases hN with h | ⟨x, y, hxy, hst⟩
  · exact terminal_witness hF hD hbot htop hb ht hc h
  · exact ⟨x, hxy.2.1, y, hxy.2.2.2.1, Or.inr hst⟩

/-- **Gap parent property ⇒ Cut, for any closed sequence.** -/
theorem cut_of_gap_parent_closed (H : ℕ) (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) {T : ℕ → Finset β} (hc : Closed T)
    (hgap : ∀ n x' y', Bad F D (T (n + 1)) x' y' → (∃ a b, Bad F D (T (n + 1)) a b ∧ b ≤ F a b) ∨
      ∃ x y, Bad F D (T n) x y ∧ height H y' + (H - height H x') < height H y + (H - height H x)) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  let φ : Finset β → β → β → ℕ := fun _ x y => height H y + (H - height H x)
  have hB : ∀ n x y, Bad F D (T n) x y → φ (T n) x y ≤ 2 * H := fun n x y _ => by
    have := height_le (H := H) y; have := height_le (H := H) x; simp only [φ]; omega
  rcases potential_parent_stage_bound φ T hB hgap with ⟨n, -, a, b, hab, hst⟩ | hterm
  · exact ⟨a, hab.2.1, b, hab.2.2.2.1, Or.inr hst⟩
  · obtain ⟨hb, ht, hcl⟩ := hc (2 * H + 1)
    exact terminal_witness hF hD hbot htop hb ht hcl hterm

/-- **Maximum-gap drop ⇒ Cut, for any closed sequence.** -/
theorem cut_of_max_gap_drop_closed (H : ℕ) (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) {T : ℕ → Finset β} (hc : Closed T)
    (hdrop : ∀ n (h' : (badSet F D (T (n + 1))).Nonempty),
      (∃ a b, Bad F D (T (n + 1)) a b ∧ b ≤ F a b) ∨
      ∃ h : (badSet F D (T n)).Nonempty, (badSet F D (T (n + 1))).sup' h' (gap H) < (badSet F D (T n)).sup' h (gap H)) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  refine cut_of_gap_parent_closed H hF hD hbot htop hc fun n x' y' hb => ?_
  have h' : (badSet F D (T (n + 1))).Nonempty := ⟨(x', y'), mem_badSet.2 hb⟩
  rcases hdrop n h' with hst | ⟨h, hlt⟩
  · exact Or.inl hst
  · right
    obtain ⟨p, hp, hlt'⟩ := (parent_iff_max_drop h h' (gap H)).2 hlt (x', y') (mem_badSet.2 hb)
    exact ⟨p.1, p.2, mem_badSet.1 hp, hlt'⟩

theorem cut_of_gap_parent_general (H : ℕ) (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) {T : ℕ → Finset β} (hr : GRun F D T)
    (hgap : ∀ n x' y', Bad F D (T (n + 1)) x' y' → (∃ a b, Bad F D (T (n + 1)) a b ∧ b ≤ F a b) ∨
      ∃ x y, Bad F D (T n) x y ∧ height H y' + (H - height H x') < height H y + (H - height H x)) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y :=
  cut_of_gap_parent_closed H hF hD hbot htop (grun_closed hr) hgap

theorem cut_of_max_gap_drop_general (H : ℕ) (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) {T : ℕ → Finset β} (hr : GRun F D T)
    (hdrop : ∀ n (h' : (badSet F D (T (n + 1))).Nonempty),
      (∃ a b, Bad F D (T (n + 1)) a b ∧ b ≤ F a b) ∨
      ∃ h : (badSet F D (T n)).Nonempty, (badSet F D (T (n + 1))).sup' h' (gap H) < (badSet F D (T n)).sup' h (gap H)) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y :=
  cut_of_max_gap_drop_closed H hF hD hbot htop (grun_closed hr) hdrop

end Mordor.GeneralRun
