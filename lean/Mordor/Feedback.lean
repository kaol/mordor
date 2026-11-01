import Mordor.Crossing
import Mordor.RelativeCut

/-!
# Feedback closure of the meet rows (round 26, §34.3z⁶⁶)

Response to an outside brief proposing a "first-hit row-switching" feedback process for the crossing triple: outside
outputs `F (m_A) q` are fed back as columns.

* The brief's Deliverables 1–2 are existing lemmas: the first-hit value is not below its row
  (`Crossing.endpoint_not_le`, i.e. `A ⊄ Λ(z)`), and at an outside column some row of `A` escapes every `pⱼ`, `j ∈ A`
  (`Crossing.no_closed_rows` with `S = A`).
* `meetRow_range_finite`: the meet rows take finitely many values.
* `feedback_finite`: **if the outside columns reachable from `⊤` by feeding back the outputs of meet rows form a
  finite set, the cut has a witness** (`cut_cross` applied to the row-compressed `F (meetRow p x) y`). So in a
  counterexample for a finitely generated cut the feedback closure is infinite. With finitely many rows per column it
  then contains an infinite feedback ray (König), along which the row must switch infinitely often (a constant row `A`
  from any column enters `D`, since its orbit lies below the `F m_A`-orbit of `⊤`).
-/

namespace Mordor.Feedback
open Mordor.Crossing

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem meetRow_range_finite (p : ι → α) : (Set.range (meetRow p)).Finite := by
  classical
  let g : Finset ι → α := fun s => Finset.univ.inf fun i => if i ∈ s then p i else ⊤
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨Finset.univ.filter fun i => x ≤ p i, ?_⟩
  simp only [g, meetRow]
  refine Finset.inf_congr rfl fun i _ => ?_
  by_cases h : x ≤ p i
  · simp [h]
  · simp [h]

/-- **Finite feedback closure forces a witness.** -/
theorem feedback_finite [Nonempty ι] {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : ι → α) (Q : Set α) (hQ : Q.Finite) (htop : ⊤ ∈ Q) (hQout : ∀ q ∈ Q, ¬ ∃ i, q ≤ p i)
    (hcl : ∀ x, (∃ i, x ≤ p i) → ∀ q ∈ Q, (¬ ∃ i, F (meetRow p x) q ≤ p i) → F (meetRow p x) q ∈ Q) :
    ∃ x, (∃ i, x ≤ p i) ∧ ∃ y, (¬ ∃ i, y ≤ p i) ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  classical
  by_contra hno
  push_neg at hno
  have nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y :=
    fun x hx y hy => hno x hx y (by push_neg at hy; exact hy)
  set Dn : Set α := {x | ∃ i, x ≤ p i}
  set M : Set α := meetRow p '' Dn
  have hM : M.Finite := (meetRow_range_finite p).subset (Set.image_subset_range _ _)
  set S : Set α := {⊥} ∪ Q ∪ M ∪ Set.image2 F M Q
  have hS : S.Finite := (((Set.finite_singleton _).union hQ).union hM).union (hM.image2 F hQ)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hMD : ∀ m ∈ M, m ∈ Dn := by
    rintro _ ⟨x, ⟨i, hi⟩, rfl⟩; exact ⟨i, meetRow_le hi⟩
  obtain ⟨x, hx, y, hy, h⟩ := RelativeCut.cut_cross Dn
    (fun a b hab ⟨i, hb⟩ => ⟨i, hab.trans hb⟩) (fun ⟨i, hi⟩ => hQout ⊤ htop ⟨i, hi⟩) ⟨i₀, bot_le⟩
    (fun x y => F (meetRow p x) y)
    (fun a a' b b' _ _ _ _ ha hb => hF _ _ _ _ (meetRow_mono p ha) hb) S hS
    (Or.inl (Or.inl (Or.inl rfl))) (Or.inl (Or.inl (Or.inr htop)))
    (fun x _ hxD y hyS hyD => by
      have hyQ : y ∈ Q := by
        rcases hyS with ((hb | hq) | hm) | ⟨m, hm, q, hq, rfl⟩
        · exact absurd (show y ∈ Dn from hb ▸ ⟨i₀, bot_le⟩) hyD
        · exact hq
        · exact absurd (hMD y hm) hyD
        · obtain ⟨x', hx', rfl⟩ := hm
          exact hcl x' hx' q hq hyD
      exact Or.inr ⟨meetRow p x, ⟨x, hxD, rfl⟩, y, hyQ, rfl⟩)
  obtain ⟨h1, h2⟩ := (rows_to_meets hF p nw).2 x hx y hy
  rcases h with h | h
  · exact h1 h
  · exact h2 h

/-! ### König: an infinite feedback ray, and it switches rows infinitely often -/

/-- **König's lemma for a finitely branching relation**: infinitely many points reachable from `r` give an infinite
path from `r`. -/
theorem konig {β : Type*} (step : β → β → Prop) (hfin : ∀ q, {q' | step q q'}.Finite) {r : β}
    (hinf : {x | Relation.ReflTransGen step r x}.Infinite) :
    ∃ f : ℕ → β, f 0 = r ∧ ∀ n, step (f n) (f (n + 1)) := by
  classical
  let P : β → Prop := fun q => {x | Relation.ReflTransGen step q x}.Infinite
  have hnext : ∀ q, P q → ∃ q', step q q' ∧ P q' := by
    intro q hq
    by_contra hno
    push_neg at hno
    have hsub : {x | Relation.ReflTransGen step q x} ⊆
        {q} ∪ ⋃ q' ∈ {q' | step q q'}, {x | Relation.ReflTransGen step q' x} := by
      intro x hx
      rcases Relation.ReflTransGen.cases_head hx with rfl | ⟨q', hq', hx'⟩
      · exact Or.inl rfl
      · exact Or.inr (Set.mem_biUnion hq' hx')
    refine hq (((Set.finite_singleton q).union ((hfin q).biUnion fun q' hq' => ?_)).subset hsub)
    exact Set.not_infinite.1 (hno q' hq')
  choose! nxt hnxt using hnext
  let f : ℕ → β := fun n => nxt^[n] r
  have hP : ∀ n, P (f n) := fun n => by
    induction n with
    | zero => exact hinf
    | succ n ih => show P (nxt^[n + 1] r); rw [Function.iterate_succ_apply']; exact (hnxt _ ih).2
  refine ⟨f, rfl, fun n => ?_⟩
  show step (nxt^[n] r) (nxt^[n + 1] r)
  rw [Function.iterate_succ_apply']; exact (hnxt _ (hP n)).1

/-- The feedback step: an outside column `q` goes to an outside output `F (meetRow p x) q` of a meet row. -/
def FStep (F : α → α → α) (p : ι → α) (q q' : α) : Prop :=
  (∃ x, (∃ i, x ≤ p i) ∧ q' = F (meetRow p x) q) ∧ ¬ ∃ i, q' ≤ p i

/-- **The infinite feedback ray.** Without a witness, there is a sequence `⊤ = q₀, q₁, …` of outside columns with
`q_{n+1} = F (m_n) q_n` for meet rows `m_n`. -/
theorem feedback_ray [Nonempty ι] {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : ι → α) (htop : ¬ ∃ i, (⊤ : α) ≤ p i)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) :
    ∃ q : ℕ → α, q 0 = ⊤ ∧ ∀ n, FStep F p (q n) (q (n + 1)) := by
  classical
  refine konig (FStep F p) (fun q => ?_) ?_
  · refine ((meetRow_range_finite p).image fun m => F m q).subset ?_
    rintro _ ⟨⟨x, -, rfl⟩, -⟩; exact ⟨meetRow p x, ⟨x, rfl⟩, rfl⟩
  · intro hfin
    have hout : ∀ y ∈ {x | Relation.ReflTransGen (FStep F p) ⊤ x}, ¬ ∃ i, y ≤ p i := by
      intro y hy
      rcases Relation.ReflTransGen.cases_tail hy with rfl | ⟨q', -, hq'⟩
      · exact htop
      · exact hq'.2
    obtain ⟨x, hx, y, hy, h⟩ := feedback_finite hF p _ hfin Relation.ReflTransGen.refl hout
      fun x hx q hq hqo => Relation.ReflTransGen.tail hq ⟨⟨x, hx, rfl⟩, hqo⟩
    rcases h with h | h
    · exact (nw x hx y hy).1 h
    · exact (nw x hx y hy).2 h

omit [Fintype ι] [DecidableEq ι] in
/-- **The ray switches rows infinitely often** (DCC): from no stage on is the row constant. A constant row `m` from
stage `N` gives `q (N + k) ≤ (F m)^[k] ⊤`, and that orbit enters `D` (`FGTwo.orbit_end`). -/
theorem ray_switches [WellFoundedLT α] {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : ι → α) (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (htop : ¬ ∃ i, (⊤ : α) ≤ p i) (q : ℕ → α) (hq : ∀ n, ¬ ∃ i, q n ≤ p i) {m : α} (hm : ∃ i, m ≤ p i) (N : ℕ)
    (hconst : ∀ n, N ≤ n → q (n + 1) = F m (q n)) : False := by
  obtain ⟨n, -, hn⟩ := FGTwo.orbit_end (InD := fun x => ∃ i, x ≤ p i) hF hm nw ⊤ htop le_top
  have hle : ∀ k, q (N + k) ≤ (F m)^[k] ⊤ := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [← Nat.add_assoc, hconst _ (Nat.le_add_right N k), Function.iterate_succ_apply']
      exact hF _ _ _ _ le_rfl ih
  obtain ⟨i, hi⟩ := hn
  have h := hle (n + 1)
  rw [Function.iterate_succ_apply'] at h
  exact hq (N + (n + 1)) ⟨i, h.trans hi⟩

end Mordor.Feedback
