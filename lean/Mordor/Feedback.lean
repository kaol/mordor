import Mordor.Crossing
import Mordor.RelativeCut
import Mathlib.Order.OrderIsoNat

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

/-! ### An injective ray (§34.3z⁶⁷) -/

section Inj
variable {β : Type*} (step : β → β → Prop) (r : β)

/-- Points reachable from `r` in exactly `n` steps. -/
def layer : ℕ → Set β
  | 0 => {r}
  | n + 1 => {y | ∃ x ∈ layer n, step x y}

theorem layer_finite (hfin : ∀ q, {q' | step q q'}.Finite) : ∀ n, (layer step r n).Finite
  | 0 => Set.finite_singleton r
  | n + 1 => by
      refine ((layer_finite hfin n).biUnion fun x _ => hfin x).subset ?_
      rintro y ⟨x, hx, hxy⟩; exact Set.mem_biUnion hx hxy

theorem reach_iff_layer {y : β} : Relation.ReflTransGen step r y ↔ ∃ n, y ∈ layer step r n := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hst ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, _, hn, hst⟩
  · rintro ⟨n, hn⟩
    induction n generalizing y with
    | zero => exact hn ▸ Relation.ReflTransGen.refl
    | succ n ih => obtain ⟨x, hx, hxy⟩ := hn; exact (ih hx).tail hxy

/-- **König with an injective path.** -/
theorem konig_injective (hfin : ∀ q, {q' | step q q'}.Finite)
    (hinf : {x | Relation.ReflTransGen step r x}.Infinite) :
    ∃ f : ℕ → β, f 0 = r ∧ (∀ n, step (f n) (f (n + 1))) ∧ Function.Injective f := by
  classical
  have hex : ∀ y, Relation.ReflTransGen step r y → ∃ n, y ∈ layer step r n := fun y h => (reach_iff_layer step r).1 h
  let dist : β → ℕ := fun y => if h : ∃ n, y ∈ layer step r n then Nat.find h else 0
  have hdist : ∀ y (h : ∃ n, y ∈ layer step r n), dist y = Nat.find h := fun y h => by simp only [dist, dif_pos h]
  let step' : β → β → Prop := fun x y => step x y ∧ (∃ n, x ∈ layer step r n) ∧ dist y = dist x + 1
  have hall : ∀ d y (h : ∃ n, y ∈ layer step r n), dist y = d → Relation.ReflTransGen step' r y := by
    intro d
    induction d with
    | zero =>
      intro y h hd
      rw [hdist y h, Nat.find_eq_zero] at hd
      exact hd ▸ Relation.ReflTransGen.refl
    | succ d ih =>
      intro y h hd
      rw [hdist y h] at hd
      have hy := Nat.find_spec h
      rw [hd] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      have hxe : ∃ n, x ∈ layer step r n := ⟨d, hx⟩
      have hdx : dist x = d := by
        rw [hdist x hxe]
        refine le_antisymm (Nat.find_min' hxe hx) (not_lt.1 fun hlt => ?_)
        have : y ∈ layer step r (Nat.find hxe + 1) := ⟨x, Nat.find_spec hxe, hxy⟩
        have := Nat.find_min' h this
        omega
      refine (ih x hxe hdx).tail ⟨hxy, hxe, ?_⟩
      rw [hdx, hdist y h, hd]
  obtain ⟨f, hf0, hf⟩ := konig step' (fun q => (hfin q).subset fun q' h => h.1) (hinf.mono fun y hy =>
    hall _ y (hex y hy) rfl)
  have hd0 : dist r = 0 := by
    rw [hdist r ⟨0, rfl⟩, Nat.find_eq_zero]; rfl
  have hdn : ∀ n, dist (f n) = n := fun n => by
    induction n with
    | zero => rw [hf0, hd0]
    | succ n ih => rw [(hf n).2.2, ih]
  exact ⟨f, hf0, fun n => (hf n).1, fun a b hab => by rw [← hdn a, ← hdn b, hab]⟩

end Inj

/-- **An injective feedback ray.** -/
theorem feedback_ray_injective [Nonempty ι] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α) (htop : ¬ ∃ i, (⊤ : α) ≤ p i)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) :
    ∃ q : ℕ → α, q 0 = ⊤ ∧ (∀ n, FStep F p (q n) (q (n + 1))) ∧ Function.Injective q := by
  classical
  refine konig_injective (FStep F p) ⊤ (fun q => ?_) ?_
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

/-- **Antichain extraction.** In a chain-finite order an injective sequence has an antichain subsequence. -/
theorem antichain_subseq {γ : Type*} [PartialOrder γ] [WellFoundedLT γ] [WellFoundedGT γ] (c : ℕ → γ)
    (hc : Function.Injective c) : ∃ g : ℕ ↪o ℕ, ∀ m n, m ≠ n → ¬ c (g m) ≤ c (g n) := by
  haveI : IsTrans γ (· < ·) := ⟨fun _ _ _ => lt_trans⟩
  haveI : IsTrans γ (· > ·) := ⟨fun _ _ _ h h' => lt_trans h' h⟩
  obtain ⟨g₁, h₁ | h₁⟩ := exists_increasing_or_nonincreasing_subseq (· < ·) c
  · obtain ⟨x, ⟨n, rfl⟩, hmax⟩ := (wellFounded_gt (α := γ)).has_min (Set.range fun n => c (g₁ n)) ⟨_, ⟨0, rfl⟩⟩
    exact absurd (h₁ n (n + 1) (Nat.lt_succ_self n)) (hmax _ ⟨n + 1, rfl⟩)
  obtain ⟨g₂, h₂ | h₂⟩ := exists_increasing_or_nonincreasing_subseq (· > ·) fun n => c (g₁ n)
  · obtain ⟨x, ⟨n, rfl⟩, hmin⟩ := (wellFounded_lt (α := γ)).has_min (Set.range fun n => c (g₁ (g₂ n))) ⟨_, ⟨0, rfl⟩⟩
    exact absurd (h₂ n (n + 1) (Nat.lt_succ_self n)) (hmin _ ⟨n + 1, rfl⟩)
  refine ⟨g₂.trans g₁, fun m n hmn hle => ?_⟩
  have hne : c (g₁ (g₂ m)) ≠ c (g₁ (g₂ n)) := fun h => hmn (g₂.injective (g₁.injective (hc h)))
  have hlt : c (g₁ (g₂ m)) < c (g₁ (g₂ n)) := lt_of_le_of_ne hle hne
  rcases lt_or_gt_of_ne hmn with h | h
  · exact h₁ _ _ (g₂.strictMono h) hlt
  · exact h₂ _ _ h hlt

/-- **The tail joins of a sequence stabilize** (DCC): `sₙ = ⨆_{k ≥ n} c k` is antitone, so it is eventually
constant. -/
theorem tail_join_stable {γ : Type*} [CompleteLattice γ] [WellFoundedLT γ] (c : ℕ → γ) :
    ∃ N, ∀ n, N ≤ n → (⨆ k, ⨆ (_ : n ≤ k), c k) = ⨆ k, ⨆ (_ : N ≤ k), c k := by
  let s : ℕ → γ := fun n => ⨆ k, ⨆ (_ : n ≤ k), c k
  have hanti : ∀ n n', n ≤ n' → s n' ≤ s n := fun n n' h =>
    iSup_mono fun k => iSup_mono' fun hk => ⟨h.trans hk, le_rfl⟩
  obtain ⟨_, ⟨N, rfl⟩, hmin⟩ := (wellFounded_lt (α := γ)).has_min (Set.range s) ⟨_, ⟨0, rfl⟩⟩
  refine ⟨N, fun n hn => ?_⟩
  by_contra hne
  exact hmin _ ⟨n, rfl⟩ (lt_of_le_of_ne (hanti N n hn) hne)

/-! ### Support windows (§34.3z⁶⁷) -/

/-- **Every support window of some fixed length has empty intersection** (DCC). Along a ray
`q (t + 1) = F (meetRow p (x t)) (q t)` of outside columns, with supports `A_t = {i | x t ≤ p i}`: for every
generator `i` there is `N` such that no block of `N` consecutive steps has `i` in every support. If it did, the
ray would sit below the `F pᵢ`-orbit of `⊤`, which enters `D` (`FGTwo.orbit_end`). Taking the maximum over the finitely
many generators gives one window length for all of them. -/
theorem feedback_window [WellFoundedLT α] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (htop : ¬ ∃ i, (⊤ : α) ≤ p i) (q x : ℕ → α) (hq : ∀ n, ¬ ∃ i, q n ≤ p i)
    (hstep : ∀ t, q (t + 1) = F (meetRow p (x t)) (q t)) :
    ∃ N, ∀ n i, ∃ t, n ≤ t ∧ t < n + N ∧ ¬ x t ≤ p i := by
  have hone : ∀ i, ∃ N, ∀ n, ∃ t, n ≤ t ∧ t < n + N ∧ ¬ x t ≤ p i := by
    intro i
    obtain ⟨n₀, -, j, hj⟩ := FGTwo.orbit_end (InD := fun x => ∃ i, x ≤ p i) hF ⟨i, le_rfl⟩ nw ⊤ htop le_top
    refine ⟨n₀ + 1, fun n => ?_⟩
    by_contra hall
    push_neg at hall
    have hle : ∀ k, k ≤ n₀ + 1 → q (n + k) ≤ (F (p i))^[k] ⊤ := by
      intro k hk
      induction k with
      | zero => exact le_top
      | succ k ih =>
        rw [← Nat.add_assoc, hstep, Function.iterate_succ_apply']
        exact hF _ _ _ _ (meetRow_le (hall (n + k) (Nat.le_add_right n k) (by omega)))
          (ih (by omega))
    have h := hle (n₀ + 1) le_rfl
    rw [Function.iterate_succ_apply'] at h
    exact hq (n + (n₀ + 1)) ⟨j, h.trans hj⟩
  choose N hN using hone
  refine ⟨Finset.univ.sup N, fun n i => ?_⟩
  obtain ⟨t, ht1, ht2, ht3⟩ := hN i n
  exact ⟨t, ht1, lt_of_lt_of_le ht2 (Nat.add_le_add_left (Finset.le_sup (Finset.mem_univ i)) n), ht3⟩

/-- **Contraction-tolerant window** (§34.3z⁶⁸, DCC). Along a ray of outside columns
`q (t + 1) = F (meetRow p (x t)) (q t)` with `x t ∈ D`, for every generator `i` and every `n` there is a step
`t ≥ n` that **omits `i` and does not contract** (`¬ x t ≤ p i` and `¬ q (t + 1) ≤ q t`). Steps containing `i`
advance the bound `q ≤ (F pᵢ)^[k] ⊤`; contracting steps keep it; the orbit of `⊤` enters `D` after finitely many
advances, and contractions alone are strict descents. -/
theorem feedback_window_contract [WellFoundedLT α] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (htop : ¬ ∃ i, (⊤ : α) ≤ p i) (q x : ℕ → α) (hq : ∀ n, ¬ ∃ i, q n ≤ p i) (hx : ∀ t, ∃ i, x t ≤ p i)
    (hstep : ∀ t, q (t + 1) = F (meetRow p (x t)) (q t)) (i : ι) (n : ℕ) :
    ∃ t, n ≤ t ∧ ¬ x t ≤ p i ∧ ¬ q (t + 1) ≤ q t := by
  classical
  by_contra hall
  push_neg at hall
  obtain ⟨n₀, -, j₀, hj₀⟩ := FGTwo.orbit_end (InD := fun x => ∃ i, x ≤ p i) hF ⟨i, le_rfl⟩ nw ⊤ htop le_top
  -- K j = number of steps containing `i` among n, …, n + j - 1
  let K : ℕ → ℕ := fun j => ((Finset.range j).filter fun u => x (n + u) ≤ p i).card
  have hK0 : K 0 = 0 := rfl
  have hKs : ∀ j, K (j + 1) = K j + if x (n + j) ≤ p i then 1 else 0 := fun j => by
    simp only [K, Finset.range_add_one, Finset.filter_insert]
    split_ifs with h
    · rw [Finset.card_insert_of_notMem (by simp)]
    · rfl
  have hbound : ∀ j, q (n + j) ≤ (F (p i))^[K j] ⊤ := by
    intro j
    induction j with
    | zero => exact le_top
    | succ j ih =>
      rw [hKs, ← Nat.add_assoc]
      by_cases hxi : x (n + j) ≤ p i
      · rw [if_pos hxi, hstep, Function.iterate_succ_apply']
        exact hF _ _ _ _ (meetRow_le hxi) ih
      · rw [if_neg hxi, Nat.add_zero]
        exact (hall (n + j) (Nat.le_add_right n j) hxi).trans ih
  have hKmono : Monotone K := monotone_nat_of_le_succ fun j => by rw [hKs]; exact Nat.le_add_right _ _
  -- K never reaches n₀ + 1
  have hlt : ∀ j, K j < n₀ + 1 := by
    intro j
    by_contra hge
    push_neg at hge
    have hreach : ∃ j', K j' = n₀ + 1 := by
      have hex : ∃ j', n₀ + 1 ≤ K j' := ⟨j, hge⟩
      let j' := Nat.find hex
      refine ⟨j', le_antisymm ?_ (Nat.find_spec hex)⟩
      rcases Nat.eq_zero_or_pos j' with h0 | hpos
      · have hs := Nat.find_spec hex; rw [show Nat.find hex = 0 from h0, hK0] at hs; omega
      · obtain ⟨j'', hj''⟩ : ∃ j'', j' = j'' + 1 := ⟨j' - 1, by omega⟩
        have hprev : K j'' < n₀ + 1 := by
          have hm := Nat.find_min hex (show j'' < Nat.find hex by omega); omega
        have hstep' := hKs j''
        rw [← hj''] at hstep'
        split_ifs at hstep' <;> omega
    obtain ⟨j', hj'⟩ := hreach
    have h := hbound j'
    rw [hj', Function.iterate_succ_apply'] at h
    exact hq (n + j') ⟨j₀, h.trans hj₀⟩
  -- so K is eventually constant: from J on every step omits `i`, hence contracts strictly
  obtain ⟨J, hJ⟩ : ∃ J, ∀ j, J ≤ j → K j = K J := by
    have hfinvals : ∃ v, (∃ j, K j = v) ∧ ∀ j, K j ≤ v := by
      have hS : ((Finset.range (n₀ + 1)).filter fun v => ∃ j, K j = v).Nonempty :=
        ⟨K 0, Finset.mem_filter.2 ⟨Finset.mem_range.2 (hlt 0), 0, rfl⟩⟩
      refine ⟨_, (Finset.mem_filter.1 (Finset.max'_mem _ hS)).2, fun j => Finset.le_max' _ _ ?_⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (hlt j), j, rfl⟩
    obtain ⟨v, ⟨J, hJv⟩, hmax⟩ := hfinvals
    exact ⟨J, fun j hj => le_antisymm (hJv ▸ hmax j) (hKmono hj)⟩
  have hdesc : ∀ j, J ≤ j → q (n + j + 1) < q (n + j) := by
    intro j hj
    have hxi : ¬ x (n + j) ≤ p i := by
      intro h
      have := hKs j; rw [if_pos h, hJ j hj, hJ (j + 1) (by omega)] at this; omega
    have hc := hall (n + j) (Nat.le_add_right n j) hxi
    refine lt_of_le_of_ne hc fun heq => ?_
    have hnw := (nw (meetRow p (x (n + j))) (by obtain ⟨k, hk⟩ := hx (n + j); exact ⟨k, meetRow_le hk⟩)
      (q (n + j)) (hq _)).2
    rw [← hstep, heq] at hnw
    exact hnw le_rfl
  obtain ⟨_, ⟨m, rfl⟩, hmin⟩ := (wellFounded_lt (α := α)).has_min (Set.range fun m => q (n + (J + m))) ⟨_, ⟨0, rfl⟩⟩
  refine hmin _ ⟨m + 1, rfl⟩ ?_
  have := hdesc (J + m) (Nat.le_add_right J m)
  rwa [show n + (J + m) + 1 = n + (J + (m + 1)) by omega] at this

/-! ### Coalition fixed point (§34.3z⁷³) -/

/-- The collective row operator `H_J(t) = ⋁_{i ∈ J} F (pᵢ) t`. -/
def coalition (F : α → α → α) (p : ι → α) (J : Finset ι) (t : α) : α := J.sup fun i => F (p i) t

omit [Fintype ι] [DecidableEq ι] in
theorem coalition_mono {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
    (J : Finset ι) : Monotone (coalition F p J) := fun _ _ h =>
  Finset.sup_mono_fun fun _ _ => hF _ _ _ _ le_rfl h

/-- **The tail envelope is post-fixed for the coalition.** If from stage `N` every support meets `J`, every column
lies below `S`, and `S` is the join of the successor tail, then `S ≤ H_J(S)`. -/
theorem coalition_postfixed {γ : Type*} [CompleteLattice γ] {ι' : Type*} {F : γ → γ → γ}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι' → γ) (J : Finset ι') (q r : ℕ → γ) (N : ℕ) (S : γ)
    (hstep : ∀ n, q (n + 1) = F (r n) (q n)) (hS : ∀ n, N ≤ n → q n ≤ S)
    (hsup : S ≤ ⨆ n, ⨆ (_ : N ≤ n), q (n + 1)) (hJ : ∀ n, N ≤ n → ∃ i ∈ J, r n ≤ p i) :
    S ≤ J.sup fun i => F (p i) S :=
  hsup.trans (iSup₂_le fun n hn => by
    obtain ⟨i, hi, hri⟩ := hJ n hn
    rw [hstep]
    exact (hF _ _ _ _ hri (hS n hn)).trans (Finset.le_sup (f := fun i => F (p i) S) hi))

omit [Fintype ι] [DecidableEq ι] in
/-- **The coalition fixed point above a post-fixed point** (ACC): iterating `H_J` from `S` stabilizes at some
`t = H_J^k(S) ≥ S` with `t = H_J(t)`. -/
theorem coalition_fixedpoint [WellFoundedGT α] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α) (J : Finset ι) {S : α}
    (hS : S ≤ coalition F p J S) :
    ∃ k, S ≤ (coalition F p J)^[k] S ∧ coalition F p J ((coalition F p J)^[k] S) = (coalition F p J)^[k] S := by
  set H := coalition F p J
  have hmono := coalition_mono hF p J
  have hasc : ∀ k, H^[k] S ≤ H^[k + 1] S := fun k => by
    induction k with
    | zero => exact hS
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply' H (k + 1)]; exact hmono ih
  have hge : ∀ k, S ≤ H^[k] S := fun k => by
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact ih.trans (hasc k)
  obtain ⟨_, ⟨k, rfl⟩, hmax⟩ := (wellFounded_gt (α := α)).has_min (Set.range fun k => H^[k] S) ⟨_, ⟨0, rfl⟩⟩
  refine ⟨k, hge k, ?_⟩
  have h1 := hasc k
  rw [Function.iterate_succ_apply'] at h1
  by_contra hne
  refine hmax _ ⟨k + 1, rfl⟩ ?_
  show H^[k] S < H^[k + 1] S
  rw [Function.iterate_succ_apply']; exact lt_of_le_of_ne h1 (Ne.symm hne)

omit [DecidableEq ι] in
/-- **Components of the coalition fixed point.** If `t = H_J(t)` lies outside `D`, every component
`wᵢ = F (pᵢ) t` (`i ∈ J`) satisfies `wᵢ ≤ t` and `wᵢ < t` (no-witness); if moreover some outside column `q'` lies
below `F (pᵢ) t` (as the ray successors do), `wᵢ ∉ D`. The full-meet row value `b = F (⋀ p) t` lies below every
component, strictly below `t`, and the full-meet row contracts at `b`. -/
theorem coalition_components {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (p : ι → α) (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)
    (J : Finset ι) {t : α} (ht : coalition F p J t = t) (htD : ¬ ∃ i, t ≤ p i) :
    (∀ i ∈ J, F (p i) t < t) ∧
    (∀ i ∈ J, ∀ q', (¬ ∃ j, q' ≤ p j) → q' ≤ F (p i) t → ¬ ∃ j, F (p i) t ≤ p j) ∧
    ((∃ i, i ∈ J) → F (Finset.univ.inf p) t < t ∧ (∀ i ∈ J, F (Finset.univ.inf p) t ≤ F (p i) t) ∧
      F (Finset.univ.inf p) (F (Finset.univ.inf p) t) ≤ F (Finset.univ.inf p) t) := by
  have hle : ∀ i ∈ J, F (p i) t ≤ t := fun i hi => (Finset.le_sup (f := fun i => F (p i) t) hi).trans ht.le
  refine ⟨fun i hi => lt_of_le_of_ne (hle i hi) fun heq => (nw (p i) ⟨i, le_rfl⟩ t htD).2 heq.ge,
    fun i _ q' hq' hle ⟨j, hj⟩ => hq' ⟨j, hle.trans hj⟩, fun ⟨i₀, hi₀⟩ => ?_⟩
  have hb : ∀ i ∈ J, F (Finset.univ.inf p) t ≤ F (p i) t := fun i _ =>
    hF _ _ _ _ (Finset.inf_le (Finset.mem_univ i)) le_rfl
  have hbt : F (Finset.univ.inf p) t ≤ t := (hb i₀ hi₀).trans (hle i₀ hi₀)
  refine ⟨lt_of_le_of_ne hbt fun heq => (nw _ ⟨i₀, Finset.inf_le (Finset.mem_univ i₀)⟩ t htD).2 heq.ge, hb,
    hF _ _ _ _ le_rfl hbt⟩

omit [Fintype ι] [DecidableEq ι] in
/-- **No singleton coalition**: `t = F (pᵢ) t` is impossible for `t ∉ D`. -/
theorem coalition_not_singleton {F : α → α → α} (p : ι → α)
    (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (i : ι) {t : α}
    (ht : coalition F p {i} t = t) (htD : ¬ ∃ j, t ≤ p j) : False := by
  simp only [coalition, Finset.sup_singleton] at ht
  exact (nw (p i) ⟨i, le_rfl⟩ t htD).2 ht.ge

/-- **Essential members of a minimal hitting set.** If `J` meets every member of `𝒜` and no proper subset does, every
`i ∈ J` is the only member of `J` in some `A ∈ 𝒜`. -/
theorem essential_member {κ : Type*} [DecidableEq κ] (𝒜 : Finset (Finset κ)) (J : Finset κ)
    (hhit : ∀ A ∈ 𝒜, (A ∩ J).Nonempty) (hmin : ∀ J' ⊂ J, ¬ ∀ A ∈ 𝒜, (A ∩ J').Nonempty) :
    ∀ i ∈ J, ∃ A ∈ 𝒜, A ∩ J = {i} := by
  intro i hi
  have hsub : J.erase i ⊂ J := Finset.erase_ssubset hi
  have := hmin _ hsub
  push_neg at this
  obtain ⟨A, hA, hempty⟩ := this
  refine ⟨A, hA, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun j hj => ?_⟩⟩
  · obtain ⟨j, hj⟩ := hhit A hA
    by_contra hiA
    have hji : j ≠ i := fun h => hiA (h ▸ hj)
    exact Finset.not_nonempty_iff_eq_empty.2 hempty
      ⟨j, Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hj).1, Finset.mem_erase.2 ⟨hji, (Finset.mem_inter.1 hj).2⟩⟩⟩
  · by_contra hji
    exact Finset.not_nonempty_iff_eq_empty.2 hempty
      ⟨j, Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hj).1, Finset.mem_erase.2 ⟨hji, (Finset.mem_inter.1 hj).2⟩⟩⟩

/-! ### Exchange networks (§34.3z⁷⁴) -/

section Exchange
set_option linter.unusedSectionVars false
variable {γ : Type*} [Lattice γ] [OrderBot γ] {κ : Type*} [Fintype κ] [DecidableEq κ]
  (E : κ → κ → Prop) [DecidableRel E] (g : κ → γ → γ)

/-- The edge-balanced operator `Φ(x)ⱼ = ⋁_{i → j} gⱼ(xᵢ)`. -/
def exch (x : κ → γ) (j : κ) : γ := (Finset.univ.filter fun i => E i j).sup fun i => g j (x i)

theorem exch_mono (hg : ∀ j, Monotone (g j)) : Monotone (exch E g) := fun _ _ h j =>
  Finset.sup_mono_fun fun i _ => hg j (h i)

omit [DecidableEq κ] in
/-- An ascending sequence in an ACC order is eventually constant. -/
theorem asc_stable {δ : Type*} [PartialOrder δ] [WellFoundedGT δ] (a : ℕ → δ) (ha : Monotone a) :
    ∃ N, ∀ n, N ≤ n → a n = a N := by
  obtain ⟨_, ⟨N, rfl⟩, hmax⟩ := (wellFounded_gt (α := δ)).has_min (Set.range a) ⟨_, ⟨0, rfl⟩⟩
  exact ⟨N, fun n hn => by
    by_contra hne; exact hmax _ ⟨n, rfl⟩ (lt_of_le_of_ne (ha hn) (Ne.symm hne))⟩

/-- **Edge-balanced vector fixed point** (ACC). If `s ≤ Φ(s)`, `Φ(w) ≤ w` and `s ≤ w`, iterating `Φ` from `s`
reaches `u` with `s ≤ u ≤ w` and `Φ(u) = u` (coordinatewise ACC suffices for a finite vertex set). -/
theorem exch_fixedpoint [WellFoundedGT γ] (hg : ∀ j, Monotone (g j)) {s w : κ → γ} (hs : s ≤ exch E g s)
    (hw : exch E g w ≤ w) (hsw : s ≤ w) : ∃ u, s ≤ u ∧ u ≤ w ∧ exch E g u = u := by
  have hm := exch_mono E g hg
  let a : ℕ → κ → γ := fun k => (exch E g)^[k] s
  have hasc : Monotone a := monotone_nat_of_le_succ fun k => by
    show (exch E g)^[k] s ≤ (exch E g)^[k + 1] s
    induction k with
    | zero => exact hs
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply' _ (k + 1)]; exact hm ih
  have hle : ∀ k, a k ≤ w := fun k => by
    show (exch E g)^[k] s ≤ w
    induction k with
    | zero => exact hsw
    | succ k ih => rw [Function.iterate_succ_apply']; exact (hm ih).trans hw
  have hcoord : ∀ j, ∃ N, ∀ n, N ≤ n → a n j = a N j := fun j =>
    asc_stable (fun n => a n j) fun _ _ h => hasc h j
  choose N hN using hcoord
  let M := Finset.univ.sup N
  have hMstab : ∀ n, M ≤ n → a n = a M := fun n hn => funext fun j => by
    have hj : N j ≤ M := Finset.le_sup (Finset.mem_univ j)
    rw [hN j n (hj.trans hn), hN j M hj]
  refine ⟨a M, hasc (Nat.zero_le M), hle M, ?_⟩
  have := hMstab (M + 1) (Nat.le_succ M)
  simp only [a, Function.iterate_succ_apply'] at this
  exact this

omit [DecidableEq κ] in
/-- At a fixed point, every edge contracts: `E i j → gⱼ(uᵢ) ≤ uⱼ`. -/
theorem exch_edge_le {u : κ → γ} (hu : exch E g u = u) {i j : κ} (hij : E i j) :
    g j (u i) ≤ u j := by
  have hmem : i ∈ Finset.univ.filter fun i => E i j := by simp [hij]
  exact (Finset.le_sup (f := fun i => g j (u i)) hmem).trans (congrFun hu j).le

/-- The value of a walk: apply `g` along the listed vertices. -/
def walkVal : γ → List κ → γ
  | x, [] => x
  | x, j :: js => walkVal (g j x) js

omit [Fintype κ] [DecidableEq κ] [DecidableRel E] in
theorem walkVal_mono (hg : ∀ j, Monotone (g j)) : ∀ js : List κ, Monotone fun x => walkVal g x js
  | [], _, _, h => h
  | j :: js, _, _, h => walkVal_mono hg js (hg j h)

/-- A walk from `i` along the listed vertices uses only edges. -/
def IsWalk : κ → List κ → Prop
  | _, [] => True
  | i, j :: js => E i j ∧ IsWalk j js

/-- The endpoint of a walk. -/
def walkEnd : κ → List κ → κ
  | i, [] => i
  | _, j :: js => walkEnd j js

omit [DecidableEq κ] in
/-- **Walks contract at the fixed point**: along a walk `i → j₁ → ⋯ → jᵣ` of edges, the composite of the `g`'s
maps `uᵢ` below `u_{jᵣ}`. For a closed walk (`walkEnd i js = i`) this is `G_C(uᵢ) ≤ uᵢ`. -/
theorem walk_contract (hg : ∀ j, Monotone (g j)) {u : κ → γ} (hu : exch E g u = u) :
    ∀ (i : κ) (js : List κ), IsWalk E i js → walkVal g (u i) js ≤ u (walkEnd i js)
  | i, [], _ => le_rfl
  | i, j :: js, hc => (walkVal_mono g hg js (exch_edge_le E g hu hc.1)).trans (walk_contract hg hu j js hc.2)

omit [Fintype κ] [DecidableEq κ] [DecidableRel E] in
/-- **The cycle fixed point** (DCC): a monotone map with `G a ≤ a` has a fixed point below `a`, reached by
iterating from `a`. -/
theorem contract_fixed [WellFoundedLT γ] {G : γ → γ} (hG : Monotone G) {a : γ} (ha : G a ≤ a) :
    ∃ x, x ≤ a ∧ G x = x := by
  have hdesc : ∀ k, G^[k + 1] a ≤ G^[k] a := fun k => by
    induction k with
    | zero => exact ha
    | succ k ih =>
      have e1 : G^[k + 1 + 1] a = G (G^[k + 1] a) := Function.iterate_succ_apply' G (k + 1) a
      have e2 : G^[k + 1] a = G (G^[k] a) := Function.iterate_succ_apply' G k a
      rw [e1, e2]; rw [e2] at ih; exact hG ih
  have hle : ∀ k, G^[k] a ≤ a := fun k => by
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (hdesc k).trans ih
  obtain ⟨_, ⟨k, rfl⟩, hmin⟩ := (wellFounded_lt (α := γ)).has_min (Set.range fun k => G^[k] a) ⟨_, ⟨0, rfl⟩⟩
  refine ⟨G^[k] a, hle k, ?_⟩
  by_contra hne
  have h := hdesc k
  rw [Function.iterate_succ_apply'] at h
  exact hmin _ ⟨k + 1, rfl⟩ (by show G^[k + 1] a < G^[k] a; rw [Function.iterate_succ_apply']; exact lt_of_le_of_ne h hne)

end Exchange

/-- The three-set core of the blocker classification (finite check). -/
theorem blockers_core : ∀ A₀ A₁ A₂ : Finset (Fin 3), A₀.Nonempty → A₁.Nonempty → A₂.Nonempty →
    0 ∉ A₀ → 1 ∉ A₁ → 2 ∉ A₂ →
    (Disjoint A₀ A₁ ∨ Disjoint A₀ A₂ ∨ Disjoint A₁ A₂) ∨ (A₀ = {1, 2} ∧ A₁ = {0, 2} ∧ A₂ = {0, 1}) := by
  decide

/-- **Minimal blockers on three generators.** A family of nonempty subsets of `Fin 3` with empty intersection contains
two disjoint members, or contains the triangle `{0,1}, {1,2}, {0,2}`. -/
theorem blockers_three (𝒜 : Finset (Finset (Fin 3))) (hne : ∀ A ∈ 𝒜, A.Nonempty) (hcap : ∀ i, ∃ A ∈ 𝒜, i ∉ A) :
    (∃ A ∈ 𝒜, ∃ B ∈ 𝒜, Disjoint A B) ∨ ({0, 1} ∈ 𝒜 ∧ {1, 2} ∈ 𝒜 ∧ {0, 2} ∈ 𝒜) := by
  obtain ⟨A₀, h₀, n₀⟩ := hcap 0
  obtain ⟨A₁, h₁, n₁⟩ := hcap 1
  obtain ⟨A₂, h₂, n₂⟩ := hcap 2
  rcases blockers_core A₀ A₁ A₂ (hne _ h₀) (hne _ h₁) (hne _ h₂) n₀ n₁ n₂ with (h | h | h) | ⟨e₀, e₁, e₂⟩
  · exact Or.inl ⟨_, h₀, _, h₁, h⟩
  · exact Or.inl ⟨_, h₀, _, h₂, h⟩
  · exact Or.inl ⟨_, h₁, _, h₂, h⟩
  · subst e₀ e₁ e₂; exact Or.inr ⟨h₂, h₀, h₁⟩

end Mordor.Feedback
