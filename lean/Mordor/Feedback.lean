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
