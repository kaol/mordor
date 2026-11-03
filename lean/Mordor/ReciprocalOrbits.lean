import Mordor.BoundaryGrid

/-!
# Reciprocal support orbits (round 26, §34.3z⁹⁹)

Response to the brief "reciprocal support orbits and the first-failure matrix". `D ∋ ⊥`, `⊤ ∉ D` a witness-free
down-set, `F` monotone. For a column `q ∉ D` the **column orbit** `c₀ = ⊥`, `cₙ₊₁ = F cₙ q`; for a row `p ∈ D` the
**row orbit** `y₀ = ⊤`, `yₘ₊₁ = F p yₘ`.

* `column_orbit_mono`, `column_orbit_exits` (ACC): the column orbit ascends and leaves `D` (else a fixed point
  `c = F c q` in `D`, a witness).
* `row_orbit_anti`, `row_orbit_enters` (DCC): the row orbit descends and enters `D` (`FGTwo.orbit_end` in this
  notation).
* `interlacing`: `cₙ ≤ p`, `q ≤ yₘ` give `cₙ₊₁ ≤ yₘ₊₁`, for independent `n`, `m`.
* `first_failure_le`, `first_failure_dichotomy`: at the first support failures `s` (first `cₛ ≰ p`) and `t` (first
  `q ≰ yₜ`), `cₛ ≤ yₜ`; hence not both `cₛ ∉ D` and `yₜ ∈ D`.
* `threshold_mono_row`, `threshold_mono_col`: a failure for the larger row (smaller column) is a failure for the
  smaller row (larger column), so `s` is monotone in the row and `t` antitone in the column.
* `staircase_row`, `staircase_col`: the dynamic cells `F cₙ yₘ` are monotone in `n` and antitone in `m`, and
  squeezed: `cₙ ≤ p`, `q ≤ yₘ` give `cₙ₊₁ ≤ F cₙ yₘ ≤ yₘ₊₁`.
* None of this uses minimality of the supports: it holds for every cross pair `(p, q)`.
-/

namespace Mordor.Profile

set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] {F : α → α → α} {InD : α → Prop}
  (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
  (nw : ∀ x, InD x → ∀ y, ¬ InD y → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

/-- Column orbit `c n = (F · q)^[n] ⊥`. -/
def colOrbit (F : α → α → α) (q : α) (n : ℕ) : α := (fun x => F x q)^[n] ⊥
/-- Row orbit `y m = (F p ·)^[m] ⊤`. -/
def rowOrbit (F : α → α → α) (p : α) (m : ℕ) : α := (F p)^[m] ⊤

include hF in
theorem column_orbit_mono (q : α) : Monotone (colOrbit F q) :=
  Monotone.monotone_iterate_of_le_map (fun _ _ h => hF _ _ _ _ h le_rfl) bot_le

include hF in
theorem row_orbit_anti (p : α) : Antitone (rowOrbit F p) :=
  Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) le_top

include hF nw in
/-- **The column orbit leaves `D`** (ACC). -/
theorem column_orbit_exits [WellFoundedGT α] {q : α} (hq : ¬ InD q) :
    ∃ N, ¬ InD (colOrbit F q N) ∧ ∀ n < N, InD (colOrbit F q n) := by
  classical
  by_contra hall
  push_neg at hall
  have hin : ∀ n, InD (colOrbit F q n) := fun n => by
    induction n using Nat.strong_induction_on with
    | _ n ih => by_contra h; exact absurd (hall n h) (fun ⟨k, hk, hkD⟩ => hkD (ih k hk))
  obtain ⟨_, ⟨N, rfl⟩, hmax⟩ := (wellFounded_gt (α := α)).has_min (Set.range (colOrbit F q)) ⟨_, 0, rfl⟩
  have e := eq_of_le_of_not_lt (column_orbit_mono hF q (Nat.le_succ N)) (hmax _ ⟨N + 1, rfl⟩)
  have hstep : colOrbit F q (N + 1) = F (colOrbit F q N) q := by
    unfold colOrbit; rw [Function.iterate_succ_apply']
  have hfix : F (colOrbit F q N) q = colOrbit F q N := by rw [← hstep]; exact e.symm
  exact (nw _ (hin N) q hq).1 hfix.le

include hF nw in
/-- **The row orbit enters `D`** (DCC). -/
theorem row_orbit_enters [WellFoundedLT α] {p : α} (hp : InD p) :
    ∃ M, InD (rowOrbit F p M) ∧ ∀ m < M, ¬ InD (rowOrbit F p m) := by
  classical
  by_contra hall
  push_neg at hall
  have hout : ∀ m, ¬ InD (rowOrbit F p m) := fun m => by
    induction m using Nat.strong_induction_on with
    | _ m ih => intro h; obtain ⟨k, hk, hkD⟩ := hall m h; exact ih k hk hkD
  obtain ⟨_, ⟨M, rfl⟩, hmin⟩ := (wellFounded_lt (α := α)).has_min (Set.range (rowOrbit F p)) ⟨_, 0, rfl⟩
  have e := eq_of_le_of_not_lt (row_orbit_anti hF p (Nat.le_succ M)) (hmin _ ⟨M + 1, rfl⟩)
  have hstep : rowOrbit F p (M + 1) = F p (rowOrbit F p M) := by
    unfold rowOrbit; rw [Function.iterate_succ_apply']
  have hfix : F p (rowOrbit F p M) = rowOrbit F p M := by rw [← hstep]; exact e
  exact (nw p hp _ (hout M)).2 hfix.ge

include hF in
/-- **Interlacing**, for independent indices. -/
theorem interlacing {p q : α} {n m : ℕ} (hc : colOrbit F q n ≤ p) (hy : q ≤ rowOrbit F p m) :
    colOrbit F q (n + 1) ≤ rowOrbit F p (m + 1) := by
  unfold colOrbit rowOrbit
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  exact hF _ _ _ _ hc hy

include hF in
/-- **At the first support failures**, `c s ≤ y t`. -/
theorem first_failure_le {p q : α} {s t : ℕ} (hs : colOrbit F q s ≤ p) (ht : q ≤ rowOrbit F p t) :
    colOrbit F q (s + 1) ≤ rowOrbit F p (t + 1) :=
  interlacing hF hs ht

include hF in
/-- **First-failure dichotomy**: not both `c (s+1) ∉ D` and `y (t+1) ∈ D`. -/
theorem first_failure_dichotomy (hdown : ∀ x y, x ≤ y → InD y → InD x) {p q : α} {s t : ℕ}
    (hs : colOrbit F q s ≤ p) (ht : q ≤ rowOrbit F p t) :
    ¬ (¬ InD (colOrbit F q (s + 1)) ∧ InD (rowOrbit F p (t + 1))) :=
  fun ⟨h1, h2⟩ => h1 (hdown _ _ (first_failure_le hF hs ht) h2)

/-- A failure for the larger row is a failure for the smaller row. -/
theorem threshold_mono_row {p p' c : α} (hpp : p ≤ p') (h : ¬ c ≤ p') : ¬ c ≤ p := fun hc => h (hc.trans hpp)

/-- A failure for the smaller column is a failure for the larger column. -/
theorem threshold_mono_col {q q' y : α} (hqq : q' ≤ q) (h : ¬ q' ≤ y) : ¬ q ≤ y := fun hq => h (hqq.trans hq)

include hF in
theorem staircase_row (q y : α) {n n' : ℕ} (h : n ≤ n') : F (colOrbit F q n) y ≤ F (colOrbit F q n') y :=
  hF _ _ _ _ (column_orbit_mono hF q h) le_rfl

include hF in
theorem staircase_col (p c : α) {m m' : ℕ} (h : m ≤ m') : F c (rowOrbit F p m') ≤ F c (rowOrbit F p m) :=
  hF _ _ _ _ le_rfl (row_orbit_anti hF p h)

include hF in
/-- **The dynamic squeeze.** -/
theorem dynamic_squeeze {p q : α} {n m : ℕ} (hc : colOrbit F q n ≤ p) (hy : q ≤ rowOrbit F p m) :
    colOrbit F q (n + 1) ≤ F (colOrbit F q n) (rowOrbit F p m) ∧
      F (colOrbit F q n) (rowOrbit F p m) ≤ rowOrbit F p (m + 1) := by
  unfold colOrbit rowOrbit
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
  exact ⟨hF _ _ _ _ le_rfl hy, hF _ _ _ _ hc le_rfl⟩

/-- **Two-petal chains.** In `D = ↓p₁ ∪ ↓p₂`, an ascending pair `a ≤ b` inside `D` cannot have `a ≰ p₁` and `b ≰ p₂`.
So an ascending column orbit escapes (inside `D`) at most one generator row: for two generators, the all-A-side
pattern of the first-failure matrix is impossible (z3 confirms; all-B is impossible only at equal row-entry times). -/
theorem petal_chain {α : Type*} [Lattice α] {p₁ p₂ a b : α} (hab : a ≤ b) (ha : a ≤ p₁ ∨ a ≤ p₂)
    (hb : b ≤ p₁ ∨ b ≤ p₂) (ha1 : ¬ a ≤ p₁) (hb2 : ¬ b ≤ p₂) : False := by
  rcases hb with hb | hb
  · exact ha1 (hab.trans hb)
  · exact hb2 hb

end Mordor.Profile
