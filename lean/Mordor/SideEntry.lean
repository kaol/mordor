import Mordor.FeederStage

/-!
# Side entry from the previous generation (round 26, §34.3z¹⁶⁴)

ChatGPT brief "Collective side-entry from the previous generation" (HEAD f5b1f94).

* Route helpers: `mem_succ_of_a` (`x ∈ R_k`, `w ≤ a x`), `mem_succ_of_le_b` (`w ≤ y`, `b y ∈ R_k`), and the exact
  unfolding `mem_succ_iff` of `R_{k+1}` into the three routes.
* `b_route_iff`: the B-route of the brief, `∃ y ≥ w, b y ∈ R_k`, is just `b w ∈ R_k` (`R_k` is a down-set, `b`
  monotone): the upper region adds nothing.
* `a_route_maximal`: the A-route can always be taken from a maximal element of `R_k` (no finiteness of `Max R_k`,
  no join of `Max R_k`; only finite edge-height, through `exists_maximal_above`).
* `side_entry_false`, `sideEntryDichotomy_iff_false`: in the singleton configuration (tight `R_{k+1}`, unique `m`,
  `m' ∈ R_k` of height `k`, `m' < w`, `m ≰ w`) no element of `(m', w]` lies in `R_{k+1}`; so the brief's
  `SideEntryDichotomy` ((A) ∨ (B) for `w`) is *equivalent to `False`* under its hypotheses: proving it is proving that
  the no-cell configuration is empty, i.e. the no-cell case of `SingletonLower` itself, not a reduction of it.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} [CompleteLattice α] {F : α →o α →o α}

/-- The A-route into `R_{k+1}`. -/
theorem mem_succ_of_a {k : ℕ} {x w : α} (hx : x ∈ Rk F k) (h : w ≤ a F x) : w ∈ Rk F (k + 1) := by
  rw [Rk_succ]; exact ⟨a F x, h, Or.inr (Or.inl ⟨x, hx, rfl⟩)⟩

/-- The B-route into `R_{k+1}`. -/
theorem mem_succ_of_le_b {k : ℕ} {w y : α} (hwy : w ≤ y) (h : b F y ∈ Rk F k) : w ∈ Rk F (k + 1) := by
  rw [Rk_succ]; exact ⟨y, hwy, Or.inr (Or.inr h)⟩

/-- **The three routes into `R_{k+1}`.** -/
theorem mem_succ_iff {k : ℕ} {w : α} :
    w ∈ Rk F (k + 1) ↔ w ∈ Rk F k ∨ (∃ x ∈ Rk F k, w ≤ a F x) ∨ b F w ∈ Rk F k := by
  constructor
  · rw [Rk_succ]
    rintro ⟨y, hwy, hy | ⟨x, hx, rfl⟩ | hb⟩
    · exact Or.inl (Rk_down k hwy hy)
    · exact Or.inr (Or.inl ⟨x, hx, hwy⟩)
    · exact Or.inr (Or.inr (Rk_down k ((b F).mono hwy) hb))
  · rintro (h | ⟨x, hx, h⟩ | h)
    · rw [Rk_succ]; exact subset_step _ h
    · exact mem_succ_of_a hx h
    · exact mem_succ_of_b h

/-- **The B-route is `b w ∈ R_k`.** -/
theorem b_route_iff {k : ℕ} {w : α} : (∃ y, w ≤ y ∧ b F y ∈ Rk F k) ↔ b F w ∈ Rk F k :=
  ⟨fun ⟨_, hwy, hb⟩ => Rk_down k ((b F).mono hwy) hb, fun h => ⟨w, le_rfl, h⟩⟩

/-- Maximal elements above any element of a set, at finite edge-height (no finiteness of the set of maximal
elements is used or implied). -/
theorem exists_maximal_above {H : ℕ} (hn : NoChain α (H + 1)) {S : Set α} :
    ∀ (n : ℕ) {x : α}, H - height H x ≤ n → x ∈ S → ∃ p, x ≤ p ∧ Maximal (· ∈ S) p
  | 0, x, hx, hS => ⟨x, le_rfl, hS, fun y hy hxy => by
      by_contra hne
      have := height_strictMono hn (lt_of_le_of_ne hxy fun e => hne (e ▸ le_rfl))
      have := height_le (H := H) y; omega⟩
  | n + 1, x, hx, hS => by
      by_cases h : ∀ y ∈ S, x ≤ y → y ≤ x
      · exact ⟨x, le_rfl, hS, fun y hy hxy => h y hy hxy⟩
      · push_neg at h
        obtain ⟨y, hy, hxy, hne⟩ := h
        have := height_strictMono hn (lt_of_le_not_ge hxy hne)
        obtain ⟨p, hyp, hp⟩ := exists_maximal_above hn n (by omega) hy
        exact ⟨p, hxy.trans hyp, hp⟩

/-- **Whole-layer form of the A-route** (the brief's `MaxLayerSideEntry` reduction): an A-route from `R_k` is an
A-route from a maximal element of `R_k`. -/
theorem a_route_maximal {H k : ℕ} (hn : NoChain α (H + 1)) {w : α} :
    (∃ x ∈ Rk F k, w ≤ a F x) ↔ ∃ p, Maximal (· ∈ Rk F k) p ∧ w ≤ a F p := by
  constructor
  · rintro ⟨x, hx, hw⟩
    obtain ⟨p, hxp, hp⟩ := exists_maximal_above hn (S := Rk F k) H (by omega) hx
    exact ⟨p, hp, hw.trans ((a F).mono hxp)⟩
  · rintro ⟨p, hp, hw⟩; exact ⟨p, hp.1, hw⟩

/-- **No side element is on time.** In the singleton configuration every element of `(m', w]` is outside `R_{k+1}`
when `m ≰ w`. -/
theorem side_entry_false {k H : ℕ} (hn : NoChain α (H + 1)) (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1)
    {m' m : α} (huniq : ∀ z ∈ Rk F (k + 1), height H z = k + 1 → z = m) (hm'k : height H m' = k)
    {w : α} (hmw : ¬ m ≤ w) {z : α} (hlt : m' < z) (hzw : z ≤ w) : z ∉ Rk F (k + 1) := fun hz =>
  hmw (above_feeder_eq hn hall huniq hm'k hz hlt ▸ hzw)

/-- **The brief's `SideEntryDichotomy` is equivalent to `False`** under its own hypotheses: (A) or (B) for `w` would
put `w` into `R_{k+1}` (`mem_succ_of_a`, `mem_succ_of_le_b`), which `side_entry_false` forbids. So the dichotomy is a
restatement of the emptiness of the no-cell configuration, not an intermediate lemma. -/
theorem sideEntryDichotomy_iff_false {k H : ℕ} (hn : NoChain α (H + 1))
    (hall : ∀ z ∈ Rk F (k + 1), height H z ≤ k + 1) {m' m : α}
    (huniq : ∀ z ∈ Rk F (k + 1), height H z = k + 1 → z = m) (hm'k : height H m' = k)
    {w : α} (hm'w : m' < w) (hmw : ¬ m ≤ w) :
    ((∃ x ∈ Rk F k, w ≤ a F x) ∨ (∃ y, w ≤ y ∧ b F y ∈ Rk F k)) ↔ False := by
  refine ⟨fun h => side_entry_false hn hall huniq hm'k hmw hm'w le_rfl ?_, False.elim⟩
  rcases h with ⟨x, hx, h⟩ | ⟨y, hy, h⟩
  · exact mem_succ_of_a hx h
  · exact mem_succ_of_le_b hy h

end Mordor.OrbitHeight
