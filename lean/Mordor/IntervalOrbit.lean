import Mordor.SingletonLowerTransfer

/-!
# Orbits of invariant intervals, diagonal goodness and feeder identity (round 26, §34.3z¹⁵⁷)

Let `[l, u]` be `F`-invariant (`l ≤ F x y ≤ u` for `x, y ∈ [l, u]`) and `G = restr hinv` the restriction.
* `restr_a_le`: `(a G x).1 ≤ a F x.1`; `b_le_restr`: `b F y.1 ≤ (b G y).1`.
* `Rk_restr`: if `l ∈ R_j` then `(R^G_i).1 ⊆ R_{j+i}` — the interval orbit, started at `l`, runs inside the global
  orbit shifted by `j`. `mem_of_restr_top`: `⊤_G ∈ R^G_K ⇒ u ∈ R_{j+K}`.
* Two invariant intervals:
  - `diagPreInv`: `[⊥, c]` for a diagonal pre-fixed point `F c c ≤ c`. `diag_pre_mem`: if the orbit of `F` on
    `[⊥, c]` reaches its top within `K` steps, then `c ∈ R_K`.
  - `diagPostInv`: `[m, ⊤]` for `m ≤ F m m`. `top_mem_of_diag_post`: if `m ∈ R_j` and the orbit of `F` on `[m, ⊤]`
    reaches `⊤` within `K` steps, then `⊤ ∈ R_{j+K}`.
* `DiagGood F H` (every diagonal pre-fixed point `c` lies in `R_{h(c)}`) — exact/random evidence §34.3z¹⁵⁷.
  At `c = ⊤` it is `⊤ ∈ R_{h(⊤)}`, so `cutMaps_of_diagGood`: it is at least as strong as Cut. By `diag_pre_mem`, for
  `c < ⊤` it follows from the orbit-height property on the strictly lower lattice `[⊥, c]`, so it is available
  inside an induction on height.
* `feeder_identity_of_diagGood`: **feeder identity, index-free**: `h(m') ≤ k`, `m' ≤ t`, `t ∉ R_k`,
  `F m' t ≤ m'` ⇒ `b t = m'`. (If `b t < m'` then `b t` is diagonal pre-fixed and lower than `m'`, so it lies in
  `R_{k−1}` and puts `t` into `R_k`.)
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

variable {α : Type*} [CompleteLattice α] {F : α →o α →o α}

section Restrict
variable {l u : α} [Fact (l ≤ u)]

/-- The restriction of `F` to an invariant interval. -/
def restr (hinv : ∀ x y : Set.Icc l u, l ≤ F x.1 y.1 ∧ F x.1 y.1 ≤ u) :
    Set.Icc l u →o Set.Icc l u →o Set.Icc l u :=
  ⟨fun x => ⟨fun y => ⟨F x.1 y.1, hinv x y⟩, fun _ _ h => (F x.1).mono h⟩, fun _ _ h y => F.mono h y.1⟩

variable (hinv : ∀ x y : Set.Icc l u, l ≤ F x.1 y.1 ∧ F x.1 y.1 ≤ u)

theorem restr_a_le (x : Set.Icc l u) : (a (restr hinv) x).1 ≤ a F x.1 :=
  le_a (congrArg Subtype.val (row_a (F := restr hinv) x)).ge

theorem b_le_restr (y : Set.Icc l u) : b F y.1 ≤ (b (restr hinv) y).1 :=
  b_le (congrArg Subtype.val (col_b (F := restr hinv) y)).le

/-- **The interval orbit runs inside the shifted global orbit.** -/
theorem Rk_restr {j : ℕ} (hl : l ∈ Rk F j) : ∀ i, ∀ z ∈ Rk (restr hinv) i, z.1 ∈ Rk F (j + i)
  | 0, z, hz => Rk_down j (show z.1 ≤ (⊥ : Set.Icc l u).1 from hz) hl
  | i + 1, z, hz => by
    rw [Rk_succ] at hz
    obtain ⟨g, hzg, hg⟩ := hz
    have hzg' : z.1 ≤ g.1 := hzg
    rw [show j + (i + 1) = (j + i) + 1 by omega, Rk_succ]
    rcases hg with hgi | ⟨x, hx, hgx⟩ | hbg
    · exact ⟨g.1, hzg', Or.inl (Rk_restr hl i g hgi)⟩
    · refine ⟨a F x.1, hzg'.trans ?_, Or.inr (Or.inl ⟨x.1, Rk_restr hl i x hx, rfl⟩)⟩
      rw [hgx]; exact restr_a_le hinv x
    · exact ⟨g.1, hzg', Or.inr (Or.inr (Rk_down _ (b_le_restr hinv g) (Rk_restr hl i _ hbg)))⟩

theorem mem_of_restr_top {j K : ℕ} (hl : l ∈ Rk F j) (h : (⊤ : Set.Icc l u) ∈ Rk (restr hinv) K) :
    u ∈ Rk F (j + K) :=
  Rk_restr hinv hl K ⊤ h

end Restrict

/-- `[⊥, c]` is invariant when `F c c ≤ c`. -/
theorem diagPreInv {c : α} (hc : F c c ≤ c) :
    ∀ x y : Set.Icc (⊥ : α) c, (⊥ : α) ≤ F x.1 y.1 ∧ F x.1 y.1 ≤ c := fun x y =>
  ⟨bot_le, ((F.mono x.2.2 y.1).trans ((F c).mono y.2.2)).trans hc⟩

/-- `[m, ⊤]` is invariant when `m ≤ F m m`. -/
theorem diagPostInv {m : α} (hm : m ≤ F m m) :
    ∀ x y : Set.Icc m (⊤ : α), m ≤ F x.1 y.1 ∧ F x.1 y.1 ≤ ⊤ := fun x y =>
  ⟨hm.trans ((F.mono x.2.1 m).trans ((F x.1).mono y.2.1)), le_top⟩

/-- **Diagonal pre-fixed points enter by the length of their own interval orbit.** -/
theorem diag_pre_mem {c : α} (hc : F c c ≤ c) {K : ℕ}
    (h : haveI : Fact ((⊥ : α) ≤ c) := ⟨bot_le⟩; (⊤ : Set.Icc (⊥ : α) c) ∈ Rk (restr (diagPreInv hc)) K) :
    c ∈ Rk F K := by
  haveI : Fact ((⊥ : α) ≤ c) := ⟨bot_le⟩
  have := mem_of_restr_top (diagPreInv hc) (j := 0) (bot_mem_Rk 0) h
  rwa [Nat.zero_add] at this

/-- **Upper intervals transport the top.** -/
theorem top_mem_of_diag_post {m : α} (hm : m ≤ F m m) {j K : ℕ} (hmj : m ∈ Rk F j)
    (h : haveI : Fact (m ≤ ⊤) := ⟨le_top⟩; (⊤ : Set.Icc m (⊤ : α)) ∈ Rk (restr (diagPostInv hm)) K) :
    (⊤ : α) ∈ Rk F (j + K) := by
  haveI : Fact (m ≤ ⊤) := ⟨le_top⟩
  exact mem_of_restr_top (diagPostInv hm) hmj h

/-- Every diagonal pre-fixed point enters the orbit by its height (conjecture; see the module doc). -/
def DiagGood (F : α →o α →o α) (H : ℕ) : Prop := ∀ c, F c c ≤ c → c ∈ Rk F (height H c)

theorem cutMaps_of_diagGood {H : ℕ} (hg : DiagGood F H) : CutMaps F :=
  cutMaps_of_top_mem (hg ⊤ le_top)

/-- `DiagGood` from the orbit-height property of every interval `[⊥, c]`. -/
theorem diagGood_of_restr {H : ℕ}
    (h : ∀ c (hc : F c c ≤ c), haveI : Fact ((⊥ : α) ≤ c) := ⟨bot_le⟩;
      (⊤ : Set.Icc (⊥ : α) c) ∈ Rk (restr (diagPreInv hc)) (height H c)) : DiagGood F H :=
  fun c hc => diag_pre_mem hc (h c hc)

/-- **Feeder identity, index-free**, from diagonal goodness. -/
theorem feeder_identity_of_diagGood {H : ℕ} (hn : NoChain α (H + 1)) (hg : DiagGood F H) {k : ℕ} {m' t : α}
    (hm'k : height H m' ≤ k) (hmt : m' ≤ t) (ht : t ∉ Rk F k) (hlo : F m' t ≤ m') : b F t = m' := by
  rcases eq_or_lt_of_le (b_le hlo) with e | hlt
  · exact e
  exfalso
  have hct : b F t ≤ t := hlt.le.trans hmt
  have hdiag : F (b F t) (b F t) ≤ b F t := ((F (b F t)).mono hct).trans (col_b t).le
  have hmem := hg _ hdiag
  have h1 := height_strictMono hn hlt
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact ht (mem_succ_of_b (Rk_mono (by omega) hmem))

end Mordor.OrbitHeight
