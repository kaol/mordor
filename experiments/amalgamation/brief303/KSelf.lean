import Mordor.SelfLand

/-!
# KSelf: the k-colour form of `twoSelf` (brief run 28)

Setting: a finite lattice (`NoChain α (H+1)`), `F` monotone in both arguments, `φ = F ⊥`.

* `kSelf`: let `p` have height 2 and `y` be a landing row.  Let `S` be a set of atoms, each with Tb, each below `y`,
  each with `p` on its own descent, and suppose `S` is nonempty and **cross-closed**: every atom value `φ(X)` at a
  high column `X` that lies below `p` belongs to `S`.  Then `λ(y) = p`.
  (At the first step where row `y`'s descent leaves `↑p`, `crossAtom` from some `q ∈ S` gives a cross atom
  `t₁ = φ(X₁) ∈ S` below the next element; `crossAtom` from `t₁` gives a second one `t₂ ≠ t₁`; two atoms of `p`
  join to `p`, so the next element lies above `p` after all.)  `twoSelf` is the case `S = {q₁, q₂}`.
* `kSelf_absurd` (W0): no `m ∈ Z` of height 2 has an atom `q₀ ≤ m` with `m` on `q₀`'s descent while every atom value
  `φ(X)` (`X` high) below `m` has `m` on its descent.  In particular the colours of `C'(m)` cannot all land at `m`.
* `pairLocalS_of_nsl` (W0, conditional): if a colour `c₀ ≤ λ(c₀) = m ∈ Z` lies below the landing of every atom of
  `C'(m)`, and NSL holds at `m` (every such atom `t ≠ c₀` with `c₀ ≤ λ(t)` also has `t ≤ λ(t)`), contradiction.
* `certAtom_of_colourUniv` (W0, conditional): a colour below the landing of every colour row gives CertAtom, provided
  PairLocalS holds (stated as the hypothesis `hPLS`).
* `selfExit_not_exitColour` (W0): an atom `c ∈ Z` with `c ≤ λ(c) ∉ Z` and `φ(λ(c)) ≠ c` is the exit colour of no
  landing row whatsoever.
-/

namespace Mordor.OrbitHeight
open Mordor Mordor.Ground Mordor.GapPotential

set_option linter.unusedSectionVars false

universe u

variable {α : Type u} [CompleteLattice α] {F : α →o α →o α}

/-- **KSelf.** A nonempty cross-closed set `S` of Tb atoms below `y`, each with `p` (height 2) on its descent, makes
row `y` land at `p`. -/
theorem kSelf {H : ℕ} (hn : NoChain α (H + 1)) (hne : ∀ B, 2 < height H B → F ⊥ B ≠ ⊥)
    {p y : α} (hp2 : height H p = 2) (S : Set α)
    (hS1 : ∀ q ∈ S, height H q = 1) (hSTb : ∀ q ∈ S, ∀ B, 2 < height H B → ¬ F q B ≤ q)
    (hSy : ∀ q ∈ S, q ≤ y) (hSp : ∀ q ∈ S, ∃ i, (F q)^[i] (⊤ : α) = p) (hS0 : S.Nonempty)
    (hcl : ∀ X, 2 < height H X → F ⊥ X ≤ p → height H (F ⊥ X) = 1 → F ⊥ X ∈ S)
    {i' : ℕ} (hi' : height H ((F y)^[i'] (⊤ : α)) ≤ 2) (hmin' : ∀ j < i', 2 < height H ((F y)^[j] (⊤ : α))) :
    (F y)^[i'] (⊤ : α) = p := by
  -- one cross atom from any member of `S`, at a step where row `y` leaves `↑p`
  have cross : ∀ q ∈ S, ∀ j, p ≤ (F y)^[j] (⊤ : α) → 2 < height H ((F y)^[j] (⊤ : α)) →
      ¬ p ≤ (F y)^[j + 1] (⊤ : α) →
      ∃ X, 2 < height H X ∧ F q X = F ⊥ X ∧ height H (F q X) = 1 ∧ F q X ≤ p ∧ F q X ≠ q ∧
        F q X ≤ (F y)^[j + 1] (⊤ : α) := by
    intro q hq j hr hrh hns
    obtain ⟨i, hi⟩ := hSp q hq
    have hp2' : height H ((F q)^[i] (⊤ : α)) = 2 := hi ▸ hp2
    have hr' : (F q)^[i] (⊤ : α) ≤ (F y)^[j] (⊤ : α) := hi ▸ hr
    have hns' : ¬ (F q)^[i] (⊤ : α) ≤ (F y)^[j + 1] (⊤ : α) := hi ▸ hns
    obtain ⟨X, hX, he, h1, hle, hneq, hs⟩ := crossAtom hn hne (hS1 q hq) (hSTb q hq) hp2' (hSy q hq) hr' hrh hns'
    exact ⟨X, hX, he, h1, hi ▸ hle, hneq, hs⟩
  have hall : ∀ j, j ≤ i' → p ≤ (F y)^[j] (⊤ : α) := by
    intro j
    induction j with
    | zero => intro _; exact le_top
    | succ j ih =>
      intro hj
      have hr : p ≤ (F y)^[j] (⊤ : α) := ih (by omega)
      have hrh : 2 < height H ((F y)^[j] (⊤ : α)) := hmin' j (by omega)
      by_contra hns
      obtain ⟨q₀, hq₀⟩ := hS0
      obtain ⟨X₁, hX₁, he₁, h₁, hle₁, -, hs₁⟩ := cross q₀ hq₀ j hr hrh hns
      have ht₁S : F ⊥ X₁ ∈ S := hcl X₁ hX₁ (he₁ ▸ hle₁) (he₁ ▸ h₁)
      obtain ⟨X₂, hX₂, he₂, h₂, hle₂, hne₂, hs₂⟩ := cross (F ⊥ X₁) ht₁S j hr hrh hns
      have ht₁1 : height H (F ⊥ X₁) = 1 := he₁ ▸ h₁
      have ht₁p : F ⊥ X₁ ≤ p := he₁ ▸ hle₁
      have ht₁s : F ⊥ X₁ ≤ (F y)^[j + 1] (⊤ : α) := he₁ ▸ hs₁
      obtain ⟨hJ, -⟩ := join_of_two_atoms hn ht₁1 h₂ (Ne.symm hne₂) ht₁p hle₂ (le_of_eq hp2)
      exact hns (hJ.le.trans (sup_le ht₁s hs₂))
  exact (eq_of_le_of_height_ge hn (hall i' le_rfl) (by omega)).symm

/-- **KSelf in W0.** An element `m ∈ Z` of height 2 with an atom `q₀ ≤ m` whose descent reaches `m`, where every atom
value `φ(X)` (`X` high) below `m` has `m` on its descent: impossible (row `m` would land at `m`). -/
theorem kSelf_absurd {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    {m q₀ : α} (hm0 : F ⊥ m = ⊥) (hm2 : height H m = 2)
    (hq₀1 : height H q₀ = 1) (hq₀m : q₀ ≤ m) (hq₀p : ∃ i, (F q₀)^[i] (⊤ : α) = m)
    (hcl : ∀ X, 2 < height H X → F ⊥ X ≤ m → height H (F ⊥ X) = 1 → ∃ i, (F (F ⊥ X))^[i] (⊤ : α) = m) :
    False := by
  have hR12 : Rk F 1 ⊆ Rk F 2 := Rk_mono (F := F) (by norm_num)
  have hZT : ∀ z, F ⊥ z = ⊥ → height H z ≤ 2 := fun z hz => hk2 z (hR12 ((mem_one_iff ha).2 hz))
  have hne : ∀ B, 2 < height H B → F ⊥ B ≠ ⊥ := fun B hB h => by have := hZT B h; omega
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hmR : m ∈ Rk F 1 := (mem_one_iff ha).2 hm0
  have hbelowZ : ∀ {q : α}, q ≤ m → q ∈ Rk F 1 := fun hq =>
    (mem_one_iff ha).2 (le_bot_iff.1 (((F ⊥).mono hq).trans (le_of_eq hm0)))
  let S : Set α := {q | height H q = 1 ∧ q ≤ m ∧ ∃ i, (F q)^[i] (⊤ : α) = m}
  obtain ⟨i', hi', hmin'⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hmR))
  have heq := kSelf hn hne hm2 S (fun q hq => hq.1) (fun q hq => tb_of_tight hk2 (hbelowZ hq.2.1))
    (fun q hq => hq.2.1) (fun q hq => hq.2.2) ⟨q₀, hq₀1, hq₀m, hq₀p⟩
    (fun X hX hle h1 => ⟨h1, hle, hcl X hX hle h1⟩) hi' hmin'
  exact land_not_le hk2 hmR htop hi' hmin' (le_of_eq heq)

/-- **PairLocalS from NSL** (W0, conditional).  A colour `c₀ ∈ Z` landing at `m ∈ Z` with `c₀ ≤ m`, below the landing of
every atom value `φ(X)` (`X` high) below `m`, where every such atom `t ≠ c₀` lies below its own landing (NSL): impossible. -/
theorem pairLocalS_of_nsl {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    {c₀ : α} (hc1 : height H c₀ = 1) (hc0 : F ⊥ c₀ = ⊥)
    {i : ℕ} (hi : height H ((F c₀)^[i] (⊤ : α)) ≤ 2) (hmin : ∀ j < i, 2 < height H ((F c₀)^[j] (⊤ : α)))
    (hcl : c₀ ≤ (F c₀)^[i] (⊤ : α)) (hm0 : F ⊥ ((F c₀)^[i] (⊤ : α)) = ⊥)
    (huniv : ∀ X, 2 < height H X → F ⊥ X ≤ (F c₀)^[i] (⊤ : α) → height H (F ⊥ X) = 1 → F ⊥ X ≠ c₀ →
      ∀ k, height H ((F (F ⊥ X))^[k] (⊤ : α)) ≤ 2 → (∀ j < k, 2 < height H ((F (F ⊥ X))^[j] (⊤ : α))) →
      c₀ ≤ (F (F ⊥ X))^[k] (⊤ : α))
    (hnsl : ∀ X, 2 < height H X → F ⊥ X ≤ (F c₀)^[i] (⊤ : α) → height H (F ⊥ X) = 1 → F ⊥ X ≠ c₀ →
      ∀ k, height H ((F (F ⊥ X))^[k] (⊤ : α)) ≤ 2 → (∀ j < k, 2 < height H ((F (F ⊥ X))^[j] (⊤ : α))) →
      c₀ ≤ (F (F ⊥ X))^[k] (⊤ : α) → F ⊥ X ≤ (F (F ⊥ X))^[k] (⊤ : α)) :
    False := by
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  set m := (F c₀)^[i] (⊤ : α) with hmdef
  have hcR : c₀ ∈ Rk F 1 := (mem_one_iff ha).2 hc0
  have hmc : m ≠ c₀ := fun e => land_not_le hk2 hcR htop hi hmin (le_of_eq e)
  have hm2 : height H m = 2 := by
    have := height_strictMono hn (lt_of_le_of_ne hcl (Ne.symm hmc)); omega
  refine kSelf_absurd hn ha hk2 htop hm0 hm2 hc1 hcl ⟨i, rfl⟩ ?_
  intro X hX hle h1
  by_cases ht : F ⊥ X = c₀
  · exact ⟨i, by rw [ht]⟩
  · have htR : F ⊥ X ∈ Rk F 1 := (mem_one_iff ha).2 (le_bot_iff.1 (((F ⊥).mono hle).trans (le_of_eq hm0)))
    obtain ⟨k, hk, hmink⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ htR))
    have hc₀k := huniv X hX hle h1 ht k hk hmink
    have htk := hnsl X hX hle h1 ht k hk hmink hc₀k
    obtain ⟨hJ1, -⟩ := join_of_two_atoms hn hc1 h1 (Ne.symm ht) hc₀k htk hk
    obtain ⟨hJ2, -⟩ := join_of_two_atoms hn hc1 h1 (Ne.symm ht) hcl hle (le_of_eq hm2)
    exact ⟨k, hJ1.trans hJ2.symm⟩

/-- **Colour universal over the colour rows ⟹ CertAtom, given PairLocalS** (W0, conditional).  `hPLS` is PairLocalS in
W0 form: no colour `c₀ ≤ λ(c₀) = m ∈ Z` lies below the landing of every atom value `φ(X)` (`X` high, `φ(X) ≤ m`,
`φ(X) ≠ c₀`). -/
theorem certAtom_of_colourUniv {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    (hPLS : ∀ (c₀ : α) (i : ℕ), height H c₀ = 1 → F ⊥ c₀ = ⊥ → height H ((F c₀)^[i] (⊤ : α)) ≤ 2 →
      (∀ j < i, 2 < height H ((F c₀)^[j] (⊤ : α))) → c₀ ≤ (F c₀)^[i] (⊤ : α) → F ⊥ ((F c₀)^[i] (⊤ : α)) = ⊥ →
      (∀ X, 2 < height H X → F ⊥ X ≤ (F c₀)^[i] (⊤ : α) → height H (F ⊥ X) = 1 → F ⊥ X ≠ c₀ →
        ∀ k, height H ((F (F ⊥ X))^[k] (⊤ : α)) ≤ 2 → (∀ j < k, 2 < height H ((F (F ⊥ X))^[j] (⊤ : α))) →
        c₀ ≤ (F (F ⊥ X))^[k] (⊤ : α)) → False)
    {c₀ : α} (hc1 : height H c₀ = 1) (hc0 : F ⊥ c₀ = ⊥)
    (huniv : ∀ c, height H c = 1 → F ⊥ c = ⊥ → (∃ w, F ⊥ w = c) →
      ∀ k, height H ((F c)^[k] (⊤ : α)) ≤ 2 → (∀ j < k, 2 < height H ((F c)^[j] (⊤ : α))) → c₀ ≤ (F c)^[k] (⊤ : α))
    (hcol : ∃ w, F ⊥ w = c₀) :
    ∃ q ∈ Rk F 1, height H q = 1 ∧ ∃ k, height H ((F q)^[k] (⊤ : α)) ≤ 2 ∧
      (∀ j < k, 2 < height H ((F q)^[j] (⊤ : α))) ∧ F ⊥ ((F q)^[k] (⊤ : α)) = q := by
  have hTa : ∀ x ∈ Rk F 1, ∀ y, 2 < height H y → ¬ y ≤ F x y := fun x hx y hy hc => by
    have := hk2 y (mem_succ_of_cell (k := 1) hx le_rfl (Or.inr hc)); omega
  have hcR : c₀ ∈ Rk F 1 := (mem_one_iff ha).2 hc0
  obtain ⟨i, hi, hmin⟩ := exists_first_low ((ta_iff_lands hn _).1 (hTa _ hcR))
  have hcl : c₀ ≤ (F c₀)^[i] (⊤ : α) := huniv c₀ hc1 hc0 hcol i hi hmin
  refine certAtom_of_closed hn ha hk2 htop hc1 hc0 hi hmin hcl ?_ ?_
  · intro hpZ i' hi' hmin'
    exfalso
    refine hPLS c₀ i hc1 hc0 hi hmin hcl hpZ ?_
    intro X hX hle h1 _ k hk hmink
    have hφ0 : F ⊥ (F ⊥ X) = ⊥ := le_bot_iff.1 (((F ⊥).mono hle).trans (le_of_eq hpZ))
    exact huniv (F ⊥ X) h1 hφ0 ⟨X, rfl⟩ k hk hmink
  · intro hpZ i' hi' hmin'
    obtain ⟨-, hs1, hs0⟩ := exit_atom hn hk2 ha hcR htop hi hmin hpZ
    exact huniv _ hs1 hs0 ⟨_, rfl⟩ i' hi' hmin'

/-- **A self-exit colour is no exit colour** (W0).  If an atom `c ∈ Z` lies below its own landing `A ∉ Z` and
`φ(A) ≠ c`, then no row `y` lands at an element `P` with `φ(P) = c`. -/
theorem selfExit_not_exitColour {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    {c : α} (hc1 : height H c = 1) (hc0 : F ⊥ c = ⊥)
    {i : ℕ} (hi : height H ((F c)^[i] (⊤ : α)) ≤ 2) (hmin : ∀ j < i, 2 < height H ((F c)^[j] (⊤ : α)))
    (hcl : c ≤ (F c)^[i] (⊤ : α)) (hA0 : F ⊥ ((F c)^[i] (⊤ : α)) ≠ ⊥) (hAc : F ⊥ ((F c)^[i] (⊤ : α)) ≠ c)
    {y : α} {k : ℕ} (hk : height H ((F y)^[k] (⊤ : α)) ≤ 2) :
    F ⊥ ((F y)^[k] (⊤ : α)) ≠ c := by
  intro hPc
  have hcR : c ∈ Rk F 1 := (mem_one_iff ha).2 hc0
  set A := (F c)^[i] (⊤ : α) with hAdef
  set P := (F y)^[k] (⊤ : α) with hPdef
  obtain ⟨hA2, hs1, -⟩ := exit_atom hn hk2 ha hcR htop hi hmin hA0
  have hsA : F ⊥ A ≤ A := (land_bot_lt hk2 ha hcR htop hi hmin).le
  -- `F(⊥, P) ≤ P`: `P` is a descent element below the previous one
  have hφP : F ⊥ P ≤ P := by
    have hk0 : k ≠ 0 := land_index_pos htop hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hle : P ≤ (F y)^[k'] (⊤ : α) := by
      have := iter_antitone_of_le (F y).monotone (le_top : F y ⊤ ≤ ⊤) (Nat.le_succ k'); exact this
    have hP : P = F y ((F y)^[k'] (⊤ : α)) := by rw [hPdef, Function.iterate_succ_apply']
    calc F ⊥ P ≤ F ⊥ ((F y)^[k'] (⊤ : α)) := (F ⊥).mono hle
      _ ≤ F y ((F y)^[k'] (⊤ : α)) := (F.mono bot_le) _
      _ = P := hP.symm
  have hcP : c ≤ P := hPc ▸ hφP
  obtain ⟨hJ, -⟩ := join_of_two_atoms hn hc1 hs1 (Ne.symm hAc) hcl hsA (le_of_eq hA2)
  have hcap : A ≤ F ⊥ A ⊔ c := hJ.le.trans (sup_le le_sup_right le_sup_left)
  have hle := land_capture hcP hcap
  have hA2' : height H A = 2 := hA2
  have hk' : height H P ≤ 2 := hk
  have heq : A = P := eq_of_le_of_height_ge hn hle (by omega)
  exact hAc (by rw [heq]; exact hPc)

/-- **Exit colour is universal among the landings that meet an exit** (W0).  If row `a ∈ Z` lands at `A ∉ Z` and some
atom `g` lies below both `A` and the landing of a row `y` (any row, any descent index), then the exit colour
`φ(A)` lies below that landing too.  (If `g ≠ φ(A)`, `A = g ⊔ φ(A)` is captured.)  So, when the colour-row landings
pairwise share a colour and one colour row exits, its exit colour is universal over the colour rows: the open case of
Helly2 is the one where every colour row lands in `Z`. -/
theorem exitColour_univ_of_meet {H : ℕ} (hn : NoChain α (H + 1)) (ha : a F ⊥ = ⊥)
    (hk2 : ∀ z ∈ Rk F 2, height H z ≤ 2) (htop : 2 < height H (⊤ : α))
    {x : α} (hx0 : F ⊥ x = ⊥) {i : ℕ} (hi : height H ((F x)^[i] (⊤ : α)) ≤ 2)
    (hmin : ∀ j < i, 2 < height H ((F x)^[j] (⊤ : α))) (hA0 : F ⊥ ((F x)^[i] (⊤ : α)) ≠ ⊥)
    {y g : α} {k : ℕ} (hg1 : height H g = 1) (hgA : g ≤ (F x)^[i] (⊤ : α)) (hgy : g ≤ (F y)^[k] (⊤ : α)) :
    F ⊥ ((F x)^[i] (⊤ : α)) ≤ (F y)^[k] (⊤ : α) := by
  have hxR : x ∈ Rk F 1 := (mem_one_iff ha).2 hx0
  set A := (F x)^[i] (⊤ : α) with hAdef
  obtain ⟨hA2, hs1, -⟩ := exit_atom hn hk2 ha hxR htop hi hmin hA0
  have hsA : F ⊥ A ≤ A := (land_bot_lt hk2 ha hxR htop hi hmin).le
  by_cases hgs : g = F ⊥ A
  · exact hgs ▸ hgy
  · obtain ⟨hJ, -⟩ := join_of_two_atoms hn hg1 hs1 hgs hgA hsA (le_of_eq hA2)
    have hcap : A ≤ F ⊥ A ⊔ g := hJ.le.trans (sup_le le_sup_right le_sup_left)
    exact hsA.trans (land_capture hgy hcap)

end Mordor.OrbitHeight
