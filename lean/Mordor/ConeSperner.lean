import Mordor.Sperner
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# A Sperner lemma for cones: the mod-2 Hopf trace formula (log §34.3z³³)

`K` is a finite simplicial complex on a finite vertex type `V` (nonempty faces, closed under nonempty subsets) that
is a *cone*: some apex `v₀` can be added to every face. `φ` sends faces to vertices. A complete flag of a face `τ`
is an injective word `w : Fin n → V` with image `τ`; its labels are `φ` of its prefixes. If the labels of every
complete flag of every face form a face (`φ` is simplicial on flags), then

**`odd_full`: the number of pairs (face, complete flag) whose labels are exactly the face is odd.**

Proof (Hopf trace mod 2). Over `ZMod 2`, with matrices indexed by faces:
* `G σ τ` counts the complete flags of `τ` labelled exactly by `σ`; `trace G` is the count above.
* `chain`: `G * Bd = Bd * G` for the boundary `Bd`. Door counting: deleting one label of a flag of `τ` leaves `σ`
  an odd number of times iff the labels are `σ` plus one new vertex (`Sperner.removal`); inner doors pair up under
  the adjacent swap, and the last door is a complete flag of a facet.
* `cone`: `Bd * H + H * Bd = 1 + Pi` for the cone homotopy `H τ = τ ∪ {v₀}` and `Pi` the projection to the apex.
* Hence `trace G = trace (G * Pi) = 1`.
-/

namespace Mordor.ConeSperner
open Finset Classical Mordor.Sperner
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

/-- The letters of `w` at positions `≤ t`. -/
noncomputable def pre {n : ℕ} (w : Fin n → V) (t : ℕ) : Finset V :=
  (univ.filter fun s : Fin n => s.val ≤ t).image w

theorem mem_pre {n : ℕ} {w : Fin n → V} {t : ℕ} {x : V} : x ∈ pre w t ↔ ∃ s : Fin n, s.val ≤ t ∧ w s = x := by
  simp [pre]

/-- The labels of the complete flag spelled by `w`. -/
noncomputable def lab (φ : Finset V → V) {n : ℕ} (w : Fin n → V) : List V :=
  List.ofFn fun t : Fin n => φ (pre w t.val)

theorem lab_length (φ : Finset V → V) {n : ℕ} (w : Fin n → V) : (lab φ w).length = n := by simp [lab]

/-- Complete flags of `τ` of length `n`: injective words with image `τ`. -/
noncomputable def W (n : ℕ) (τ : Finset V) : Finset (Fin n → V) :=
  univ.filter fun w => Function.Injective w ∧ univ.image w = τ

theorem mem_W {n : ℕ} {τ : Finset V} {w : Fin n → V} : w ∈ W n τ ↔ Function.Injective w ∧ univ.image w = τ := by
  simp [W]

theorem card_of_mem_W {n : ℕ} {τ : Finset V} {w : Fin n → V} (h : w ∈ W n τ) : τ.card = n := by
  obtain ⟨hi, hτ⟩ := mem_W.1 h
  rw [← hτ, card_image_of_injective _ hi, card_univ, Fintype.card_fin]

/-! ### The adjacent swap -/

theorem pre_sw {n : ℕ} (w : Fin n → V) {s t : ℕ} (hst : s ≠ t) : pre (w ∘ sw n t) s = pre w s := by
  ext x
  simp only [mem_pre, Function.comp]
  constructor
  · rintro ⟨r, hr, rfl⟩; exact ⟨sw n t r, (sw_le_iff hst r).2 hr, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨sw n t r, (sw_le_iff hst (sw n t r)).1 (by rw [sw_sw]; exact hr), by simp [sw_sw]⟩

theorem lab_sw (φ : Finset V → V) {n : ℕ} (w : Fin n → V) (t : ℕ) :
    (lab φ (w ∘ sw n t)).eraseIdx t = (lab φ w).eraseIdx t := by
  apply List.ext_getElem
  · simp [List.length_eraseIdx, lab_length]
  · intro i h1 h2
    simp only [List.getElem_eraseIdx, lab, List.getElem_ofFn]
    split_ifs with hi
    · rw [pre_sw w (by omega)]
    · rw [pre_sw w (by omega)]

theorem sw_mem_W {n t : ℕ} {τ : Finset V} {w : Fin n → V} (h : w ∈ W n τ) : w ∘ sw n t ∈ W n τ := by
  obtain ⟨hi, hτ⟩ := mem_W.1 h
  refine mem_W.2 ⟨hi.comp (Equiv.injective _), ?_⟩
  rw [← hτ]; ext x; simp only [mem_image, mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨r, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨r, rfl⟩; exact ⟨sw n t r, by rw [sw_sw]⟩

theorem sw_ne_self {n t : ℕ} {w : Fin n → V} (hi : Function.Injective w) (ht : t + 1 < n) : w ∘ sw n t ≠ w := by
  intro h
  have := congrFun h ⟨t, by omega⟩
  simp only [Function.comp] at this
  have h2 := hi this
  have := congrArg Fin.val h2
  rw [sw_val ht] at this; simp at this

/-- **Inner doors pair up.** For `t + 1 < n`, deleting label `t` is invariant under the swap at `t`, so the count of
flags whose labels minus position `t` are `M` is even. -/
theorem inner_doors (φ : Finset V → V) {n t : ℕ} (ht : t + 1 < n) (τ : Finset V) (M : Multiset V) :
    (∑ w ∈ W n τ, ind ((((lab φ w).eraseIdx t : List V) : Multiset V) = M)) = 0 := by
  refine sum_involution (fun w _ => w ∘ sw n t) (fun w _ => ?_) (fun w hw _ => sw_ne_self (mem_W.1 hw).1 ht)
    (fun w hw => sw_mem_W hw) (fun w _ => ?_)
  · rw [lab_sw]; unfold ind; split_ifs <;> decide
  · funext r; simp [sw_sw]

/-! ### The last door: complete flags of facets -/

theorem pre_snoc {m : ℕ} (u : Fin m → V) (x : V) {t : ℕ} (ht : t < m) :
    pre (Fin.snoc (α := fun _ => V) u x) t = pre u t := by
  ext y
  simp only [mem_pre]
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hsm : s.val < m := by omega
    obtain ⟨s', rfl⟩ : ∃ s' : Fin m, s = Fin.castSucc s' := ⟨⟨s.val, hsm⟩, Fin.ext rfl⟩
    exact ⟨s', hs, by rw [Fin.snoc_castSucc]⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨Fin.castSucc s, hs, by rw [Fin.snoc_castSucc]⟩

theorem lab_snoc_erase (φ : Finset V → V) {m : ℕ} (u : Fin m → V) (x : V) :
    (lab φ (Fin.snoc (α := fun _ => V) u x)).eraseIdx m = lab φ u := by
  apply List.ext_getElem
  · simp [List.length_eraseIdx, lab_length]
  · intro i h1 h2
    have hi : i < m := by simpa [lab_length] using h2
    simp only [List.getElem_eraseIdx, lab, List.getElem_ofFn]
    rw [dif_pos hi, pre_snoc u x hi]

theorem snoc_mem_W {m : ℕ} {τ : Finset V} {x : V} (hx : x ∈ τ) {u : Fin m → V} (hu : u ∈ W m (τ.erase x)) :
    Fin.snoc (α := fun _ => V) u x ∈ W (m + 1) τ := by
  obtain ⟨hi, himg⟩ := mem_W.1 hu
  have hxu : ∀ r, u r ≠ x := fun r h => by
    have : u r ∈ τ.erase x := himg ▸ mem_image_of_mem u (mem_univ r)
    rw [h] at this; simp at this
  refine mem_W.2 ⟨fun a b hab => ?_, ?_⟩
  · induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast b => simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab; exact absurd hab.symm (hxu b)
    | cast a =>
      induction b using Fin.lastCases with
      | last => simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab; exact absurd hab (hxu a)
      | cast b => simp only [Fin.snoc_castSucc] at hab; rw [hi hab]
  · ext y
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨r, rfl⟩
      induction r using Fin.lastCases with
      | last => simpa using hx
      | cast r =>
        rw [Fin.snoc_castSucc]
        have : u r ∈ τ.erase x := himg ▸ mem_image_of_mem u (mem_univ r)
        exact mem_of_mem_erase this
    · intro hy
      by_cases hyx : y = x
      · exact ⟨Fin.last m, by simp [hyx]⟩
      · have : y ∈ univ.image u := himg ▸ mem_erase.2 ⟨hyx, hy⟩
        obtain ⟨r, _, rfl⟩ := mem_image.1 this
        exact ⟨Fin.castSucc r, by rw [Fin.snoc_castSucc]⟩

theorem init_mem_W {m : ℕ} {τ : Finset V} {w : Fin (m + 1) → V} (hw : w ∈ W (m + 1) τ) :
    w (Fin.last m) ∈ τ ∧ (fun r : Fin m => w (Fin.castSucc r)) ∈ W m (τ.erase (w (Fin.last m))) := by
  obtain ⟨hi, himg⟩ := mem_W.1 hw
  refine ⟨himg ▸ mem_image_of_mem w (mem_univ _), mem_W.2 ⟨fun a b h => Fin.castSucc_injective _ (hi h), ?_⟩⟩
  ext y
  simp only [mem_image, mem_univ, true_and, mem_erase]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨fun h => Fin.castSucc_lt_last r |>.ne (hi h), himg ▸ mem_image_of_mem w (mem_univ _)⟩
  · rintro ⟨hne, hy⟩
    obtain ⟨r, _, rfl⟩ := mem_image.1 (himg.symm ▸ hy : y ∈ univ.image w)
    induction r using Fin.lastCases with
    | last => exact absurd rfl hne
    | cast r => exact ⟨r, rfl⟩

/-- **The last door.** Flags of `τ` with their last label deleted are the complete flags of the facets of `τ`. -/
theorem last_door {β : Type*} [AddCommMonoid β] (φ : Finset V → V) (m : ℕ) (τ : Finset V) (f : List V → β) :
    (∑ w ∈ W (m + 1) τ, f ((lab φ w).eraseIdx m)) = ∑ x ∈ τ, ∑ u ∈ W m (τ.erase x), f (lab φ u) := by
  rw [sum_sigma']
  refine sum_bij' (fun w _ => ⟨w (Fin.last m), fun r => w (Fin.castSucc r)⟩)
    (fun p _ => Fin.snoc (α := fun _ => V) p.2 p.1) (fun w hw => ?_) (fun p hp => ?_) (fun w _ => ?_)
    (fun p _ => ?_) (fun w _ => ?_)
  · exact mem_sigma.2 (init_mem_W hw)
  · obtain ⟨hx, hu⟩ := mem_sigma.1 hp; exact snoc_mem_W hx hu
  · exact Fin.snoc_init_self (α := fun _ => V) w
  · obtain ⟨x, u⟩ := p
    simp only [Fin.snoc_last]
    congr 1
    funext r; exact Fin.snoc_castSucc (α := fun _ => V) _ _ _
  · simp only
    conv_lhs => rw [← Fin.snoc_init_self (α := fun _ => V) w]
    rw [lab_snoc_erase]; rfl

/-! ### The complex and the matrices -/

/-- `K` is a simplicial complex that is a cone with apex `v₀`. -/
structure IsCone (K : Finset (Finset V)) (v₀ : V) : Prop where
  ne : ∀ τ ∈ K, τ.Nonempty
  down : ∀ τ ∈ K, ∀ σ : Finset V, σ ⊆ τ → σ.Nonempty → σ ∈ K
  apex : ∀ τ ∈ K, insert v₀ τ ∈ K

/-- `K` is a cone with apex `v₀`, and `φ` sends complete flags to faces. -/
structure ConeData (K : Finset (Finset V)) (φ : Finset V → V) (v₀ : V) : Prop extends IsCone K v₀ where
  simp : ∀ τ ∈ K, ∀ n, ∀ w ∈ W n τ, (lab φ w).toFinset ∈ K

theorem sum_range_W {β : Type*} [AddCommMonoid β] (τ : Finset V) (F : ∀ n, (Fin n → V) → β) :
    (∑ n ∈ range (Fintype.card V + 1), ∑ w ∈ W n τ, F n w) = ∑ w ∈ W τ.card τ, F τ.card w := by
  refine sum_eq_single τ.card (fun n _ hn => sum_eq_zero fun w hw => absurd (card_of_mem_W hw) (Ne.symm hn))
    (fun h => absurd (mem_range.2 (Nat.lt_succ_of_le (card_le_univ τ))) h)

variable (K : Finset (Finset V)) (φ : Finset V → V) (v₀ : V)

/-- Flags of `τ` labelled exactly by `σ`, counted mod 2 (only `n = |τ|` contributes). -/
noncomputable def G : Matrix K K (ZMod 2) := fun σ τ =>
  ∑ n ∈ range (Fintype.card V + 1), ∑ w ∈ W n τ.1, ind (((lab φ w : List V) : Multiset V) = σ.1.val)

noncomputable def Bd : Matrix K K (ZMod 2) := fun σ τ => ind (σ.1 ⊆ τ.1 ∧ σ.1.card + 1 = τ.1.card)

noncomputable def Hc : Matrix K K (ZMod 2) := fun σ τ => ind (v₀ ∉ τ.1 ∧ σ.1 = insert v₀ τ.1)

noncomputable def Pi : Matrix K K (ZMod 2) := fun σ τ => ind (σ.1 = {v₀} ∧ τ.1.card = 1)

variable {K φ v₀}

/-- Summing a label list against the boundary: the faces one vertex above `σ`. -/
theorem bd_ind (σ : K) (l : List V) (hl : l.toFinset ∈ K) :
    (∑ ρ : K, Bd K σ ρ * ind (((l : List V) : Multiset V) = ρ.1.val)) =
      ind (∃ y, y ∉ σ.1.val ∧ ((l : List V) : Multiset V) = y ::ₘ σ.1.val) := by
  by_cases hex : ∃ y, y ∉ σ.1.val ∧ ((l : List V) : Multiset V) = y ::ₘ σ.1.val
  · obtain ⟨y, hy, he⟩ := hex
    have hyσ : y ∉ σ.1 := fun h => hy (by simpa using h)
    have hval : (insert y σ.1).val = y ::ₘ σ.1.val := Finset.insert_val_of_notMem hyσ
    have hρ₀ : insert y σ.1 ∈ K := by
      have : l.toFinset = insert y σ.1 := Finset.ext fun z => by
        rw [List.mem_toFinset, ← Multiset.mem_coe, he, Multiset.mem_cons, Finset.mem_insert]; simp
      rw [← this]; exact hl
    rw [sum_eq_single ⟨insert y σ.1, hρ₀⟩]
    · unfold Bd ind
      rw [if_pos ⟨Finset.subset_insert _ _, by rw [card_insert_of_notMem hyσ]⟩, if_pos (by rw [he, hval]),
        if_pos ⟨y, hy, he⟩, mul_one]
    · intro ρ _ hne
      unfold ind
      rw [if_neg, mul_zero]
      intro h
      exact hne (Subtype.ext (Finset.val_inj.1 (by rw [← h, he, hval])))
    · simp
  · unfold ind; rw [if_neg hex]
    refine sum_eq_zero fun ρ _ => ?_
    unfold Bd ind
    by_cases h1 : σ.1 ⊆ ρ.1 ∧ σ.1.card + 1 = ρ.1.card
    swap; · rw [if_neg h1, zero_mul]
    by_cases h2 : ((l : List V) : Multiset V) = ρ.1.val
    swap; · rw [if_neg h2, mul_zero]
    exfalso
    obtain ⟨hsub, hcard⟩ := h1
    obtain ⟨y, hy⟩ : ∃ y, ρ.1 \ σ.1 = {y} := by
      apply Finset.card_eq_one.1; rw [card_sdiff_of_subset hsub]; omega
    have hyρ : y ∈ ρ.1 := (Finset.mem_sdiff.1 (hy ▸ mem_singleton_self y)).1
    have hyσ : y ∉ σ.1 := (Finset.mem_sdiff.1 (hy ▸ mem_singleton_self y)).2
    have hρ : ρ.1 = insert y σ.1 := by
      ext z; constructor
      · intro hz; by_cases hzσ : z ∈ σ.1
        · exact mem_insert_of_mem hzσ
        · have : z ∈ ρ.1 \ σ.1 := mem_sdiff.2 ⟨hz, hzσ⟩
          rw [hy, mem_singleton] at this; rw [this]; exact mem_insert_self _ _
      · intro hz; rcases mem_insert.1 hz with rfl | hz
        · exact hyρ
        · exact hsub hz
    exact absurd ⟨y, fun h => hyσ (by simpa using h), by rw [h2, hρ, Finset.insert_val_of_notMem hyσ]⟩ hex

theorem inner_rho (hK : ConeData K φ v₀) (σ τ : K) {n : ℕ} {w : Fin n → V} (hw : w ∈ W n τ.1) :
    (∑ ρ : K, Bd K σ ρ * ind (((lab φ w : List V) : Multiset V) = ρ.1.val)) =
      ind (∃ y, y ∉ σ.1.val ∧ ((lab φ w : List V) : Multiset V) = y ::ₘ σ.1.val) :=
  bd_ind σ (lab φ w) (hK.simp τ.1 τ.2 n w hw)

/-- Summing a row against the boundary: the facets of `τ`. -/
theorem bd_right (hK : IsCone K v₀) (σ τ : K) (M : Matrix K K (ZMod 2)) (g : Finset V → ZMod 2) (hg0 : g ∅ = 0)
    (hM : ∀ ρ : K, ρ.1 ⊆ τ.1 → ρ.1.card + 1 = τ.1.card → M σ ρ = g ρ.1) :
    (∑ ρ : K, M σ ρ * Bd K ρ τ) = ∑ x ∈ τ.1, g (τ.1.erase x) := by
  have hinj : Set.InjOn (fun x => τ.1.erase x) τ.1 := fun x hx y hy hxy => by
    by_contra hne
    have : x ∈ τ.1.erase y := mem_erase.2 ⟨hne, hx⟩
    rw [← show τ.1.erase x = τ.1.erase y from hxy] at this; simp at this
  calc (∑ ρ : K, M σ ρ * Bd K ρ τ)
      = ∑ ρ : K, (if ρ.1 ⊆ τ.1 ∧ ρ.1.card + 1 = τ.1.card then g ρ.1 else 0) := by
        refine sum_congr rfl fun ρ _ => ?_
        unfold Bd ind; split_ifs with h
        · rw [mul_one]; exact hM ρ h.1 h.2
        · rw [mul_zero]
    _ = ∑ ρ ∈ K, (if ρ ⊆ τ.1 ∧ ρ.card + 1 = τ.1.card then g ρ else 0) :=
        Finset.sum_coe_sort K (fun ρ => if ρ ⊆ τ.1 ∧ ρ.card + 1 = τ.1.card then g ρ else 0)
    _ = ∑ ρ ∈ K.filter (fun ρ => ρ ⊆ τ.1 ∧ ρ.card + 1 = τ.1.card), g ρ := (sum_filter _ _).symm
    _ = ∑ ρ ∈ τ.1.image (fun x => τ.1.erase x), g ρ := by
        refine sum_subset (fun ρ hρ => ?_) (fun ρ hρ hn => ?_)
        · obtain ⟨_, hsub, hc⟩ := (mem_filter.1 hρ)
          obtain ⟨x, hx⟩ : ∃ x, τ.1 \ ρ = {x} := by
            apply Finset.card_eq_one.1; rw [card_sdiff_of_subset hsub]; omega
          have hxτ : x ∈ τ.1 := (mem_sdiff.1 (hx ▸ mem_singleton_self x)).1
          refine mem_image.2 ⟨x, hxτ, ?_⟩
          ext z; simp only [mem_erase]
          constructor
          · rintro ⟨hzx, hz⟩
            by_contra hzρ
            have : z ∈ τ.1 \ ρ := mem_sdiff.2 ⟨hz, hzρ⟩
            rw [hx, mem_singleton] at this; exact hzx this
          · intro hz
            refine ⟨fun h => ?_, hsub hz⟩
            have : x ∉ ρ := (mem_sdiff.1 (hx ▸ mem_singleton_self x)).2
            exact this (h ▸ hz)
        · obtain ⟨x, hx, rfl⟩ := mem_image.1 hρ
          have hP : τ.1.erase x ⊆ τ.1 ∧ (τ.1.erase x).card + 1 = τ.1.card :=
            ⟨erase_subset _ _, by rw [card_erase_of_mem hx]; have := card_pos.2 ⟨x, hx⟩; omega⟩
          have hnK : τ.1.erase x ∉ K := fun h => hn (mem_filter.2 ⟨h, hP⟩)
          have he : τ.1.erase x = ∅ := by
            by_contra hne
            exact hnK (hK.down τ.1 τ.2 _ (erase_subset _ _) (Finset.nonempty_iff_ne_empty.2 hne))
          rw [he, hg0]
    _ = ∑ x ∈ τ.1, g (τ.1.erase x) := sum_image hinj

theorem lab_zero (φ : Finset V → V) (u : Fin 0 → V) : lab φ u = [] := by simp [lab]

/-- **`G` is a chain map.** -/
theorem chain (hK : ConeData K φ v₀) : G K φ * Bd K = Bd K * G K φ := by
  ext σ τ
  simp only [Matrix.mul_apply]
  obtain ⟨m, hm⟩ : ∃ m, τ.1.card = m + 1 :=
    ⟨τ.1.card - 1, by have := (hK.ne τ.1 τ.2).card_pos; omega⟩
  have hσ0 : σ.1.val ≠ 0 := fun h => (hK.ne σ.1 σ.2).ne_empty (Finset.val_eq_zero.1 h)
  have hcV : m + 1 ∈ range (Fintype.card V + 1) := mem_range.2 (by have := card_le_univ τ.1; omega)
  -- the target: complete flags of the facets of τ labelled by σ
  let g : Finset V → ZMod 2 := fun ρ => ∑ u ∈ W m ρ, ind (((lab φ u : List V) : Multiset V) = σ.1.val)
  have hR : (∑ ρ : K, Bd K σ ρ * G K φ ρ τ) = ∑ x ∈ τ.1, g (τ.1.erase x) := by
    calc (∑ ρ : K, Bd K σ ρ * G K φ ρ τ)
        = ∑ n ∈ range (Fintype.card V + 1), ∑ w ∈ W n τ.1,
            ∑ ρ : K, Bd K σ ρ * ind (((lab φ w : List V) : Multiset V) = ρ.1.val) := by
          simp only [G, Finset.mul_sum]
          rw [Finset.sum_comm]; exact sum_congr rfl fun n _ => Finset.sum_comm
      _ = ∑ n ∈ range (Fintype.card V + 1), ∑ w ∈ W n τ.1,
            ind (∃ y, y ∉ σ.1.val ∧ ((lab φ w : List V) : Multiset V) = y ::ₘ σ.1.val) :=
          sum_congr rfl fun n _ => sum_congr rfl fun w hw => inner_rho hK σ τ hw
      _ = ∑ w ∈ W (m + 1) τ.1, ind (∃ y, y ∉ σ.1.val ∧ ((lab φ w : List V) : Multiset V) = y ::ₘ σ.1.val) :=
          sum_eq_single (m + 1) (fun n _ hn => sum_eq_zero fun w hw => by have := card_of_mem_W hw; omega)
            (fun h => absurd hcV h)
      _ = ∑ w ∈ W (m + 1) τ.1, ∑ j ∈ range (m + 1),
            ind ((((lab φ w).eraseIdx j : List V) : Multiset V) = σ.1.val) := by
          refine sum_congr rfl fun w _ => ?_
          have := removal (lab φ w) σ.1.val σ.1.nodup
          rw [lab_length] at this; unfold ind; convert this.symm
      _ = ∑ j ∈ range (m + 1), ∑ w ∈ W (m + 1) τ.1,
            ind ((((lab φ w).eraseIdx j : List V) : Multiset V) = σ.1.val) := Finset.sum_comm
      _ = ∑ w ∈ W (m + 1) τ.1, ind ((((lab φ w).eraseIdx m : List V) : Multiset V) = σ.1.val) := by
          rw [sum_range_succ, sum_eq_zero (fun j hj => inner_doors φ (by simp at hj; omega) τ.1 σ.1.val),
            zero_add]
      _ = ∑ x ∈ τ.1, g (τ.1.erase x) := last_door φ m τ.1 (fun l => ind (((l : List V) : Multiset V) = σ.1.val))
  have hL : (∑ ρ : K, G K φ σ ρ * Bd K ρ τ) = ∑ x ∈ τ.1, g (τ.1.erase x) := by
    have hg0 : g ∅ = 0 := sum_eq_zero fun u hu => by
      have h0 := card_of_mem_W hu; simp at h0; subst h0
      rw [lab_zero]; unfold ind; rw [if_neg]; exact fun h => hσ0 h.symm
    refine bd_right hK.toIsCone σ τ _ g hg0 fun ρ _ hc => ?_
    unfold G
    exact sum_eq_single m (fun n _ hn => sum_eq_zero fun u hu => by have := card_of_mem_W hu; omega)
      (fun h' => absurd (mem_range.2 (by have := card_le_univ τ.1; omega)) h')
  rw [hL, hR]

/-! ### The cone homotopy -/

theorem ind_t {p : Prop} (h : p) : ind p = 1 := if_pos h
theorem ind_f {p : Prop} (h : ¬ p) : ind p = 0 := if_neg h

theorem cone_entry (σ τ : Finset V) (v₀ : V) (hσ : σ.Nonempty) (hτ : τ.Nonempty) :
    ind (v₀ ∉ τ ∧ σ ⊆ insert v₀ τ ∧ σ.card + 1 = (insert v₀ τ).card) +
      ind (v₀ ∈ σ ∧ (σ.erase v₀).Nonempty ∧ σ.erase v₀ ⊆ τ ∧ (σ.erase v₀).card + 1 = τ.card) =
    ind (σ = τ) + ind (σ = {v₀} ∧ τ.card = 1) := by
  have two : (1 : ZMod 2) + 1 = 0 := by decide
  by_cases h0 : v₀ ∈ τ
  · rw [ind_f (fun h => h.1 h0), zero_add]
    by_cases hst : σ = τ
    · subst hst
      by_cases h1 : σ.card = 1
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.1 h1
        have hav : a = v₀ := by rw [ha] at h0; exact (Finset.mem_singleton.1 h0).symm
        subst hav
        have hB : ¬ (a ∈ σ ∧ (σ.erase a).Nonempty ∧ σ.erase a ⊆ σ ∧ (σ.erase a).card + 1 = σ.card) := by
          rintro ⟨-, hne, -⟩; rw [ha] at hne; simp at hne
        rw [ind_f hB, ind_t rfl, ind_t ⟨ha, h1⟩, two]
      · have hne : (σ.erase v₀).Nonempty := by
          rw [← Finset.card_pos, card_erase_of_mem h0]; have := hσ.card_pos; omega
        have hc1 : (σ.erase v₀).card + 1 = σ.card := by
          rw [card_erase_of_mem h0]; exact Nat.sub_add_cancel hσ.card_pos
        rw [ind_t ⟨h0, hne, erase_subset _ _, hc1⟩, ind_t rfl, ind_f (fun h => h1 h.2), add_zero]
    · rw [ind_f hst, zero_add]
      have hB : ¬ (v₀ ∈ σ ∧ (σ.erase v₀).Nonempty ∧ σ.erase v₀ ⊆ τ ∧ (σ.erase v₀).card + 1 = τ.card) := by
        rintro ⟨hv, -, hsub, hc⟩
        apply hst
        have hs : σ ⊆ τ := fun z hz => by
          by_cases hzv : z = v₀
          · exact hzv ▸ h0
          · exact hsub (mem_erase.2 ⟨hzv, hz⟩)
        exact Finset.eq_of_subset_of_card_le hs (by have := hσ.card_pos; rw [card_erase_of_mem hv] at hc; omega)
      have hR : ¬ (σ = {v₀} ∧ τ.card = 1) := by
        rintro ⟨rfl, hc⟩
        obtain ⟨a, ha⟩ := Finset.card_eq_one.1 hc
        rw [ha] at h0 hst; rw [Finset.mem_singleton.1 h0] at hst; exact hst rfl
      rw [ind_f hB, ind_f hR]
  · have hins : (insert v₀ τ).card = τ.card + 1 := card_insert_of_notMem h0
    by_cases hv : v₀ ∈ σ
    · have hst : σ ≠ τ := fun h => h0 (h ▸ hv)
      rw [ind_f hst, zero_add]
      have hsub : σ ⊆ insert v₀ τ ↔ σ.erase v₀ ⊆ τ := by
        constructor
        · intro h z hz
          obtain ⟨hzv, hzσ⟩ := mem_erase.1 hz
          exact (mem_insert.1 (h hzσ)).resolve_left hzv
        · intro h z hz
          by_cases hzv : z = v₀
          · exact hzv ▸ mem_insert_self _ _
          · exact mem_insert_of_mem (h (mem_erase.2 ⟨hzv, hz⟩))
      have hc : σ.card = (σ.erase v₀).card + 1 := by rw [card_erase_of_mem hv]; have := hσ.card_pos; omega
      by_cases he : σ.erase v₀ = ∅
      · have hσ1 : σ = {v₀} := by
          ext z; constructor
          · intro hz; by_contra hzv
            have : z ∈ σ.erase v₀ := mem_erase.2 ⟨by simpa using hzv, hz⟩
            rw [he] at this; simp at this
          · intro hz; rw [mem_singleton] at hz; exact hz ▸ hv
        have hB : ¬ (v₀ ∈ σ ∧ (σ.erase v₀).Nonempty ∧ σ.erase v₀ ⊆ τ ∧ (σ.erase v₀).card + 1 = τ.card) := by
          rintro ⟨-, hne, -⟩; rw [he] at hne; simp at hne
        rw [ind_f hB, add_zero]
        by_cases h1 : τ.card = 1
        · rw [ind_t (show (v₀ ∉ τ ∧ σ ⊆ insert v₀ τ ∧ σ.card + 1 = (insert v₀ τ).card) from ⟨h0, hsub.2 (by rw [he]; exact empty_subset _), by rw [hins, hc, he, h1]; rfl⟩),
            ind_t (show (σ = {v₀} ∧ τ.card = 1) from ⟨hσ1, h1⟩)]
        · rw [ind_f (show ¬ (v₀ ∉ τ ∧ σ ⊆ insert v₀ τ ∧ σ.card + 1 = (insert v₀ τ).card) from fun h => h1 (by have := h.2.2; rw [hins, hc, he] at this; simp at this; omega)),
            ind_f (show ¬ (σ = {v₀} ∧ τ.card = 1) from fun h => h1 h.2)]
      · have hne : (σ.erase v₀).Nonempty := Finset.nonempty_iff_ne_empty.2 he
        have hσ1 : σ ≠ {v₀} := fun h => he (by rw [h]; simp)
        rw [ind_f (show ¬ (σ = {v₀} ∧ τ.card = 1) from fun h => hσ1 h.1)]
        by_cases hP : σ.erase v₀ ⊆ τ ∧ (σ.erase v₀).card + 1 = τ.card
        · rw [ind_t (show (v₀ ∉ τ ∧ σ ⊆ insert v₀ τ ∧ σ.card + 1 = (insert v₀ τ).card) from ⟨h0, hsub.2 hP.1, by rw [hins, hc, hP.2]⟩),
            ind_t (show (v₀ ∈ σ ∧ (σ.erase v₀).Nonempty ∧ σ.erase v₀ ⊆ τ ∧ (σ.erase v₀).card + 1 = τ.card) from ⟨hv, hne, hP⟩), two]
        · rw [ind_f (show ¬ (v₀ ∉ τ ∧ σ ⊆ insert v₀ τ ∧ σ.card + 1 = (insert v₀ τ).card) from fun h => hP ⟨hsub.1 h.2.1, by have := h.2.2; rw [hins, hc] at this; omega⟩),
            ind_f (show ¬ (v₀ ∈ σ ∧ (σ.erase v₀).Nonempty ∧ σ.erase v₀ ⊆ τ ∧ (σ.erase v₀).card + 1 = τ.card) from fun h => hP h.2.2), add_zero]
    · have hB : ¬ (v₀ ∈ σ ∧ (σ.erase v₀).Nonempty ∧ σ.erase v₀ ⊆ τ ∧ (σ.erase v₀).card + 1 = τ.card) :=
        fun h => hv h.1
      have hR : ¬ (σ = {v₀} ∧ τ.card = 1) := fun h => hv (h.1 ▸ mem_singleton_self v₀)
      rw [ind_f hB, add_zero, ind_f hR, add_zero]
      have hiff : (v₀ ∉ τ ∧ σ ⊆ insert v₀ τ ∧ σ.card + 1 = (insert v₀ τ).card) ↔ σ = τ := by
        constructor
        · rintro ⟨-, hs, hc⟩
          have hs' : σ ⊆ τ := fun z hz => (mem_insert.1 (hs hz)).resolve_left (fun e => hv (e ▸ hz))
          exact Finset.eq_of_subset_of_card_le hs' (by omega)
        · rintro rfl; exact ⟨h0, subset_insert _ _, hins.symm⟩
      exact ite_iff hiff

theorem cone (hK : IsCone K v₀) : Bd K * Hc K v₀ + Hc K v₀ * Bd K = 1 + Pi K v₀ := by
  ext σ τ
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply]
  have h1 : (∑ ρ : K, Bd K σ ρ * Hc K v₀ ρ τ) =
      ind (v₀ ∉ τ.1 ∧ σ.1 ⊆ insert v₀ τ.1 ∧ σ.1.card + 1 = (insert v₀ τ.1).card) := by
    rw [sum_eq_single ⟨insert v₀ τ.1, hK.apex τ.1 τ.2⟩]
    · rw [ind_and, mul_comm]
      congr 1
      exact ite_iff (by simp)
    · intro ρ _ hne; unfold Hc ind; rw [if_neg, mul_zero]
      rintro ⟨-, h⟩; exact hne (Subtype.ext h)
    · simp
  have h2 : (∑ ρ : K, Hc K v₀ σ ρ * Bd K ρ τ) =
      ind (v₀ ∈ σ.1 ∧ (σ.1.erase v₀).Nonempty ∧ σ.1.erase v₀ ⊆ τ.1 ∧ (σ.1.erase v₀).card + 1 = τ.1.card) := by
    by_cases hP : v₀ ∈ σ.1 ∧ (σ.1.erase v₀).Nonempty
    · have hρK : σ.1.erase v₀ ∈ K := hK.down σ.1 σ.2 _ (erase_subset _ _) hP.2
      rw [sum_eq_single ⟨σ.1.erase v₀, hρK⟩]
      · unfold Bd Hc ind
        rw [if_pos ⟨fun h => by simp at h, (insert_erase hP.1).symm⟩, one_mul]
        exact ite_iff (by simp [hP.1, hP.2])
      · intro ρ _ hne; unfold Hc ind; rw [if_neg, zero_mul]
        rintro ⟨hv, h⟩; apply hne; apply Subtype.ext
        simp only; rw [h, erase_insert hv]
      · simp
    · rw [ind_f (fun h => hP ⟨h.1, h.2.1⟩)]
      refine sum_eq_zero fun ρ _ => ?_
      unfold Hc ind; rw [if_neg, zero_mul]
      rintro ⟨hv, h⟩
      apply hP
      refine ⟨h ▸ mem_insert_self _ _, ?_⟩
      rw [h, erase_insert hv]; exact hK.ne ρ.1 ρ.2
  rw [h1, h2, cone_entry σ.1 τ.1 v₀ (hK.ne σ.1 σ.2) (hK.ne τ.1 τ.2)]
  congr 1
  exact ite_iff Subtype.ext_iff.symm

/-! ### The trace -/

theorem W_one (v : V) : W 1 {v} = {fun _ => v} := by
  ext w
  simp only [mem_W, mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    funext r
    have : w r ∈ univ.image w := mem_image_of_mem w (mem_univ r)
    rw [h, mem_singleton] at this; exact this
  · rintro rfl
    exact ⟨fun a b _ => Subsingleton.elim a b, by ext; simp⟩

theorem G_apex (_hK : ConeData K φ v₀) (hv : {v₀} ∈ K) (τ : K) :
    G K φ τ ⟨{v₀}, hv⟩ = ind (τ.1 = {φ {v₀}}) := by
  unfold G
  rw [sum_eq_single 1 (fun n _ hn => sum_eq_zero fun w hw => by have := card_of_mem_W hw; simp at this; omega)
    (fun h => absurd (mem_range.2 (by have := Fintype.card_pos_iff.2 ⟨v₀⟩; omega)) h)]
  simp only
  rw [W_one, sum_singleton]
  have hpre : pre (fun _ : Fin 1 => v₀) 0 = {v₀} := by ext; simp [mem_pre, eq_comm]
  have : lab φ (fun _ : Fin 1 => v₀) = [φ {v₀}] := by simp [lab, hpre]
  rw [this]
  refine ite_iff ?_
  constructor
  · intro h; apply Finset.val_inj.1; rw [← h]; rfl
  · intro h; rw [h]; rfl

/-- **The mod-2 Hopf trace formula for cones.** A chain map `M` on a cone has the trace of its action on `H₀`: the
sum of the column of the apex over the vertices. -/
theorem trace_chain (hK : IsCone K v₀) (hv : {v₀} ∈ K) (M : Matrix K K (ZMod 2)) (hM : M * Bd K = Bd K * M) :
    Matrix.trace M = ∑ τ : K, ind (τ.1.card = 1) * M τ ⟨{v₀}, hv⟩ := by
  have two : ∀ x : ZMod 2, x + x = 0 := by decide
  have twoM : ∀ N : Matrix K K (ZMod 2), N + N = 0 := fun N => by
    ext i j; simp only [Matrix.add_apply, Matrix.zero_apply, two]
  have h1 : (1 : Matrix K K (ZMod 2)) = Bd K * Hc K v₀ + Hc K v₀ * Bd K + Pi K v₀ := by
    rw [cone hK, add_assoc, twoM, add_zero]
  have hcyc : Matrix.trace (M * (Bd K * Hc K v₀)) = Matrix.trace (M * (Hc K v₀ * Bd K)) := by
    rw [← Matrix.mul_assoc, hM, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  calc Matrix.trace M = Matrix.trace (M * 1) := by rw [Matrix.mul_one]
    _ = Matrix.trace (M * (Bd K * Hc K v₀)) + Matrix.trace (M * (Hc K v₀ * Bd K)) +
          Matrix.trace (M * Pi K v₀) := by
        rw [h1, Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add]
    _ = Matrix.trace (M * Pi K v₀) := by rw [hcyc, two, zero_add]
    _ = ∑ τ : K, ind (τ.1.card = 1) * M τ ⟨{v₀}, hv⟩ := by
        simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
        refine sum_congr rfl fun τ _ => ?_
        rw [sum_eq_single ⟨{v₀}, hv⟩]
        · unfold Pi; rw [mul_comm]
          exact congrArg (· * _) (ite_iff ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩)
        · intro ρ _ hne; unfold Pi; rw [ind_f (fun h => hne (Subtype.ext h.1)), mul_zero]
        · simp

theorem trace_G (hK : ConeData K φ v₀) (hv : {v₀} ∈ K) : Matrix.trace (G K φ) = 1 := by
  rw [trace_chain hK.toIsCone hv _ (chain hK)]
  have hφK : {φ {v₀}} ∈ K := by
    have := hK.simp {v₀} hv 1 (fun _ => v₀) (by rw [W_one]; exact mem_singleton_self _)
    have hpre : pre (fun _ : Fin 1 => v₀) 0 = {v₀} := by ext; simp [mem_pre, eq_comm]
    simpa [lab, hpre] using this
  rw [sum_eq_single ⟨{φ {v₀}}, hφK⟩]
  · rw [G_apex hK hv, ind_t (card_singleton _), ind_t rfl, mul_one]
  · intro τ _ hne; rw [G_apex hK hv, ind_f (fun h => hne (Subtype.ext h)), mul_zero]
  · simp

/-- **Cone Sperner lemma.** Some face of `K` has a complete flag whose labels are exactly that face. -/
theorem exists_full (hK : ConeData K φ v₀) (hv : {v₀} ∈ K) :
    ∃ τ ∈ K, ∃ n, ∃ w ∈ W n τ, ((lab φ w : List V) : Multiset V) = τ.val := by
  by_contra hno
  push_neg at hno
  have := trace_G hK hv
  rw [Matrix.trace] at this
  rw [sum_eq_zero fun τ _ => ?_] at this
  · exact absurd this (by decide)
  · unfold G
    exact sum_eq_zero fun n _ => sum_eq_zero fun w hw => ind_f (hno τ.1 τ.2 n w hw)

end Mordor.ConeSperner
