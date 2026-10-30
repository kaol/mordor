import Mordor.CLL
import Mathlib.Order.Preorder.Chain

/-!
# The double-cone lemma and the Cut Lemma on finite posets (log §34.3z³⁶–³⁷)

`D` is a finite poset with a bottom, `C` a finite poset with a top. A *cell* is a pair `(ρ, σ)` of nonempty chains of
`D` and `C`, ordered by `ρ ⊇ ρ'`, `σ ⊆ σ'`. A labelling sends cells monotonically into the ordinal sum `D ⊕ C`, with
W1 (a `D`-label is not below all of `ρ`) and W2 (a `C`-label is not above all of `σ`).
**`dcl`: no such labelling exists.** **`cut_finite`: the Cut Lemma holds on every finite bounded poset.**

Proof (relative Lefschetz, mod 2). `K` is the complex of chains of `D ⊕ (C ∖ ⊤)`, a cone with apex `⊥`. A face `τ`
is subdivided by the *words* over `τ ∪ {⊤}`, and if `⊥ ∉ τ` also over `τ ∪ {⊥}`: injective words with a `C`-letter
first and a `D`-letter last. Cut `t` of a word is the cell (`D`-letters after `t`, `C`-letters up to `t`); its label
is the labelling there. Over `ZMod 2`:
* `door`: for words over any alphabet `A`, deleting one label is, up to adjacent swaps, deleting the second letter
  (a `D`-letter) or the second-to-last letter (a `C`-letter): the words over the sets `A ∖ x`.
* `chain`: hence `G * Bd = Bd * G` for `G σ τ` = words of `τ` labelled exactly `σ`. The two alphabets of a face
  share the corner words over `τ` itself; those cancel, except at a cone face, where they are the base face.
* `ConeSperner.trace_chain`: `trace G = 1` (the apex `{⊥}` has the single word `⊤⊥`).
* A word labelled exactly by its face violates W1 at its first cut (alphabet `τ ∪ {⊤}`) or W2 at its last cut
  (alphabet `τ ∪ {⊥}`), so `trace G = 0`.
-/

namespace Mordor.RelativeCut
open Finset Classical Mordor.ConeSperner
open Mordor.Sperner (ind sw sw_val sw_sw removal)
set_option linter.unusedSectionVars false

variable {D C : Type*} [Fintype D] [Fintype C]

/-- The decidable equality `ConeSperner` uses. -/
noncomputable local instance : DecidableEq (D ⊕ C) := fun a b => Classical.propDecidable (a = b)

local notation "V" => D ⊕ C

/-- The `D`-part and the `C`-part of a set of letters. -/
noncomputable def Dp (S : Finset (D ⊕ C)) : Finset D := univ.filter fun d => Sum.inl d ∈ S
noncomputable def Cp (S : Finset (D ⊕ C)) : Finset C := univ.filter fun c => Sum.inr c ∈ S

theorem mem_Dp {S : Finset (D ⊕ C)} {d : D} : d ∈ Dp S ↔ Sum.inl d ∈ S := by simp [Dp]
theorem mem_Cp {S : Finset (D ⊕ C)} {c : C} : c ∈ Cp S ↔ Sum.inr c ∈ S := by simp [Cp]

theorem Dp_mono {S T : Finset (D ⊕ C)} (h : S ⊆ T) : Dp S ⊆ Dp T := fun _ hd => mem_Dp.2 (h (mem_Dp.1 hd))
theorem Cp_mono {S T : Finset (D ⊕ C)} (h : S ⊆ T) : Cp S ⊆ Cp T := fun _ hc => mem_Cp.2 (h (mem_Cp.1 hc))

theorem Cp_insert_inl (S : Finset (D ⊕ C)) (d : D) : Cp (insert (Sum.inl d) S) = Cp S := by
  ext c; simp [mem_Cp]

theorem Dp_erase_inr (S : Finset (D ⊕ C)) (c : C) : Dp (S.erase (Sum.inr c)) = Dp S := by
  ext d; simp [mem_Dp]

/-- The letters after position `t`. -/
noncomputable def post {n : ℕ} (u : Fin n → D ⊕ C) (t : ℕ) : Finset (D ⊕ C) := univ.image u \ pre u t

theorem mem_post {n : ℕ} {u : Fin n → D ⊕ C} (hu : Function.Injective u) {t : ℕ} {x : D ⊕ C} :
    x ∈ post u t ↔ ∃ s : Fin n, t < s.val ∧ u s = x := by
  simp only [post, mem_sdiff, mem_image, mem_univ, true_and, mem_pre]
  constructor
  · rintro ⟨⟨s, rfl⟩, h⟩
    exact ⟨s, by by_contra h'; exact h ⟨s, by omega, rfl⟩, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, rfl⟩, fun ⟨r, hr, he⟩ => by have := hu he; subst this; omega⟩

/-- A `C`-letter first and a `D`-letter last. -/
def Ends {n : ℕ} (u : Fin n → D ⊕ C) : Prop :=
  ∀ i : Fin n, (i.val = 0 → ∃ c, u i = Sum.inr c) ∧ (i.val + 1 = n → ∃ d, u i = Sum.inl d)

theorem ends_iff {k : ℕ} (u : Fin (k + 2) → D ⊕ C) :
    Ends u ↔ (∃ c, u 0 = Sum.inr c) ∧ ∃ d, u (Fin.last _) = Sum.inl d := by
  constructor
  · intro h; exact ⟨(h 0).1 rfl, (h (Fin.last _)).2 rfl⟩
  · rintro ⟨h0, h1⟩ i
    refine ⟨fun hi => ?_, fun hi => ?_⟩
    · have : i = 0 := Fin.ext hi; rw [this]; exact h0
    · have : i = Fin.last _ := Fin.ext (by simp; omega); rw [this]; exact h1

/-- The label of cut `t`, and the labels of a word. -/
noncomputable def cl (z : Finset D → Finset C → D ⊕ C) {n : ℕ} (u : Fin n → D ⊕ C) (t : ℕ) : D ⊕ C :=
  z (Dp (post u t)) (Cp (pre u t))

noncomputable def labw (z : Finset D → Finset C → D ⊕ C) {n : ℕ} (u : Fin n → D ⊕ C) : List (D ⊕ C) :=
  List.ofFn fun t : Fin (n - 1) => cl z u t.val

theorem labw_length (z : Finset D → Finset C → D ⊕ C) {n : ℕ} (u : Fin n → D ⊕ C) :
    (labw z u).length = n - 1 := by simp [labw]

theorem mem_labw {z : Finset D → Finset C → D ⊕ C} {n : ℕ} {u : Fin n → D ⊕ C} {x : D ⊕ C} :
    x ∈ labw z u ↔ ∃ t : ℕ, t + 1 < n ∧ cl z u t = x := by
  simp only [labw, List.mem_ofFn]
  constructor
  · rintro ⟨t, rfl⟩; exact ⟨t.val, by omega, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨⟨t, by omega⟩, rfl⟩

/-! ### Adjacent swaps -/

theorem image_sw {n t : ℕ} (u : Fin n → D ⊕ C) : univ.image (u ∘ sw n t) = univ.image u := by
  ext x; simp only [mem_image, mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨r, rfl⟩; exact ⟨_, rfl⟩
  · rintro ⟨r, rfl⟩; exact ⟨sw n t r, by rw [sw_sw]⟩

theorem cl_sw (z : Finset D → Finset C → D ⊕ C) {n : ℕ} (u : Fin n → D ⊕ C) {s t : ℕ} (hst : s ≠ t) :
    cl z (u ∘ sw n t) s = cl z u s := by
  simp only [cl, post, image_sw, pre_sw u hst]

theorem labw_sw (z : Finset D → Finset C → D ⊕ C) {n : ℕ} (u : Fin n → D ⊕ C) (t : ℕ) :
    (labw z (u ∘ sw n t)).eraseIdx t = (labw z u).eraseIdx t := by
  apply List.ext_getElem
  · simp [List.length_eraseIdx, labw_length]
  · intro i h1 h2
    simp only [List.getElem_eraseIdx, labw, List.getElem_ofFn]
    split_ifs with hi
    · rw [cl_sw z u (by omega)]
    · rw [cl_sw z u (by omega)]

theorem sw_fix {n t : ℕ} (ht : t + 1 < n) (i : Fin n) (h1 : i.val ≠ t) (h2 : i.val ≠ t + 1) : sw n t i = i :=
  Fin.ext (by rw [sw_val ht]; simp [h1, h2])

theorem sw_at {n t : ℕ} (ht : t + 1 < n) (i : Fin n) (h : i.val = t) : (sw n t i).val = t + 1 := by
  rw [sw_val ht]; simp [h]

theorem sw_at' {n t : ℕ} (ht : t + 1 < n) (i : Fin n) (h : i.val = t + 1) : (sw n t i).val = t := by
  rw [sw_val ht]; simp [h]

/-- Swap pairs cancel mod 2. -/
theorem sum_sw_zero {n t : ℕ} (ht : t + 1 < n) (S : Finset (Fin n → D ⊕ C)) (hS : ∀ u ∈ S, u ∘ sw n t ∈ S)
    (hi : ∀ u ∈ S, Function.Injective u) (f : (Fin n → D ⊕ C) → ZMod 2)
    (hf : ∀ u ∈ S, f (u ∘ sw n t) = f u) : ∑ u ∈ S, f u = 0 := by
  have two : ∀ x : ZMod 2, x + x = 0 := by decide
  refine sum_involution (fun u _ => u ∘ sw n t) (fun u hu => ?_) (fun u hu _ => sw_ne_self (hi u hu) ht)
    (fun u hu => hS u hu) (fun u _ => ?_)
  · rw [hf u hu]; exact two _
  · funext r; simp [sw_sw]

/-! ### Deleting and inserting a letter -/

theorem val_succAbove {k : ℕ} (p : Fin (k + 1)) (s : Fin k) :
    (p.succAbove s).val = if s.val < p.val then s.val else s.val + 1 := by
  by_cases h : s.val < p.val
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]; rfl
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (by simp [Fin.le_def]; omega)]; rfl

theorem pre_del_lt {k : ℕ} (u : Fin (k + 1) → D ⊕ C) (p : Fin (k + 1)) {i : ℕ} (hi : i < p.val) :
    pre (Fin.removeNth p u) i = pre u i := by
  ext x
  simp only [mem_pre, Fin.removeNth]
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨p.succAbove s, ?_, rfl⟩
    rw [val_succAbove]; split_ifs <;> omega
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨s.val, by omega⟩, hs, congrArg u (Fin.ext ?_)⟩
    rw [val_succAbove]; simp only; split_ifs <;> omega

theorem pre_del_ge {k : ℕ} (u : Fin (k + 1) → D ⊕ C) (p : Fin (k + 1)) {i : ℕ} (hi : p.val ≤ i + 1) :
    insert (u p) (pre (Fin.removeNth p u) i) = pre u (i + 1) := by
  ext x
  simp only [mem_insert, mem_pre]
  constructor
  · rintro (rfl | ⟨s, hs, rfl⟩)
    · exact ⟨p, hi, rfl⟩
    · refine ⟨p.succAbove s, ?_, rfl⟩
      rw [val_succAbove]; split_ifs <;> omega
  · rintro ⟨s, hs, rfl⟩
    by_cases hsp : s = p
    · left; rw [hsp]
    · right
      obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hsp
      refine ⟨r, ?_, by show u (p.succAbove r) = u s; rw [hr]⟩
      have := congrArg Fin.val hr
      rw [val_succAbove] at this; split_ifs at this <;> omega

theorem image_del {k : ℕ} {u : Fin (k + 1) → D ⊕ C} (hu : Function.Injective u) (p : Fin (k + 1)) :
    univ.image (Fin.removeNth p u) = (univ.image u).erase (u p) := by
  ext x
  simp only [mem_image, mem_univ, true_and, mem_erase, Fin.removeNth]
  constructor
  · rintro ⟨s, rfl⟩; exact ⟨fun h => Fin.succAbove_ne p s (hu h), _, rfl⟩
  · rintro ⟨hne, s, rfl⟩
    have hsp : s ≠ p := fun h => hne (h ▸ rfl)
    obtain ⟨r, hr⟩ := Fin.exists_succAbove_eq hsp
    exact ⟨r, by rw [hr]⟩

theorem del_mem_W {k : ℕ} {A : Finset (D ⊕ C)} {u : Fin (k + 1) → D ⊕ C} (hu : u ∈ W (k + 1) A)
    (p : Fin (k + 1)) : u p ∈ A ∧ Fin.removeNth p u ∈ W k (A.erase (u p)) := by
  obtain ⟨hi, himg⟩ := mem_W.1 hu
  refine ⟨himg ▸ mem_image_of_mem u (mem_univ p), mem_W.2 ⟨fun a b h => ?_, by rw [image_del hi, himg]⟩⟩
  exact Fin.succAbove_right_injective (hi h)

theorem ins_mem_W {k : ℕ} {A : Finset (D ⊕ C)} {x : D ⊕ C} (hx : x ∈ A) {v : Fin k → D ⊕ C}
    (hv : v ∈ W k (A.erase x)) (p : Fin (k + 1)) : Fin.insertNth p x v ∈ W (k + 1) A := by
  obtain ⟨hi, himg⟩ := mem_W.1 hv
  have hvx : ∀ r, v r ≠ x := fun r h => by
    have : v r ∈ A.erase x := himg ▸ mem_image_of_mem v (mem_univ r)
    rw [h] at this; simp at this
  refine mem_W.2 ⟨fun a b hab => ?_, ?_⟩
  · rcases Fin.eq_self_or_eq_succAbove p a with ha | ⟨a', rfl⟩ <;>
      rcases Fin.eq_self_or_eq_succAbove p b with hb | ⟨b', rfl⟩
    · rw [ha, hb]
    · rw [ha] at hab; simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hab
      exact absurd hab.symm (hvx b')
    · rw [hb] at hab; simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove] at hab
      exact absurd hab (hvx a')
    · simp only [Fin.insertNth_apply_succAbove] at hab; rw [hi hab]
  · ext y
    simp only [mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨r, rfl⟩
      rcases Fin.eq_self_or_eq_succAbove p r with rfl | ⟨r', rfl⟩
      · simpa using hx
      · rw [Fin.insertNth_apply_succAbove]
        exact mem_of_mem_erase (himg ▸ mem_image_of_mem v (mem_univ r'))
    · intro hy
      by_cases hyx : y = x
      · exact ⟨p, by simp [hyx]⟩
      · have : y ∈ univ.image v := himg ▸ mem_erase.2 ⟨hyx, hy⟩
        obtain ⟨r, _, rfl⟩ := mem_image.1 this
        exact ⟨p.succAbove r, by rw [Fin.insertNth_apply_succAbove]⟩

/-- **Doors at a fixed position.** Words with the letter at `p` deleted are the words over the sets `A ∖ x`. -/
theorem door_bij {β : Type*} [AddCommMonoid β] {k : ℕ} (p : Fin (k + 1)) (A : Finset (D ⊕ C))
    (f : D ⊕ C → (Fin k → D ⊕ C) → β) :
    (∑ u ∈ W (k + 1) A, f (u p) (Fin.removeNth p u)) = ∑ x ∈ A, ∑ v ∈ W k (A.erase x), f x v := by
  rw [sum_sigma']
  refine sum_bij' (fun u _ => ⟨u p, Fin.removeNth p u⟩) (fun q _ => Fin.insertNth p q.1 q.2)
    (fun u hu => mem_sigma.2 (del_mem_W hu p)) (fun q hq => ?_) (fun u _ => Fin.insertNth_self_removeNth p u)
    (fun q _ => ?_) (fun u _ => rfl)
  · obtain ⟨hx, hv⟩ := mem_sigma.1 hq; exact ins_mem_W hx hv p
  · obtain ⟨x, v⟩ := q; simp [Fin.removeNth_insertNth]

/-- The first door: deleting the second letter, a `D`-letter. -/
theorem labw_first (z : Finset D → Finset C → D ⊕ C) {m : ℕ} (u : Fin (m + 3) → D ⊕ C)
    (hu : Function.Injective u) {d : D} (hd : u 1 = Sum.inl d) :
    (labw z u).eraseIdx 0 = labw z (Fin.removeNth 1 u) := by
  apply List.ext_getElem
  · simp [List.length_eraseIdx, labw_length]
  · intro i h1 h2
    simp only [List.getElem_eraseIdx, labw, List.getElem_ofFn]
    rw [dif_neg (by omega)]
    simp only [List.getElem_ofFn, cl]
    have hpre := pre_del_ge u 1 (i := i) (by simp)
    congr 1
    · congr 1
      simp only [post, image_del hu, ← hpre]
      ext x; simp only [mem_sdiff, mem_insert, mem_erase]; tauto
    · rw [← hpre, hd, Cp_insert_inl]

/-- The last door: deleting the second-to-last letter, a `C`-letter. -/
theorem labw_last (z : Finset D → Finset C → D ⊕ C) {m : ℕ} (u : Fin (m + 3) → D ⊕ C)
    (hu : Function.Injective u) {c : C} (hc : u ⟨m + 1, by omega⟩ = Sum.inr c) :
    (labw z u).eraseIdx (m + 1) = labw z (Fin.removeNth ⟨m + 1, by omega⟩ u) := by
  apply List.ext_getElem
  · simp [List.length_eraseIdx, labw_length]
  · intro i h1 h2
    have hi : i < m + 1 := by simpa [labw_length] using h2
    simp only [List.getElem_eraseIdx, labw, List.getElem_ofFn]
    rw [dif_pos hi]
    simp only [List.getElem_ofFn, cl]
    have hpre := pre_del_lt u ⟨m + 1, by omega⟩ (i := i) hi
    have : post (Fin.removeNth ⟨m + 1, by omega⟩ u) i = (post u i).erase (Sum.inr c) := by
      simp only [post, image_del hu, hpre, hc]
      ext x; simp only [mem_sdiff, mem_erase]; tauto
    rw [hpre, this, Dp_erase_inr]

/-! ### The door lemma -/

variable (z : Finset D → Finset C → D ⊕ C)

/-- Words over `B` labelled exactly `M`. -/
noncomputable def S (M : Multiset (D ⊕ C)) (B : Finset (D ⊕ C)) : ZMod 2 :=
  ∑ u ∈ W B.card B, if Ends u then ind (((labw z u : List (D ⊕ C)) : Multiset (D ⊕ C)) = M) else 0

variable {z}

theorem S_small {M : Multiset (D ⊕ C)} (hM : M ≠ 0) {B : Finset (D ⊕ C)} (hB : B.card ≤ 1) : S z M B = 0 := by
  refine sum_eq_zero fun u _ => ?_
  split_ifs
  · have : labw z u = [] := List.eq_nil_of_length_eq_zero (by rw [labw_length]; omega)
    rw [this]; exact ind_f (fun h => hM h.symm)
  · rfl

theorem S_card {M : Multiset (D ⊕ C)} {B : Finset (D ⊕ C)} {k : ℕ} (hk : B.card = k) :
    S z M B = ∑ u ∈ W k B, if Ends u then ind (((labw z u : List (D ⊕ C)) : Multiset (D ⊕ C)) = M) else 0 := by
  rw [S, hk]

theorem two_z : ∀ x : ZMod 2, x + x = 0 := by decide

/-- The indicator that deleting label `j` of `u` leaves `M`. -/
noncomputable def E (M : Multiset (D ⊕ C)) {n : ℕ} (u : Fin n → D ⊕ C) (j : ℕ) : ZMod 2 :=
  ind ((((labw z u).eraseIdx j : List (D ⊕ C)) : Multiset (D ⊕ C)) = M)

/-- The indicator that `v` (with a `D`-letter `x`, resp. a `C`-letter) is a word labelled `M`. -/
noncomputable def Fl (M : Multiset (D ⊕ C)) {k : ℕ} (x : D ⊕ C) (v : Fin k → D ⊕ C) : ZMod 2 :=
  if (∃ d, x = Sum.inl d) ∧ Ends v then ind (((labw z v : List (D ⊕ C)) : Multiset (D ⊕ C)) = M) else 0
noncomputable def Fr (M : Multiset (D ⊕ C)) {k : ℕ} (x : D ⊕ C) (v : Fin k → D ⊕ C) : ZMod 2 :=
  if (∃ c, x = Sum.inr c) ∧ Ends v then ind (((labw z v : List (D ⊕ C)) : Multiset (D ⊕ C)) = M) else 0

theorem ends_del {m : ℕ} (u : Fin (m + 3) → D ⊕ C) (p : Fin (m + 3)) (h0 : 0 < p.val) (h1 : p.val < m + 2) :
    Ends u ↔ Ends (Fin.removeNth p u) := by
  rw [ends_iff, ends_iff]
  have e0 : Fin.removeNth p u 0 = u 0 := by
    show u (p.succAbove 0) = u 0
    congr 1; apply Fin.ext; rw [val_succAbove, Fin.val_zero, Fin.val_zero, if_pos h0]
  have el : Fin.removeNth p u (Fin.last _) = u (Fin.last _) := by
    show u (p.succAbove (Fin.last _)) = u (Fin.last _)
    congr 1; apply Fin.ext; rw [val_succAbove, Fin.val_last, Fin.val_last, if_neg (by omega)]
  rw [e0, el]

/-- **The door lemma.** -/
theorem door {M : Multiset (D ⊕ C)} (hM : M ≠ 0) (A : Finset (D ⊕ C)) :
    (∑ u ∈ W A.card A, if Ends u then ∑ j ∈ range (A.card - 1), E (z := z) M u j else 0) =
      ∑ x ∈ A, S z M (A.erase x) := by
  by_cases hA : A.card ≤ 2
  · rw [sum_eq_zero fun u _ => ?_, sum_eq_zero fun x hx => S_small hM ?_]
    · rw [card_erase_of_mem hx]; omega
    · split_ifs
      · refine sum_eq_zero fun j hj => ind_f fun h => hM ?_
        have : (labw z u).eraseIdx j = [] := List.eq_nil_of_length_eq_zero (by
          rw [List.length_eraseIdx, labw_length]; simp at hj; split_ifs; omega)
        rw [← h, this]; rfl
      · rfl
  obtain ⟨m, hm⟩ : ∃ m, A.card = m + 3 := ⟨A.card - 3, by omega⟩
  have hR : ∀ x ∈ A, S z M (A.erase x) = ∑ v ∈ W (m + 2) (A.erase x),
      if Ends v then ind (((labw z v : List (D ⊕ C)) : Multiset (D ⊕ C)) = M) else 0 :=
    fun x hx => S_card (by rw [card_erase_of_mem hx, hm]; rfl)
  rw [sum_congr rfl hR, hm]
  set WA := (W (m + 3) A).filter Ends with hWAdef
  have hWA : ∀ u ∈ WA, Function.Injective u ∧ Ends u := fun u hu =>
    ⟨(mem_W.1 (mem_filter.1 hu).1).1, (mem_filter.1 hu).2⟩
  have hEsw : ∀ (u : Fin (m + 3) → D ⊕ C) (t : ℕ), E (z := z) M (u ∘ sw (m + 3) t) t = E (z := z) M u t :=
    fun u t => by unfold E; rw [labw_sw]
  have hfst : ∑ u ∈ WA, E (z := z) M u 0 = ∑ x ∈ A, ∑ v ∈ W (m + 2) (A.erase x), Fl (z := z) M x v := by
    rw [← sum_filter_add_sum_filter_not WA (fun u => ∃ c, u 1 = Sum.inr c)]
    rw [sum_sw_zero (t := 0) (by omega) _ (fun u hu => ?_) (fun u hu => (hWA u (mem_filter.1 hu).1).1) _
      (fun u _ => hEsw u 0), zero_add]
    · refine Eq.trans ?_ (door_bij 1 A (Fl (z := z) M))
      rw [hWAdef, filter_filter, sum_filter]
      refine sum_congr rfl fun u hu => ?_
      have hi := (mem_W.1 hu).1
      have hE := ends_del u 1 (by simp) (by simp)
      unfold Fl
      rcases hx : u 1 with d | c
      · rw [if_congr (show (Ends u ∧ ¬∃ c, (Sum.inl d : D ⊕ C) = Sum.inr c) ↔ Ends u by simp) rfl rfl,
          if_congr (show ((∃ d', (Sum.inl d : D ⊕ C) = Sum.inl d') ∧ Ends (Fin.removeNth 1 u)) ↔ Ends u by
            rw [hE]; simp) rfl rfl]
        split_ifs
        · unfold E; rw [labw_first z u hi hx]
        · rfl
      · rw [if_neg (by simp), if_neg (by simp)]
    · obtain ⟨hu, ⟨c, hc⟩⟩ := mem_filter.1 hu
      obtain ⟨hW, he⟩ := mem_filter.1 hu
      refine mem_filter.2 ⟨mem_filter.2 ⟨sw_mem_W hW, fun i => ⟨fun h0 => ?_, fun h1 => ?_⟩⟩, ?_⟩
      · have : (sw (m + 3) 0 i).val = 1 := sw_at (by omega) i h0
        rw [Function.comp, show sw (m + 3) 0 i = 1 from Fin.ext this]; exact ⟨c, hc⟩
      · rw [Function.comp, sw_fix (by omega) i (by omega) (by omega)]; exact (he i).2 h1
      · have : (sw (m + 3) 0 1).val = 0 := sw_at' (by omega) 1 rfl
        rw [Function.comp, show sw (m + 3) 0 1 = 0 from Fin.ext this]; exact (he 0).1 rfl
  have hlst : ∑ u ∈ WA, E (z := z) M u (m + 1) =
      ∑ x ∈ A, ∑ v ∈ W (m + 2) (A.erase x), Fr (z := z) M x v := by
    rw [← sum_filter_add_sum_filter_not WA (fun u => ∃ d, u ⟨m + 1, by omega⟩ = Sum.inl d)]
    rw [sum_sw_zero (t := m + 1) (by omega) _ (fun u hu => ?_) (fun u hu => (hWA u (mem_filter.1 hu).1).1) _
      (fun u _ => hEsw u (m + 1)), zero_add]
    · refine Eq.trans ?_ (door_bij ⟨m + 1, by omega⟩ A (Fr (z := z) M))
      rw [hWAdef, filter_filter, sum_filter]
      refine sum_congr rfl fun u hu => ?_
      have hi := (mem_W.1 hu).1
      have hE := ends_del u ⟨m + 1, by omega⟩ (by simp) (by simp)
      unfold Fr
      rcases hx : u ⟨m + 1, by omega⟩ with d | c
      · rw [if_neg (by simp), if_neg (by simp)]
      · rw [if_congr (show (Ends u ∧ ¬∃ d, (Sum.inr c : D ⊕ C) = Sum.inl d) ↔ Ends u by simp) rfl rfl,
          if_congr (show ((∃ c', (Sum.inr c : D ⊕ C) = Sum.inr c') ∧
            Ends (Fin.removeNth ⟨m + 1, by omega⟩ u)) ↔ Ends u by rw [hE]; simp) rfl rfl]
        split_ifs
        · unfold E; rw [labw_last z u hi hx]
        · rfl
    · obtain ⟨hu, ⟨d, hd⟩⟩ := mem_filter.1 hu
      obtain ⟨hW, he⟩ := mem_filter.1 hu
      refine mem_filter.2 ⟨mem_filter.2 ⟨sw_mem_W hW, fun i => ⟨fun h0 => ?_, fun h1 => ?_⟩⟩, ?_⟩
      · rw [Function.comp, sw_fix (by omega) i (by omega) (by omega)]; exact (he i).1 h0
      · have : (sw (m + 3) (m + 1) i).val = m + 1 := sw_at' (by omega) i (by omega)
        rw [Function.comp, show sw (m + 3) (m + 1) i = ⟨m + 1, by omega⟩ from Fin.ext this]; exact ⟨d, hd⟩
      · have : (sw (m + 3) (m + 1) ⟨m + 1, by omega⟩).val = m + 2 := sw_at (by omega) _ rfl
        rw [Function.comp, show sw (m + 3) (m + 1) ⟨m + 1, by omega⟩ = Fin.last _ from Fin.ext this]
        exact (he (Fin.last _)).2 rfl
  calc (∑ u ∈ W (m + 3) A, if Ends u then ∑ j ∈ range (m + 3 - 1), E (z := z) M u j else 0)
      = ∑ j ∈ range (m + 2), ∑ u ∈ WA, E (z := z) M u j := by
        rw [hWAdef, Finset.sum_comm, sum_filter]; rfl
    _ = ∑ u ∈ WA, E (z := z) M u 0 + ∑ u ∈ WA, E (z := z) M u (m + 1) := by
        rw [sum_range_succ, sum_range_succ', sum_eq_zero fun j hj => ?_, zero_add]
        simp only [mem_range] at hj
        refine sum_sw_zero (t := j + 1) (by omega) WA (fun u hu => ?_) (fun u hu => (hWA u hu).1) _
          (fun u _ => hEsw u (j + 1))
        obtain ⟨hW, he⟩ := mem_filter.1 hu
        refine mem_filter.2 ⟨sw_mem_W hW, fun i => ⟨fun h0 => ?_, fun h1 => ?_⟩⟩
        · rw [Function.comp, sw_fix (by omega) i (by omega) (by omega)]; exact (he i).1 h0
        · rw [Function.comp, sw_fix (by omega) i (by omega) (by omega)]; exact (he i).2 h1
    _ = ∑ x ∈ A, ∑ v ∈ W (m + 2) (A.erase x),
          if Ends v then ind (((labw z v : List (D ⊕ C)) : Multiset (D ⊕ C)) = M) else 0 := by
        rw [hfst, hlst, ← sum_add_distrib]
        refine sum_congr rfl fun x _ => ?_
        rw [← sum_add_distrib]
        refine sum_congr rfl fun v _ => ?_
        unfold Fl Fr
        rcases x with d | c
        · rw [if_congr (show ((∃ d', (Sum.inl d : D ⊕ C) = Sum.inl d') ∧ Ends v) ↔ Ends v by simp) rfl rfl,
            if_neg (show ¬((∃ c, (Sum.inl d : D ⊕ C) = Sum.inr c) ∧ Ends v) by simp), add_zero]
        · rw [if_neg (show ¬((∃ d, (Sum.inr c : D ⊕ C) = Sum.inl d) ∧ Ends v) by simp), zero_add,
            if_congr (show ((∃ c', (Sum.inr c : D ⊕ C) = Sum.inr c') ∧ Ends v) ↔ Ends v by simp) rfl rfl]

/-! ### The complex of chains of `D ⊕ (C ∖ ⊤)`, a cone with apex `⊥` -/

section Complex

variable [PartialOrder D] [PartialOrder C] [OrderBot D] [OrderTop C]

/-- The ordinal sum order: `D` below `C`. -/
def R (x y : D ⊕ C) : Prop := Sum.Lex (· ≤ ·) (· ≤ ·) x y

theorem R_inl {d d' : D} : R (Sum.inl d : D ⊕ C) (Sum.inl d') ↔ d ≤ d' := Sum.lex_inl_inl
theorem R_inr {c c' : C} : R (Sum.inr c : D ⊕ C) (Sum.inr c') ↔ c ≤ c' := Sum.lex_inr_inr
theorem R_inr_inl {c : C} {d : D} : ¬ R (Sum.inr c : D ⊕ C) (Sum.inl d) := Sum.lex_inr_inl

variable (D C) in
/-- Faces: nonempty chains avoiding `⊤`. -/
noncomputable def Kc : Finset (Finset (D ⊕ C)) :=
  univ.filter fun τ => τ.Nonempty ∧ IsChain R (τ : Set (D ⊕ C)) ∧ (Sum.inr ⊤ : D ⊕ C) ∉ τ

theorem mem_Kc {τ : Finset (D ⊕ C)} :
    τ ∈ Kc D C ↔ τ.Nonempty ∧ IsChain R (τ : Set (D ⊕ C)) ∧ (Sum.inr ⊤ : D ⊕ C) ∉ τ := by simp [Kc]

theorem isCone : IsCone (Kc D C) (Sum.inl ⊥) where
  ne := fun τ h => (mem_Kc.1 h).1
  down := fun τ h σ hs hne =>
    mem_Kc.2 ⟨hne, (mem_Kc.1 h).2.1.mono (by exact_mod_cast hs), fun ht => (mem_Kc.1 h).2.2 (hs ht)⟩
  apex := fun τ h => by
    obtain ⟨-, hch, ht⟩ := mem_Kc.1 h
    refine mem_Kc.2 ⟨insert_nonempty _ _, ?_, by simp [ht]⟩
    rw [coe_insert]
    refine hch.insert fun b _ _ => Or.inl ?_
    rcases b with d | c
    · exact R_inl.2 bot_le
    · exact Sum.Lex.sep _ _

variable (D C) in
/-- A monotone double-cone labelling with W1 and W2. -/
structure Labelling where
  z : Finset D → Finset C → D ⊕ C
  mono : ∀ (ρ ρ' : Finset D) (σ σ' : Finset C), ρ'.Nonempty → σ.Nonempty → IsChain (· ≤ ·) (ρ : Set D) →
    IsChain (· ≤ ·) (σ' : Set C) → ρ' ⊆ ρ → σ ⊆ σ' → R (z ρ σ) (z ρ' σ')
  w1 : ∀ (ρ : Finset D) (σ : Finset C) (d : D), ρ.Nonempty → σ.Nonempty → IsChain (· ≤ ·) (ρ : Set D) →
    IsChain (· ≤ ·) (σ : Set C) → z ρ σ = Sum.inl d → ¬ ∀ x ∈ ρ, d ≤ x
  w2 : ∀ (ρ : Finset D) (σ : Finset C) (c : C), ρ.Nonempty → σ.Nonempty → IsChain (· ≤ ·) (ρ : Set D) →
    IsChain (· ≤ ·) (σ : Set C) → z ρ σ = Sum.inr c → ¬ ∀ y ∈ σ, y ≤ c

/-! ### Words of a face -/

theorem pre_sub_image {n : ℕ} (u : Fin n → D ⊕ C) (t : ℕ) : pre u t ⊆ univ.image u := fun x hx => by
  obtain ⟨s, -, rfl⟩ := mem_pre.1 hx; exact mem_image_of_mem u (mem_univ s)

theorem pre_mono {n : ℕ} (u : Fin n → D ⊕ C) {s t : ℕ} (h : s ≤ t) : pre u s ⊆ pre u t := fun x hx => by
  obtain ⟨r, hr, rfl⟩ := mem_pre.1 hx; exact mem_pre.2 ⟨r, by omega, rfl⟩

theorem post_anti {n : ℕ} (u : Fin n → D ⊕ C) {s t : ℕ} (h : s ≤ t) : post u t ⊆ post u s := fun x hx => by
  simp only [post, mem_sdiff] at hx ⊢; exact ⟨hx.1, fun h' => hx.2 (pre_mono u h h')⟩

/-- The alphabets of a face. -/
def Alph (τ A : Finset (D ⊕ C)) : Prop := τ ∈ Kc D C ∧ A ⊆ insert (Sum.inl ⊥) (insert (Sum.inr ⊤) τ)

theorem chain_Dp {τ A : Finset (D ⊕ C)} (h : Alph τ A) : IsChain (· ≤ ·) (Dp A : Set D) := by
  intro d hd d' hd' hne
  have hd1 := h.2 (mem_Dp.1 hd); have hd2 := h.2 (mem_Dp.1 hd')
  simp only [mem_insert, Sum.inl.injEq, reduceCtorEq, false_or] at hd1 hd2
  rcases hd1 with rfl | hd1
  · exact Or.inl bot_le
  rcases hd2 with rfl | hd2
  · exact Or.inr bot_le
  rcases (mem_Kc.1 h.1).2.1 hd1 hd2 (by simpa using hne) with h' | h'
  · exact Or.inl (R_inl.1 h')
  · exact Or.inr (R_inl.1 h')

theorem chain_Cp {τ A : Finset (D ⊕ C)} (h : Alph τ A) : IsChain (· ≤ ·) (Cp A : Set C) := by
  intro c hc c' hc' hne
  have hc1 := h.2 (mem_Cp.1 hc); have hc2 := h.2 (mem_Cp.1 hc')
  simp only [mem_insert, Sum.inr.injEq, reduceCtorEq, false_or] at hc1 hc2
  rcases hc1 with rfl | hc1
  · exact Or.inr le_top
  rcases hc2 with rfl | hc2
  · exact Or.inl le_top
  rcases (mem_Kc.1 h.1).2.1 hc1 hc2 (by simpa using hne) with h' | h'
  · exact Or.inl (R_inr.1 h')
  · exact Or.inr (R_inr.1 h')

variable {τ A : Finset (D ⊕ C)} {n : ℕ} {u : Fin n → D ⊕ C}

/-- The cell at cut `t` is a pair of nonempty chains. -/
theorem cell_ok (h : Alph τ A) (hu : u ∈ W n A) (he : Ends u) {t : ℕ} (ht : t + 1 < n) :
    (Dp (post u t)).Nonempty ∧ (Cp (pre u t)).Nonempty ∧ IsChain (· ≤ ·) (Dp (post u t) : Set D) ∧
      IsChain (· ≤ ·) (Cp (pre u t) : Set C) := by
  obtain ⟨hi, himg⟩ := mem_W.1 hu
  have hsubD : Dp (post u t) ⊆ Dp A := Dp_mono (fun x hx => himg ▸ (mem_sdiff.1 hx).1)
  have hsubC : Cp (pre u t) ⊆ Cp A := Cp_mono (himg ▸ pre_sub_image u t)
  obtain ⟨d, hd⟩ := (he ⟨n - 1, by omega⟩).2 (by simp; omega)
  obtain ⟨c, hc⟩ := (he ⟨0, by omega⟩).1 rfl
  refine ⟨⟨d, mem_Dp.2 ((mem_post hi).2 ⟨_, by simp; omega, hd⟩)⟩, ⟨c, mem_Cp.2 (mem_pre.2 ⟨_, by simp, hc⟩)⟩,
    (chain_Dp h).mono (by exact_mod_cast hsubD), (chain_Cp h).mono (by exact_mod_cast hsubC)⟩

theorem cl_mono (L : Labelling D C) (h : Alph τ A) (hu : u ∈ W n A) (he : Ends u) {s t : ℕ} (hst : s ≤ t)
    (ht : t + 1 < n) : R (cl L.z u s) (cl L.z u t) := by
  obtain ⟨-, hCs, hDs, -⟩ := cell_ok h hu he (t := s) (by omega)
  obtain ⟨hDt, -, -, hCt⟩ := cell_ok h hu he ht
  exact L.mono _ _ _ _ hDt hCs hDs hCt (Dp_mono (post_anti u hst)) (Cp_mono (pre_mono u hst))

/-- The labels of a word of a face form a face. -/
theorem labw_face (L : Labelling D C) (h : Alph τ A) (hu : u ∈ W n A) (he : Ends u) (hn : 2 ≤ n) :
    (labw L.z u).toFinset ∈ Kc D C := by
  refine mem_Kc.2 ⟨⟨cl L.z u 0, List.mem_toFinset.2 (mem_labw.2 ⟨0, by omega, rfl⟩)⟩, ?_, ?_⟩
  · intro x hx y hy _
    obtain ⟨s, hs, rfl⟩ := mem_labw.1 (List.mem_toFinset.1 hx)
    obtain ⟨t, ht, rfl⟩ := mem_labw.1 (List.mem_toFinset.1 hy)
    rcases le_total s t with hst | hst
    · exact Or.inl (cl_mono L h hu he hst ht)
    · exact Or.inr (cl_mono L h hu he hst hs)
  · intro htop
    obtain ⟨t, ht, he'⟩ := mem_labw.1 (List.mem_toFinset.1 htop)
    obtain ⟨hD, hC, hDc, hCc⟩ := cell_ok h hu he ht
    exact L.w2 _ _ ⊤ hD hC hDc hCc he' fun y _ => le_top

/-- **A word labelled exactly by its face is impossible.** -/
theorem not_full (L : Labelling D C) (hτ : τ ∈ Kc D C) (hu : u ∈ W n A) (he : Ends u)
    (hA : A = insert (Sum.inr ⊤) τ ∨ (A = insert (Sum.inl ⊥) τ ∧ (Sum.inl ⊥ : D ⊕ C) ∉ τ))
    (hlab : ((labw L.z u : List (D ⊕ C)) : Multiset (D ⊕ C)) = τ.val) : False := by
  have hAlph : Alph τ A := ⟨hτ, by rcases hA with rfl | ⟨rfl, -⟩ <;> intro x hx <;> simp at hx ⊢ <;> tauto⟩
  obtain ⟨hi, himg⟩ := mem_W.1 hu
  have hmem : ∀ x, x ∈ τ ↔ ∃ t, t + 1 < n ∧ cl L.z u t = x := fun x => by
    rw [← mem_labw, ← Multiset.mem_coe, hlab, Finset.mem_val]
  have htop := (mem_Kc.1 hτ).2.2
  have hn : 2 ≤ n := by
    obtain ⟨y, hy⟩ := (mem_Kc.1 hτ).1
    have hcard : A.card = τ.card + 1 := by
      rcases hA with rfl | ⟨rfl, hb⟩
      · exact card_insert_of_notMem htop
      · exact card_insert_of_notMem hb
    rw [← card_of_mem_W hu, hcard]; have := card_pos.2 ⟨y, hy⟩; omega
  rcases hA with rfl | ⟨rfl, hb⟩
  · -- W1 at the first cut
    obtain ⟨hD, hC, hDc, hCc⟩ := cell_ok hAlph hu he (t := 0) (by omega)
    have hall : ∀ d ∈ Dp (post u 0), R (cl L.z u 0) (Sum.inl d) := fun d hd => by
      have h1 : Sum.inl d ∈ insert (Sum.inr ⊤) τ := himg ▸ (mem_sdiff.1 (mem_Dp.1 hd)).1
      obtain ⟨t, ht, hct⟩ := (hmem _).1 ((mem_insert.1 h1).resolve_left (by simp))
      rw [← hct]; exact cl_mono L hAlph hu he (Nat.zero_le t) ht
    obtain ⟨d₁, hd₁⟩ := hD
    rcases hz : cl L.z u 0 with d₀ | c₀
    · refine L.w1 _ _ d₀ ⟨d₁, hd₁⟩ hC hDc hCc hz fun x hx => ?_
      have := hall x hx; rw [hz] at this; exact R_inl.1 this
    · have := hall d₁ hd₁; rw [hz] at this; exact R_inr_inl this
  · -- W2 at the last cut
    obtain ⟨hD, hC, hDc, hCc⟩ := cell_ok hAlph hu he (t := n - 2) (by omega)
    have hall : ∀ c ∈ Cp (pre u (n - 2)), R (Sum.inr c) (cl L.z u (n - 2)) := fun c hc => by
      have h1 : Sum.inr c ∈ insert (Sum.inl ⊥) τ := himg ▸ pre_sub_image u _ (mem_Cp.1 hc)
      obtain ⟨t, ht, hct⟩ := (hmem _).1 ((mem_insert.1 h1).resolve_left (by simp))
      rw [← hct]; exact cl_mono L hAlph hu he (by omega) (by omega)
    obtain ⟨c₁, hc₁⟩ := hC
    rcases hz : cl L.z u (n - 2) with d₀ | c₀
    · have := hall c₁ hc₁; rw [hz] at this; exact R_inr_inl this
    · refine L.w2 _ _ c₀ hD ⟨c₁, hc₁⟩ hDc hCc hz fun y hy => ?_
      have := hall y hy; rw [hz] at this; exact R_inr.1 this

/-! ### The matrix -/

/-- Words of `τ` labelled exactly `σ`: over `τ ∪ {⊤}`, and over `τ ∪ {⊥}` unless `τ` is a cone face. -/
noncomputable def G (L : Labelling D C) : Matrix (Kc D C) (Kc D C) (ZMod 2) := fun σ τ =>
  S L.z σ.1.val (insert (Sum.inr ⊤) τ.1) +
    ind ((Sum.inl ⊥ : D ⊕ C) ∉ τ.1) * S L.z σ.1.val (insert (Sum.inl ⊥) τ.1)

theorem bd_S (L : Labelling D C) (σ : Kc D C) (A : Finset (D ⊕ C))
    (hface : ∀ u ∈ W A.card A, Ends u → (labw L.z u).toFinset ∈ Kc D C) :
    (∑ ρ : Kc D C, Bd (Kc D C) σ ρ * S L.z ρ.1.val A) = ∑ x ∈ A, S L.z σ.1.val (A.erase x) := by
  have hσ0 : σ.1.val ≠ 0 := fun h => ((mem_Kc.1 σ.2).1).ne_empty (Finset.val_eq_zero.1 h)
  rw [← door (z := L.z) hσ0 A]
  simp only [S, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun u hu => ?_
  by_cases he : Ends u
  · simp only [if_pos he]
    rw [bd_ind σ (labw L.z u) (hface u hu he)]
    have := removal (labw L.z u) σ.1.val σ.1.nodup
    rw [labw_length] at this; unfold E ind; convert this.symm
  · simp only [if_neg he, mul_zero, sum_const_zero]

theorem faces_of (L : Labelling D C) {τ : Finset (D ⊕ C)} (hτ : τ ∈ Kc D C) {x : D ⊕ C} (hx : x ∉ τ)
    (hxs : x = Sum.inr ⊤ ∨ x = Sum.inl ⊥) :
    ∀ u ∈ W (insert x τ).card (insert x τ), Ends u → (labw L.z u).toFinset ∈ Kc D C := fun u hu he => by
  refine labw_face L ⟨hτ, ?_⟩ hu he ?_
  · intro y hy; rcases mem_insert.1 hy with rfl | hy
    · rcases hxs with rfl | rfl <;> simp
    · simp [hy]
  · rw [card_insert_of_notMem hx]; have := ((mem_Kc.1 hτ).1).card_pos; omega

/-- **`G` is a chain map.** -/
theorem chain (L : Labelling D C) : G L * Bd (Kc D C) = Bd (Kc D C) * G L := by
  ext σ τ
  simp only [Matrix.mul_apply]
  have hσ0 : σ.1.val ≠ 0 := fun h => ((mem_Kc.1 σ.2).1).ne_empty (Finset.val_eq_zero.1 h)
  have htop : (Sum.inr ⊤ : D ⊕ C) ∉ τ.1 := (mem_Kc.1 τ.2).2.2
  set T : D ⊕ C := Sum.inr ⊤ with hT
  set B : D ⊕ C := Sum.inl ⊥ with hB
  let g : Finset (D ⊕ C) → ZMod 2 := fun ρ =>
    S L.z σ.1.val (insert T ρ) + ind (B ∉ ρ) * S L.z σ.1.val (insert B ρ)
  have hg0 : g ∅ = 0 := by
    simp only [g, insert_empty]
    rw [S_small hσ0 (by simp), S_small hσ0 (by simp), mul_zero, add_zero]
  rw [bd_right isCone σ τ (G L) g hg0 (fun ρ _ _ => rfl)]
  have hR : (∑ ρ : Kc D C, Bd (Kc D C) σ ρ * G L ρ τ) =
      (∑ x ∈ insert T τ.1, S L.z σ.1.val ((insert T τ.1).erase x)) +
        ind (B ∉ τ.1) * ∑ x ∈ insert B τ.1, S L.z σ.1.val ((insert B τ.1).erase x) := by
    simp only [G, mul_add, sum_add_distrib]
    congr 1
    · exact bd_S L σ _ (faces_of L τ.2 htop (Or.inl rfl))
    · by_cases hb : B ∈ τ.1
      · have hb' : (Sum.inl ⊥ : D ⊕ C) ∈ τ.1 := hb
        simp only [ind_f (not_not.2 hb'), zero_mul, mul_zero, sum_const_zero]
        rw [ind_f (not_not.2 hb), zero_mul]
      · rw [← bd_S L σ _ (faces_of L τ.2 hb (Or.inr rfl)), Finset.mul_sum]
        exact sum_congr rfl fun ρ _ => by ring
  have hTe : ∀ x ∈ τ.1, (insert T τ.1).erase x = insert T (τ.1.erase x) := fun x hx =>
    erase_insert_of_ne (fun h => htop (h ▸ hx))
  have eT : (∑ x ∈ insert T τ.1, S L.z σ.1.val ((insert T τ.1).erase x)) =
      S L.z σ.1.val τ.1 + ∑ x ∈ τ.1, S L.z σ.1.val (insert T (τ.1.erase x)) := by
    rw [sum_insert htop, erase_insert htop]
    exact congrArg _ (sum_congr rfl fun x hx => by rw [hTe x hx])
  have eL : (∑ x ∈ τ.1, g (τ.1.erase x)) = (∑ x ∈ τ.1, S L.z σ.1.val (insert T (τ.1.erase x))) +
      ∑ x ∈ τ.1, ind (B ∉ τ.1.erase x) * S L.z σ.1.val (insert B (τ.1.erase x)) := sum_add_distrib
  rw [hR, eT, eL]
  by_cases hb : B ∈ τ.1
  · have eI : (∑ x ∈ τ.1, ind (B ∉ τ.1.erase x) * S L.z σ.1.val (insert B (τ.1.erase x))) =
        S L.z σ.1.val τ.1 := by
      rw [sum_eq_single B (fun x _ hx => by rw [ind_f (fun h => h (mem_erase.2 ⟨Ne.symm hx, hb⟩)), zero_mul])
        (fun h => absurd hb h), ind_t (notMem_erase _ _), one_mul, insert_erase hb]
    rw [ind_f (not_not.2 hb), zero_mul, add_zero, eI, add_comm]
  · have hBe : ∀ x ∈ τ.1, (insert B τ.1).erase x = insert B (τ.1.erase x) := fun x hx =>
      erase_insert_of_ne (fun h => hb (h ▸ hx))
    have eB : (∑ x ∈ insert B τ.1, S L.z σ.1.val ((insert B τ.1).erase x)) =
        S L.z σ.1.val τ.1 + ∑ x ∈ τ.1, S L.z σ.1.val (insert B (τ.1.erase x)) := by
      rw [sum_insert hb, erase_insert hb]
      exact congrArg _ (sum_congr rfl fun x hx => by rw [hBe x hx])
    have eI : (∑ x ∈ τ.1, ind (B ∉ τ.1.erase x) * S L.z σ.1.val (insert B (τ.1.erase x))) =
        ∑ x ∈ τ.1, S L.z σ.1.val (insert B (τ.1.erase x)) :=
      sum_congr rfl fun x _ => by rw [ind_t (fun h => hb (mem_of_mem_erase h)), one_mul]
    rw [ind_t hb, one_mul, eB, eI]
    have key : ∀ a b c : ZMod 2, a + b = c + a + (c + b) := by decide
    exact key _ _ _

/-! ### The trace -/

/-- The single word of the apex: `⊤⊥`. -/
noncomputable def w₀ : Fin 2 → D ⊕ C := ![Sum.inr ⊤, Sum.inl ⊥]

theorem w₀_mem : (w₀ : Fin 2 → D ⊕ C) ∈ W 2 (insert (Sum.inr ⊤) {Sum.inl ⊥} : Finset (D ⊕ C)) := by
  refine mem_W.2 ⟨fun a b h => ?_, ?_⟩
  · fin_cases a <;> fin_cases b <;> simp_all [w₀]
  · ext x; simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro ⟨r, rfl⟩; fin_cases r <;> simp [w₀]
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩

theorem w₀_ends : Ends (w₀ : Fin 2 → D ⊕ C) := (ends_iff _).2 ⟨⟨⊤, rfl⟩, ⟨⊥, rfl⟩⟩

theorem S_apex (L : Labelling D C) (M : Multiset (D ⊕ C)) :
    S L.z M (insert (Sum.inr ⊤) {Sum.inl ⊥}) =
      ind (((labw L.z w₀ : List (D ⊕ C)) : Multiset (D ⊕ C)) = M) := by
  have hA : (insert (Sum.inr ⊤) {Sum.inl ⊥} : Finset (D ⊕ C)).card = 2 := by
    rw [card_insert_of_notMem (by simp)]; rfl
  have hw := w₀_mem (D := D) (C := C)
  rw [S_card hA, sum_eq_single w₀]
  · rw [if_pos w₀_ends]
  · intro u hu hne
    rw [if_neg]
    intro he
    obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := (ends_iff u).1 he
    apply hne
    obtain ⟨-, himg⟩ := mem_W.1 hu
    have h0 : u 0 ∈ (insert (Sum.inr ⊤) {Sum.inl ⊥} : Finset (D ⊕ C)) := himg ▸ mem_image_of_mem u (mem_univ 0)
    have h1 : u 1 ∈ (insert (Sum.inr ⊤) {Sum.inl ⊥} : Finset (D ⊕ C)) := himg ▸ mem_image_of_mem u (mem_univ 1)
    have hd' : u 1 = Sum.inl d := hd
    rw [hc] at h0; rw [hd'] at h1
    simp only [mem_insert, mem_singleton, reduceCtorEq, or_false, false_or] at h0 h1
    funext i; fin_cases i
    · simp [w₀, hc, h0]
    · simp [w₀, hd', h1]
  · exact fun h => absurd hw h

/-- **The double-cone lemma.** -/
theorem dcl (L : Labelling D C) : False := by
  have hv : ({Sum.inl ⊥} : Finset (D ⊕ C)) ∈ Kc D C := by
    refine mem_Kc.2 ⟨singleton_nonempty _, ?_, by simp⟩
    rw [coe_singleton]; exact Set.Subsingleton.isChain Set.subsingleton_singleton
  have htr := trace_chain isCone hv (G L) (chain L)
  -- the trace is zero: no word is labelled exactly by its face
  have h0 : Matrix.trace (G L) = 0 := by
    refine sum_eq_zero fun τ _ => ?_
    simp only [Matrix.diag, G]
    have hz : ∀ A, (A = insert (Sum.inr ⊤) τ.1 ∨ (A = insert (Sum.inl ⊥) τ.1 ∧ (Sum.inl ⊥ : D ⊕ C) ∉ τ.1)) →
        S L.z τ.1.val A = 0 := fun A hA => sum_eq_zero fun u hu => by
      split_ifs with he
      · exact ind_f (not_full L τ.2 hu he hA)
      · rfl
    rw [hz _ (Or.inl rfl)]
    by_cases hb : (Sum.inl ⊥ : D ⊕ C) ∈ τ.1
    · rw [ind_f (not_not.2 hb), zero_mul, add_zero]
    · rw [hz _ (Or.inr ⟨rfl, hb⟩), mul_zero, add_zero]
  -- the trace is one: the apex has a single word
  have hw₀ : labw L.z w₀ = [cl L.z w₀ 0] := by simp [labw]
  have hface : ({cl L.z w₀ 0} : Finset (D ⊕ C)) ∈ Kc D C := by
    have h := labw_face L (τ := {Sum.inl ⊥}) ⟨hv, by intro x hx; simp at hx ⊢; tauto⟩ w₀_mem w₀_ends le_rfl
    rwa [hw₀, List.toFinset_cons, List.toFinset_nil, insert_empty] at h
  have h1 : (∑ τ : Kc D C, ind (τ.1.card = 1) * G L τ ⟨{Sum.inl ⊥}, hv⟩) = 1 := by
    simp only [G, ind_f (show ¬ (Sum.inl ⊥ : D ⊕ C) ∉ ({Sum.inl ⊥} : Finset (D ⊕ C)) by simp), zero_mul,
      add_zero, S_apex, hw₀]
    rw [sum_eq_single ⟨{cl L.z w₀ 0}, hface⟩]
    · rw [ind_t (card_singleton _), one_mul]; exact ind_t rfl
    · intro τ _ hne
      have : ¬ ((([cl L.z w₀ 0] : List (D ⊕ C)) : Multiset (D ⊕ C)) = τ.1.val) :=
        fun h => hne (Subtype.ext (Finset.val_inj.1 (by rw [← h]; rfl)))
      rw [ind_f this, mul_zero]
    · simp
  rw [h0, h1] at htr
  exact absurd htr (by decide)

end Complex

/-! ### The Cut Lemma on finite bounded posets -/

section Cut
open Mordor.CLL (cmax cmax_spec)

/-- The bottom of a chain (`⊥` if there is none). -/
noncomputable def cmin {β : Type*} [PartialOrder β] [OrderBot β] (ρ : Finset β) : β :=
  if h : ∃ m ∈ ρ, ∀ y ∈ ρ, m ≤ y then h.choose else ⊥

theorem cmin_spec {β : Type*} [PartialOrder β] [OrderBot β] {ρ : Finset β} (hne : ρ.Nonempty)
    (hch : IsChain (· ≤ ·) (ρ : Set β)) : cmin ρ ∈ ρ ∧ ∀ y ∈ ρ, cmin ρ ≤ y := by
  have h : ∃ m ∈ ρ, ∀ y ∈ ρ, m ≤ y := by
    obtain ⟨m, hm, hmin⟩ := ρ.exists_minimal hne
    refine ⟨m, hm, fun y hy => ?_⟩
    by_cases hmy : m = y
    · rw [hmy]
    · rcases hch hm hy hmy with h1 | h1
      · exact h1
      · exact hmin hy h1
  unfold cmin; rw [dif_pos h]; exact h.choose_spec

/-- **Finite cross-capture.** In any bounded poset, if a finite set `S ∋ ⊥, ⊤` contains `F x y` for all
`x ∈ S ∩ D`, `y ∈ S ∖ D`, then the cut `D` has a witness (in `S`). No lattice structure, no chain condition, and
`F` need only be monotone on cross pairs `D × Dᶜ` (the ground theory of §34.3g–h encodes exactly this). -/
theorem cut_cross {α : Type*} [PartialOrder α] [BoundedOrder α] (Dn : Set α)
    (hD : ∀ a b, a ≤ b → b ∈ Dn → a ∈ Dn) (htop : ⊤ ∉ Dn) (hbot : ⊥ ∈ Dn)
    (F : α → α → α) (hF : ∀ a a' b b', a ∈ Dn → a' ∈ Dn → b ∉ Dn → b' ∉ Dn → a ≤ a' → b ≤ b' → F a b ≤ F a' b')
    (S : Set α) (hS : S.Finite) (hbS : ⊥ ∈ S) (htS : ⊤ ∈ S)
    (hcross : ∀ x ∈ S, x ∈ Dn → ∀ y ∈ S, y ∉ Dn → F x y ∈ S) :
    ∃ x ∈ Dn, ∃ y ∉ Dn, F x y ≤ x ∨ y ≤ F x y := by
  by_contra hno
  push_neg at hno
  haveI : Finite S := hS.to_subtype
  haveI : Finite {x : α // x ∈ S ∧ x ∈ Dn} :=
    Finite.of_injective (fun x => (⟨x.1, x.2.1⟩ : S)) fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h)
  haveI : Finite {y : α // y ∈ S ∧ y ∉ Dn} :=
    Finite.of_injective (fun y => (⟨y.1, y.2.1⟩ : S)) fun a b h => Subtype.ext (by simpa using congrArg Subtype.val h)
  letI : Fintype {x : α // x ∈ S ∧ x ∈ Dn} := Fintype.ofFinite _
  letI : Fintype {y : α // y ∈ S ∧ y ∉ Dn} := Fintype.ofFinite _
  letI : OrderBot {x : α // x ∈ S ∧ x ∈ Dn} :=
    { bot := ⟨⊥, hbS, hbot⟩, bot_le := fun a => (bot_le : ⊥ ≤ a.1) }
  letI : OrderTop {y : α // y ∈ S ∧ y ∉ Dn} :=
    { top := ⟨⊤, htS, htop⟩, le_top := fun a => (le_top : a.1 ≤ ⊤) }
  let val : Finset {x : α // x ∈ S ∧ x ∈ Dn} → Finset {y : α // y ∈ S ∧ y ∉ Dn} → α :=
    fun ρ σ => F (cmin ρ).1 (cmax σ).1
  have hvS : ∀ ρ σ, val ρ σ ∈ S := fun ρ σ => hcross _ (cmin ρ).2.1 (cmin ρ).2.2 _ (cmax σ).2.1 (cmax σ).2.2
  let zf : Finset {x : α // x ∈ S ∧ x ∈ Dn} → Finset {y : α // y ∈ S ∧ y ∉ Dn} →
      {x : α // x ∈ S ∧ x ∈ Dn} ⊕ {y : α // y ∈ S ∧ y ∉ Dn} :=
    fun ρ σ => if hv : val ρ σ ∈ Dn then Sum.inl ⟨val ρ σ, hvS ρ σ, hv⟩ else Sum.inr ⟨val ρ σ, hvS ρ σ, hv⟩
  refine dcl (D := {x : α // x ∈ S ∧ x ∈ Dn}) (C := {y : α // y ∈ S ∧ y ∉ Dn})
    { z := zf
      mono := fun ρ ρ' σ σ' hρ' hσ hρc hσc hsub hsσ => ?_
      w1 := fun ρ σ d hρ hσ hρc hσc h hall => ?_
      w2 := fun ρ σ c hρ hσ hρc hσc h hall => ?_ }
  · have hρ : ρ.Nonempty := hρ'.mono hsub
    have hσ' : σ'.Nonempty := hσ.mono hsσ
    have hle : val ρ σ ≤ val ρ' σ' := hF _ _ _ _ (cmin ρ).2.2 (cmin ρ').2.2 (cmax σ).2.2 (cmax σ').2.2
      ((cmin_spec hρ hρc).2 _ (hsub (cmin_spec hρ' (hρc.mono (by exact_mod_cast hsub))).1))
      ((cmax_spec hσ' hσc).2 _ (hsσ (cmax_spec hσ (hσc.mono (by exact_mod_cast hsσ))).1))
    simp only [zf]
    by_cases hv : val ρ σ ∈ Dn <;> by_cases hv' : val ρ' σ' ∈ Dn
    · rw [dif_pos hv, dif_pos hv']; exact R_inl.2 hle
    · rw [dif_pos hv, dif_neg hv']; exact Sum.Lex.sep _ _
    · exact absurd (hD _ _ hle hv') hv
    · rw [dif_neg hv, dif_neg hv']; exact R_inr.2 hle
  · simp only [zf] at h
    by_cases hv : val ρ σ ∈ Dn
    · rw [dif_pos hv, Sum.inl.injEq] at h
      have hle : val ρ σ ≤ (cmin ρ).1 := by
        have := hall _ (cmin_spec hρ hρc).1; rw [← h] at this; exact this
      exact (hno _ (cmin ρ).2.2 _ (cmax σ).2.2).1 hle
    · rw [dif_neg hv] at h; cases h
  · simp only [zf] at h
    by_cases hv : val ρ σ ∈ Dn
    · rw [dif_pos hv] at h; cases h
    · rw [dif_neg hv, Sum.inr.injEq] at h
      have hle : (cmax σ).1 ≤ val ρ σ := by
        have := hall _ (cmax_spec hσ hσc).1; rw [← h] at this; exact this
      exact (hno _ (cmin ρ).2.2 _ (cmax σ).2.2).2 hle

/-- **The Cut Lemma on every finite bounded poset.** -/
theorem cut_finite {α : Type*} [Fintype α] [PartialOrder α] [BoundedOrder α] (Dn : Set α)
    (hD : ∀ a b, a ≤ b → b ∈ Dn → a ∈ Dn) (htop : ⊤ ∉ Dn) (hbot : ⊥ ∈ Dn)
    (F : α → α → α) (hF : ∀ a a' b b', a ≤ a' → b ≤ b' → F a b ≤ F a' b') :
    ∃ x ∈ Dn, ∃ y ∉ Dn, F x y ≤ x ∨ y ≤ F x y :=
  cut_cross Dn hD htop hbot F (fun a a' b b' _ _ _ _ => hF a a' b b') Set.univ Set.finite_univ trivial trivial
    fun _ _ _ _ _ _ => trivial


/-- **The Cut Lemma on end-finite bounded posets** (poset form of `cut_of_end_finite`). If every proper principal ideal
and filter is finite, every cut has a witness: with `c = F ⊥ ⊤ ≠ ⊥`, each value lies below `F x ⊤ ∈ ↑c ∖ {⊤}`, a
finite set of elements with finite ideals, so all cross values lie in one finite set and `cut_cross` applies. -/
theorem cut_end_finite_poset {α : Type*} [PartialOrder α] [BoundedOrder α]
    (hI : ∀ g : α, g ≠ ⊤ → (Set.Iic g).Finite) (hJ : ∀ g : α, g ≠ ⊥ → (Set.Ici g).Finite) (Dn : Set α)
    (hD : ∀ a b, a ≤ b → b ∈ Dn → a ∈ Dn) (htop : ⊤ ∉ Dn) (hbot : ⊥ ∈ Dn)
    (F : α → α → α) (hF : ∀ a a' b b', a ≤ a' → b ≤ b' → F a b ≤ F a' b') :
    ∃ x ∈ Dn, ∃ y ∉ Dn, F x y ≤ x ∨ y ≤ F x y := by
  by_contra hno
  push_neg at hno
  have hc : F ⊥ ⊤ ≠ ⊥ := fun h => (hno ⊥ hbot ⊤ htop).1 (le_of_eq h)
  let U : Set α := Set.Ici (F ⊥ ⊤) \ {⊤}
  have hU : U.Finite := (hJ _ hc).subset Set.diff_subset
  let Vs : Set α := Set.iUnion fun u => Set.iUnion fun (_ : u ∈ U) => Set.Iic u
  have hV : Vs.Finite := Set.Finite.biUnion hU fun u hu => hI u hu.2
  have hval : ∀ x ∈ Dn, ∀ y, y ∉ Dn → F x y ∈ Vs := fun x hx y hy => by
    have hu : F x ⊤ ∈ U := ⟨hF _ _ _ _ bot_le le_rfl, fun h => (hno x hx ⊤ htop).2 (le_of_eq h.symm)⟩
    exact Set.mem_iUnion₂.2 ⟨_, hu, hF _ _ _ _ le_rfl le_top⟩
  obtain ⟨x, hx, y, hy, h⟩ := cut_cross Dn hD htop hbot F (fun a a' b b' _ _ _ _ => hF a a' b b')
    (Vs ∪ {⊥, ⊤}) (hV.union (Set.toFinite _)) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
    (fun x _ hx y _ hy => Or.inl (hval x hx y hy))
  rcases h with h | h
  · exact (hno x hx y hy).1 h
  · exact (hno x hx y hy).2 h

end Cut

end Mordor.RelativeCut
