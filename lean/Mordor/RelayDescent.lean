import Mordor.RankTwoIncidence

/-!
# Relays in star petals: normal form and descent (round 26, §34.3z¹⁴⁶)

ChatGPT brief "Eliminate the relay in rank-two cuts" (HEAD d3dfe8a).

Setting: a bounded lattice with DCC, `F` monotone, `D` a witness-free proper cut, blocks `a, b ∈ D` (the brief's
`a_i`, `a_j`) with common point `s ≤ a, b`; the petal `a` is isolated with centre `s` (every member not below `a`
meets `a` below `s`); below `a` the cut has rank two (`v < z < a → v = ⊥`).

A **relay** at a column `u`: `u ∉ D`, `F ⊥ u ≤ s`, `F b u ≤ u`, `F b u ≤ a` (§34.3z¹⁴⁵).

* `relay_normal_form`: with `p = F s u`, `q = F b u`, `v = F a u`: `p ≤ q ≤ a`, `q ≤ u`, `p ≰ s`, `q ≰ b`, `u ≰ q`,
  `p ≤ v`, `v ≰ u` (`FGTwo.l4`, centre `s`, petal `a`), `p ≤ u ⊓ v`, and `u ⊓ v < u` — the strictness comes from
  `u ≰ v` (witness-freeness at row `a`), not from `v ≰ u`; and `p = a` or `p` is an atom.
* `relay_meet_update`: with `w = u ⊓ F a u`, `w < u`, and either `w ∈ D` (*terminal*), or the relay persists at `w`,
  or the **private seed**: `p = F s u` is an atom `< a`, `F s w = p`, `F b w = a`, `a ≰ w`, `p ≤ w`, `w ⊓ a = p`.
* `relay_descends` (DCC): every relay column lies above a relay column `u'` (same blocks) whose meet update is
  terminal or a private seed.

With an atomic centre (`hsat : ∀ v < s, v = ⊥`):
* `relay_bot_value`: `F ⊥ u = s`; `relay_centre_value`: `F s u = a` (so `F b u = a ≤ u`);
* `no_private_seed`: the private seed never occurs;
* `relay_descends_terminal` (`a` maximal): every relay descends to a **terminal relay** `u'`: `a ≤ u'`,
  `F ⊥ u' = s`, `F s u' = F b u' = a`, `a < F a u'`, `F a u' ∉ D`, `u' ⊓ F a u' = a`.
The terminal relay is not shown to yield a witness; see the log for partial models.
-/

namespace Mordor.Relay
open Mordor

set_option linter.unusedSectionVars false

variable {β : Type*} [Lattice β] [BoundedOrder β] [WellFoundedLT β] {F : β → β → β}

/-- A relay column for the blocks `a`, `b` with centre `s`. -/
def IsRelay (F : β → β → β) (D : Set β) (s a b u : β) : Prop :=
  u ∉ D ∧ F ⊥ u ≤ s ∧ F b u ≤ u ∧ F b u ≤ a

structure Setting (F : β → β → β) (D : Set β) (s a b : β) : Prop where
  mono : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y'
  down : ∀ ⦃x y⦄, x ≤ y → y ∈ D → x ∈ D
  top : ⊤ ∉ D
  nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y
  ha : a ∈ D
  hb : b ∈ D
  hsa : s ≤ a
  hsb : s ≤ b
  iso : ∀ x ∈ D, ¬ x ≤ a → ∀ z, z ≤ x → z ≤ a → z ≤ s
  rank2 : ∀ z, z < a → ∀ v, v < z → v = ⊥

variable {D : Set β} {s a b : β}

/-- `FGTwo.l4` for the isolated petal `a` with centre `s`. -/
theorem petal_l4 (S : Setting F D s a b) {u : β} (hu : u ∉ D) (hsu : F s u ≤ a) : ¬ F a u ≤ u := by
  let InB : β → Prop := fun x => x ∈ D ∧ ∀ z, z ≤ x → z ≤ a → z ≤ s
  exact Mordor.FGTwo.l4 (InD := (· ∈ D)) (InB := InB) (a := a) (r := s) S.mono
    (fun x => ⟨fun hx => (em (x ≤ a)).elim Or.inl (fun h => Or.inr ⟨hx, S.iso x hx h⟩),
      fun h => h.elim (fun h' => S.down h' S.ha) (fun h' => h'.1)⟩)
    (fun x y hxy hy => ⟨S.down hxy hy.1, fun z hz hza => hy.2 z (hz.trans hxy) hza⟩)
    S.hsa (fun z hza hz => hz.2 z le_rfl hza) (fun x hx y hy => S.nw x hx y hy) u hu hsu

/-- **Relay normal form.** -/
theorem relay_normal_form (S : Setting F D s a b) {u : β} (hr : IsRelay F D s a b u) :
    F s u ≤ F b u ∧ F b u ≤ a ∧ F b u ≤ u ∧ ¬ F s u ≤ s ∧ ¬ F b u ≤ b ∧ ¬ u ≤ F b u ∧
      F s u ≤ F a u ∧ ¬ F a u ≤ u ∧ F s u ≤ u ⊓ F a u ∧ u ⊓ F a u < u ∧
      (F s u = a ∨ ∀ v, v < F s u → v = ⊥) := by
  obtain ⟨hu, -, hbu, hba⟩ := hr
  have hsD : s ∈ D := S.down S.hsa S.ha
  have hpq : F s u ≤ F b u := S.mono _ _ _ _ S.hsb le_rfl
  have hpa : F s u ≤ a := hpq.trans hba
  have hv : ¬ F a u ≤ u := petal_l4 S hu hpa
  have hpv : F s u ≤ F a u := S.mono _ _ _ _ S.hsa le_rfl
  refine ⟨hpq, hba, hbu, (S.nw s hsD u hu).1, (S.nw b S.hb u hu).1, (S.nw b S.hb u hu).2, hpv, hv,
    le_inf (hpq.trans hbu) hpv, lt_of_le_of_ne inf_le_left (fun e => (S.nw a S.ha u hu).2 (e.symm.le.trans inf_le_right)), ?_⟩
  rcases eq_or_lt_of_le hpa with e | hlt
  · exact Or.inl e
  · exact Or.inr (S.rank2 _ hlt)

/-- The private-seed configuration at the meet update `w = u ⊓ F a u`. -/
def PrivateSeed (F : β → β → β) (D : Set β) (s a b u : β) : Prop :=
  let w := u ⊓ F a u
  w ∉ D ∧ F s u < a ∧ (∀ v, v < F s u → v = ⊥) ∧ F s w = F s u ∧ F b w = a ∧ ¬ a ≤ w ∧ F s u ≤ w ∧
    w ⊓ a = F s u

/-- **The meet update.** -/
theorem relay_meet_update (S : Setting F D s a b) {u : β} (hr : IsRelay F D s a b u) :
    u ⊓ F a u < u ∧ (u ⊓ F a u ∈ D ∨ IsRelay F D s a b (u ⊓ F a u) ∨ PrivateSeed F D s a b u) := by
  obtain ⟨hpq, hba, hbu, hps, -, -, hpv, -, hpw, hwlt, hcase⟩ := relay_normal_form S hr
  obtain ⟨hu, h0, -, -⟩ := hr
  set w := u ⊓ F a u with hw
  refine ⟨hwlt, ?_⟩
  by_cases hwD : w ∈ D
  · exact Or.inl hwD
  have hsD : s ∈ D := S.down S.hsa S.ha
  have h0w : F ⊥ w ≤ s := (S.mono _ _ _ _ le_rfl inf_le_left).trans h0
  have hqw : F b w ≤ a := (S.mono _ _ _ _ le_rfl inf_le_left).trans hba
  by_cases hrel : F b w ≤ w
  · exact Or.inr (Or.inl ⟨hwD, h0w, hrel, hqw⟩)
  right; right
  -- p = a is impossible: then a ≤ w and F b w ≤ a ≤ w
  rcases hcase with hpa | hat
  · exact absurd (hqw.trans (hpa ▸ hpw)) hrel
  have hpa : F s u < a := lt_of_le_of_ne (hpq.trans hba) (fun e => hrel (hqw.trans (e ▸ hpw)))
  -- p' = F s w equals p
  have hp'le : F s w ≤ F s u := S.mono _ _ _ _ le_rfl inf_le_left
  have hp'ns : ¬ F s w ≤ s := (S.nw s hsD w hwD).1
  have hp' : F s w = F s u := by
    rcases eq_or_lt_of_le hp'le with e | hlt
    · exact e
    · exact absurd ((hat _ hlt).symm ▸ bot_le) hp'ns
  -- q' = F b w lies in [p, a] and is not below w, so it is a
  have hq'lo : F s u ≤ F b w := hp' ▸ S.mono _ _ _ _ S.hsb le_rfl
  have hq' : F b w = a := by
    rcases eq_or_lt_of_le hqw with e | hlt
    · exact e
    · exfalso
      rcases eq_or_lt_of_le hq'lo with e | hlt'
      · exact hrel (e ▸ hpw)
      · have := S.rank2 _ hlt _ hlt'
        exact (Ne.symm (ne_of_lt hlt')) (by
          have hb0 : F s u = ⊥ := this
          exact absurd (hb0 ▸ bot_le) hps)
  have hanw : ¬ a ≤ w := fun h => hrel (hq' ▸ h)
  have hwa : w ⊓ a = F s u := by
    have hlo : F s u ≤ w ⊓ a := le_inf hpw hpa.le
    rcases eq_or_lt_of_le (inf_le_right : w ⊓ a ≤ a) with e | hlt
    · exact absurd (e ▸ inf_le_left) hanw
    · rcases eq_or_lt_of_le hlo with e | hlt'
      · exact e.symm
      · exact absurd ((S.rank2 _ hlt _ hlt') ▸ bot_le) hps
  exact ⟨hwD, hpa, hat, hp', hq', hanw, hpw, hwa⟩

/-- **Relay descent** (DCC). -/
theorem relay_descends (S : Setting F D s a b) :
    ∀ u, IsRelay F D s a b u → ∃ u', u' ≤ u ∧ IsRelay F D s a b u' ∧
      (u' ⊓ F a u' ∈ D ∨ PrivateSeed F D s a b u') := by
  intro u
  induction u using WellFoundedLT.induction with
  | _ u ih =>
    intro hr
    obtain ⟨hlt, h | h | h⟩ := relay_meet_update S hr
    · exact ⟨u, le_rfl, hr, Or.inl h⟩
    · obtain ⟨u', hu', hr', hend⟩ := ih _ hlt h
      exact ⟨u', hu'.trans hlt.le, hr', hend⟩
    · exact ⟨u, le_rfl, hr, Or.inr h⟩

end Mordor.Relay

namespace Mordor.Relay
open Mordor

set_option linter.unusedSectionVars false

variable {β : Type*} [Lattice β] [BoundedOrder β] [WellFoundedLT β] {F : β → β → β} {D : Set β} {s a b : β}

/-- In a relay with an atomic centre, the bottom row hits the centre: `F ⊥ u = s`. -/
theorem relay_bot_value (S : Setting F D s a b) (hsat : ∀ v, v < s → v = ⊥) {u : β}
    (hr : IsRelay F D s a b u) : F ⊥ u = s := by
  have hbD : (⊥ : β) ∈ D := S.down bot_le S.ha
  rcases eq_or_lt_of_le hr.2.1 with e | hlt
  · exact e
  · exact absurd ((hsat _ hlt).le) (S.nw ⊥ hbD u hr.1).1

/-- **In a relay with an atomic centre the centre row hits the block: `F s u = a`.** Hence the private seed never
occurs (it needs `F s u` to be an atom). -/
theorem relay_centre_value (S : Setting F D s a b) (hsat : ∀ v, v < s → v = ⊥) {u : β}
    (hr : IsRelay F D s a b u) : F s u = a := by
  obtain ⟨-, -, -, hps, -, -, -, -, -, -, hcase⟩ := relay_normal_form S hr
  rcases hcase with e | hat
  · exact e
  have hsp : s ≤ F s u := relay_bot_value S hsat hr ▸ S.mono _ _ _ _ bot_le le_rfl
  exfalso
  rcases eq_or_lt_of_le hsp with e | hlt
  · exact hps e.ge
  · have hs0 : s = ⊥ := hat s hlt
    have hbD : (⊥ : β) ∈ D := S.down bot_le S.ha
    exact (S.nw ⊥ hbD u hr.1).1 (hs0 ▸ (relay_bot_value S hsat hr).le)

theorem no_private_seed (S : Setting F D s a b) (hsat : ∀ v, v < s → v = ⊥) {u : β}
    (hr : IsRelay F D s a b u) : ¬ PrivateSeed F D s a b u := fun h =>
  (ne_of_lt h.2.1) (relay_centre_value S hsat hr)

/-- **Every relay descends to a terminal relay** (DCC, `a` maximal in `D`, atomic centre): some relay column
`u' ≤ u` has `a ≤ u'`, `F ⊥ u' = s`, `F s u' = F b u' = a`, `a < F a u'`, `F a u' ∉ D` and `u' ⊓ F a u' = a`. -/
theorem relay_descends_terminal (S : Setting F D s a b) (hsat : ∀ v, v < s → v = ⊥)
    (hamax : ∀ n ∈ D, a ≤ n → n = a) {u : β} (hr : IsRelay F D s a b u) :
    ∃ u', u' ≤ u ∧ IsRelay F D s a b u' ∧ a ≤ u' ∧ F ⊥ u' = s ∧ F s u' = a ∧ F b u' = a ∧ a < F a u' ∧
      F a u' ∉ D ∧ u' ⊓ F a u' = a := by
  obtain ⟨u', hu', hr', hend⟩ := relay_descends S u hr
  have hp := relay_centre_value S hsat hr'
  obtain ⟨hpq, hba, hbu, -, -, -, hpv, hv, hpw, -, -⟩ := relay_normal_form S hr'
  have hq : F b u' = a := le_antisymm hba (hp ▸ hpq)
  have hau : a ≤ u' := hq ▸ hbu
  have hav : a ≤ F a u' := hp ▸ hpv
  have hlt : a < F a u' := lt_of_le_of_ne hav (fun e => hv (e ▸ hau))
  have hvD : F a u' ∉ D := fun h => (ne_of_lt hlt) (hamax _ h hav).symm
  rcases hend with hw | hps
  · exact ⟨u', hu', hr', hau, relay_bot_value S hsat hr', hp, hq, hlt, hvD,
      hamax _ hw (hp ▸ hpw)⟩
  · exact absurd hps (no_private_seed S hsat hr')

end Mordor.Relay
