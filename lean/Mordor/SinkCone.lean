import Mordor.WeakBase

/-!
# The sink-cone package and the cone-restricted weak base (round 26, §34.3z⁸²)

* `SinkCone F p u₀ j`: `u₀ ∉ D`; on the down-cone of `u₀` (outside `D`) `j` never transfers, no column is
  `pⱼ`-contracting, and every generator's transfer status is constant. `sinkCone_exists` packages `sink_below`.
* `cone_descent`: a failure of the cone-restricted weak base (WB-cone) descends to the reduced configuration of
  `weak_base_reduced` at a column still in the cone.
* `cone_no_anchor_contracting`: WB-cone alone (not the global weak base) excludes every `cⱼ`-contracting cone column.
* `cone_hull`: the cross-column structure of a cone column `v`: the least `pⱼ`-contracting column `μ ≥ v` exists, lies
  outside the cone, and its `cⱼ`-orbit transfers at a last point `w ≤ μ` whose whole down-set meets the cone only
  inside `D` (in particular `w ⊓ v ∈ D`).
* `self_entry_not_above_orbit`: a `j`-self-entry column is never above a pre-entry point of the `cⱼ`-orbit of a
  `pⱼ`-contracting column. So WB-cone at a reduced failure `v` reduces to the single cross-column inequality
  `(F cⱼ)^[k] μ ≤ v` for the hull `μ` of `v`.
* `orbit_avoids_cone` (correction): that inequality is impossible on a sink cone, since no pre-entry orbit point of a
  `pⱼ`-contracting column lies below `u₀`. The reduction above is therefore vacuous on the cone.
-/

namespace Mordor.Profile
open Mordor.Crossing

set_option linter.unusedSectionVars false

variable {α : Type*} [Lattice α] [BoundedOrder α] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sink-cone package. -/
structure SinkCone (F : α → α → α) (p : ι → α) (u₀ : α) (j : ι) : Prop where
  out : ¬ ∃ i, u₀ ≤ p i
  noTransfer : ∀ v, v ≤ u₀ → ¬ Transfer F p j v
  noContract : ∀ v, v ≤ u₀ → (¬ ∃ i, v ≤ p i) → ¬ F (p j) v ≤ v
  uniform : ∀ a v, v ≤ u₀ → (¬ ∃ i, v ≤ p i) → (Transfer F p a v ↔ Transfer F p a u₀)

variable {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') (p : ι → α)
  (nw : ∀ x, (∃ i, x ≤ p i) → ∀ y, ¬ (∃ i, y ≤ p i) → ¬ F x y ≤ x ∧ ¬ y ≤ F x y)

include hF nw in
theorem sinkCone_exists [WellFoundedLT α] [Nonempty ι] {s : α} (hs : ¬ ∃ i, s ≤ p i) :
    ∃ u₀, u₀ ≤ s ∧ ∃ j, SinkCone F p u₀ j ∧ ¬ Transfer F p j s := by
  obtain ⟨u, hus, hu, hunif, j, hjs, hcone, hnc⟩ := sink_below hF p nw hs
  exact ⟨u, hus, j, ⟨hu, hcone, hnc, hunif⟩, hjs⟩

include hF nw in
/-- **Cone descent.** -/
theorem cone_descent [WellFoundedLT α] {u₀ : α} {j : ι} {v : α} (hv : v ≤ u₀) (hvD : ¬ ∃ i, v ≤ p i)
    (hcv : F (anchor p j) v ≤ v) (hself : F (anchor p j) v ≤ p j) :
    ∃ w, w ≤ v ∧ w ≤ u₀ ∧ (¬ ∃ i, w ≤ p i) ∧ F (anchor p j) w ≤ w ∧ F (anchor p j) w ≤ p j ∧
      (∃ i, w ⊓ F (p j) w ≤ p i) := by
  obtain ⟨w, hwv, hw⟩ := weak_base_descent hF p nw v hvD hcv hself
  exact ⟨w, hwv, hwv.trans hv, hw⟩

include hF nw in
/-- **WB-cone excludes anchor-contracting cone columns.** -/
theorem cone_no_anchor_contracting [WellFoundedLT α] {u₀ : α} {j : ι} (hC : SinkCone F p u₀ j)
    (hwb : ∀ v, v ≤ u₀ → (¬ ∃ i, v ≤ p i) → F (anchor p j) v ≤ v → ¬ F (anchor p j) v ≤ p j)
    {u : α} (huu : u ≤ u₀) (hu : ¬ ∃ i, u ≤ p i) : ¬ F (anchor p j) u ≤ u := by
  intro hcu
  have hmono : Monotone (F (anchor p j)) := fun _ _ h => hF _ _ _ _ le_rfl h
  obtain ⟨n, hU, k, hk⟩ := FGTwo.orbit_end (InD := fun x => ∃ i, x ≤ p i) hF ⟨j, anchor_le p j⟩ nw u hu hcu
  have hanti := Monotone.antitone_iterate_of_map_le hmono hcu
  have hwu : (F (anchor p j))^[n] u ≤ u := hanti (Nat.zero_le n)
  have hwc : F (anchor p j) ((F (anchor p j))^[n] u) ≤ (F (anchor p j))^[n] u := by
    rw [← Function.iterate_succ_apply' (F (anchor p j)) n u]; exact hanti (Nat.le_succ n)
  have hkj : k = j := by
    by_contra hne; exact hC.noTransfer _ (hwu.trans huu) ⟨hU n le_rfl, k, hne, hk⟩
  exact hwb _ (hwu.trans huu) (hU n le_rfl) hwc (hkj ▸ hk)

include hF nw in
/-- **The contracting hull of a cone column.** -/
theorem cone_hull [WellFoundedLT α] {u₀ : α} {j : ι} (hC : SinkCone F p u₀ j) {v : α}
    (hvD : ¬ ∃ i, v ≤ p i) :
    ∃ μ, v ≤ μ ∧ F (p j) μ ≤ μ ∧ ¬ μ ≤ u₀ ∧ (∀ y, v ≤ y → F (p j) y ≤ y → μ ≤ y) ∧
      ∃ w, w ≤ μ ∧ Transfer F p j w ∧ ∀ x, x ≤ w → x ≤ u₀ → ∃ i, x ≤ p i := by
  obtain ⟨μ, ⟨hvμ, hμ⟩, hmin⟩ :=
    (wellFounded_lt (α := α)).has_min {y | v ≤ y ∧ F (p j) y ≤ y} ⟨⊤, le_top, le_top⟩
  have hμD : ¬ ∃ i, μ ≤ p i := fun ⟨i, hi⟩ => hvD ⟨i, hvμ.trans hi⟩
  have hleast : ∀ y, v ≤ y → F (p j) y ≤ y → μ ≤ y := fun y hvy hy => by
    have hm : μ ⊓ y ∈ {y | v ≤ y ∧ F (p j) y ≤ y} :=
      ⟨le_inf hvμ hvy, le_inf ((hF _ _ _ _ le_rfl inf_le_left).trans hμ) ((hF _ _ _ _ le_rfl inf_le_right).trans hy)⟩
    have : μ ⊓ y = μ := eq_of_le_of_not_lt inf_le_left (hmin _ hm)
    exact this ▸ inf_le_right
  obtain ⟨w, hwμ, hw⟩ := transfer_below_contracting hF p nw hμD hμ
  refine ⟨μ, hvμ, hμ, fun h => hC.noContract μ h hμD hμ, hleast, w, hwμ, hw, fun x hxw hxu => ?_⟩
  by_contra hx
  exact hC.noTransfer x hxu (transfer_down hF p hxw hx hw)

include hF nw in
/-- **The missing comparison, as a reduction.** A column `v` where `j` self-enters is never above a pre-entry point of
the `F cⱼ`-orbit of a `pⱼ`-contracting column `s`: the next orbit value would be below `F cⱼ v ≤ pⱼ`, either inside `D`
too early or as an entry below `pⱼ` (`anchor_sandwich`). So WB-cone at a reduced failure `v` would follow from a single
inequality `(F cⱼ)^[k] μ ≤ v` (`k ≤` the entry time) for the contracting hull `μ` of `v` (`cone_hull`). -/
theorem self_entry_not_above_orbit [WellFoundedLT α] {j : ι} {s : α} (hs : ¬ ∃ i, s ≤ p i)
    (hgs : F (p j) s ≤ s) {n : ℕ} (hU : ∀ k ≤ n, ¬ ∃ i, (F (anchor p j))^[k] s ≤ p i)
    {v : α} (hself : F (anchor p j) v ≤ p j) {k : ℕ} (hk : k ≤ n) (hkv : (F (anchor p j))^[k] s ≤ v) : False := by
  have hnext : F (anchor p j) ((F (anchor p j))^[k] s) ≤ p j := (hF _ _ _ _ le_rfl hkv).trans hself
  rcases Nat.lt_or_ge k n with hlt | hge
  · exact hU (k + 1) hlt ⟨j, by rwa [Function.iterate_succ_apply']⟩
  · have hkn : k = n := le_antisymm hk hge
    subst hkn
    exact anchor_sandwich hF p j nw hs hgs k hU hnext

include hF nw in
/-- **Orbits of contracting columns avoid the cone** (correction to §34.3z⁸²). No pre-entry point of the `F cⱼ`-orbit of
a `pⱼ`-contracting column lies below `u₀`: the orbit descends, so its last point would be a cone column, and it transfers
(`anchor_sandwich`). Hence the inequality `(F cⱼ)^[k] μ ≤ v` proposed in §34.3z⁸² as the missing step is refuted by the
cone package itself; establishing it would be a proof of Cut, not a step towards WB-cone. -/
theorem orbit_avoids_cone [WellFoundedLT α] {u₀ : α} {j : ι} (hC : SinkCone F p u₀ j) {s : α}
    (hs : ¬ ∃ i, s ≤ p i) (hgs : F (p j) s ≤ s) {n : ℕ} (hU : ∀ k ≤ n, ¬ ∃ i, (F (anchor p j))^[k] s ≤ p i)
    (hin : ∃ i, F (anchor p j) ((F (anchor p j))^[n] s) ≤ p i) {k : ℕ} (hk : k ≤ n) :
    ¬ (F (anchor p j))^[k] s ≤ u₀ := by
  intro hku
  have hcs : F (anchor p j) s ≤ s := (hF _ _ _ _ (anchor_le p j) le_rfl).trans hgs
  have hanti := Monotone.antitone_iterate_of_map_le (fun _ _ h => hF _ _ _ _ le_rfl h) hcs
  have hout := anchor_sandwich hF p j nw hs hgs n hU
  obtain ⟨i, hi⟩ := hin
  have hij : i ≠ j := fun e => hout (e ▸ hi)
  exact hC.noTransfer _ ((hanti hk).trans hku) ⟨hU n le_rfl, i, hij, hi⟩

end Mordor.Profile
