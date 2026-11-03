import Mordor.GlobalEnvelope

/-!
# Finite support of global boundaries (round 26, §34.3z⁹⁷)

Response to the brief "finite boundary support and provenance-preserving certificates". Independent of `F` and `D`:

* `iSup_finite_support` (ACC): every indexed supremum is attained on a finite index set (a maximal finite partial join,
  which exists by ACC, is an upper bound: adding one more index cannot raise it).
* `iInf_finite_support` (DCC): dually for infima.
* `finite_envelope_support`: the envelope ends `d = ⨅ lᵢ`, `u = ⨆ uᵢ` have (separate) finite supports.
* `finite_squeeze_support`: so do the squeeze values `⨆_{v∈A} F d (y v)` and `⨅_{w∈B} F (x w) u`.
* `prefixClosure`, `subset_prefixClosure`, `prefixClosure_closed`: for tree nodes as binary words, the prefix closure
  of a finite support is finite and prefix-closed; any index set between a support and the whole family preserves the
  value (`support_between`).
-/

namespace Mordor.Profile

set_option linter.unusedSectionVars false

variable {L : Type*} [CompleteLattice L]

/-- **Finite support of suprema** (ACC). -/
theorem iSup_finite_support [WellFoundedGT L] {I : Type*} (s : I → L) :
    ∃ J : Finset I, ⨆ i, s i = J.sup s := by
  classical
  obtain ⟨_, ⟨J, rfl⟩, hmax⟩ := (wellFounded_gt (α := L)).has_min (Set.range fun J : Finset I => J.sup s)
    ⟨_, ∅, rfl⟩
  refine ⟨J, le_antisymm (iSup_le fun i => ?_) (Finset.sup_le fun i _ => le_iSup s i)⟩
  by_contra h
  have hlt : J.sup s < (insert i J).sup s := by
    rw [Finset.sup_insert]
    exact lt_of_le_of_ne le_sup_right fun e => h (e ▸ le_sup_left)
  exact hmax _ ⟨insert i J, rfl⟩ hlt

/-- **Finite support of infima** (DCC). -/
theorem iInf_finite_support [WellFoundedLT L] {I : Type*} (s : I → L) :
    ∃ J : Finset I, ⨅ i, s i = J.inf s := by
  classical
  obtain ⟨_, ⟨J, rfl⟩, hmin⟩ := (wellFounded_lt (α := L)).has_min (Set.range fun J : Finset I => J.inf s)
    ⟨_, ∅, rfl⟩
  refine ⟨J, le_antisymm (Finset.le_inf fun i _ => iInf_le s i) (le_iInf fun i => ?_)⟩
  by_contra h
  have hlt : (insert i J).inf s < J.inf s := by
    rw [Finset.inf_insert]
    exact lt_of_le_of_ne inf_le_right fun e => h (e ▸ inf_le_left)
  exact hmin _ ⟨insert i J, rfl⟩ hlt

/-- **Finite support of the envelope** (DCC for `d`, ACC for `u`; separate supports). -/
theorem finite_envelope_support [WellFoundedLT L] [WellFoundedGT L] {V : Type*} (l u : V → L) :
    (∃ Jd : Finset V, ⨅ v, l v = Jd.inf l) ∧ (∃ Ju : Finset V, ⨆ v, u v = Ju.sup u) :=
  ⟨iInf_finite_support l, iSup_finite_support u⟩

/-- **Finite support of the squeeze values.** -/
theorem finite_squeeze_support [WellFoundedLT L] [WellFoundedGT L] {V : Type*} (F : L → L → L) (x y : V → L)
    (d u : L) (A B : Set V) :
    (∃ JA : Finset A, ⨆ v : A, F d (y v) = JA.sup fun v => F d (y v)) ∧
    (∃ JB : Finset B, ⨅ w : B, F (x w) u = JB.inf fun w => F (x w) u) :=
  ⟨iSup_finite_support _, iInf_finite_support _⟩

/-- Any index set between a support and everything preserves the supremum. -/
theorem support_between {I : Type*} (s : I → L) {J K : Finset I} (hJ : ⨆ i, s i = J.sup s) (hJK : J ⊆ K) :
    ⨆ i, s i = K.sup s :=
  le_antisymm (hJ ▸ Finset.sup_mono hJK) (Finset.sup_le fun i _ => le_iSup s i)

/-- Prefix closure of a finite set of binary words (tree nodes). -/
def prefixClosure (S : Finset (List Bool)) : Finset (List Bool) := S.biUnion fun w => w.inits.toFinset

theorem subset_prefixClosure (S : Finset (List Bool)) : S ⊆ prefixClosure S := fun w hw =>
  Finset.mem_biUnion.2 ⟨w, hw, List.mem_toFinset.2 (List.mem_inits _ _ |>.2 (List.prefix_refl w))⟩

theorem prefixClosure_closed (S : Finset (List Bool)) {w v : List Bool} (hw : w ∈ prefixClosure S)
    (hv : v <+: w) : v ∈ prefixClosure S := by
  obtain ⟨u, hu, hwu⟩ := Finset.mem_biUnion.1 hw
  have hwu' : w <+: u := (List.mem_inits _ _).1 (List.mem_toFinset.1 hwu)
  exact Finset.mem_biUnion.2 ⟨u, hu, List.mem_toFinset.2 ((List.mem_inits _ _).2 (hv.trans hwu'))⟩

end Mordor.Profile
