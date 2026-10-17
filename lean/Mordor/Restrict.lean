import Mordor.Retract
import Mathlib.Order.CompleteLatticeIntervals
import Mathlib.Data.Fintype.Order

/-!
# Restriction to closed substructures: polar reduction and the Escape Lemma (log §15.1, §24.1, §30.5)

* `embed_a`, `embed_b`, `embed_m`, `embed_n`: if a complete lattice `T` order-embeds into `L` by `e`, and `T` is
  closed under `F`, `a`, `b`, then the derived maps of the restriction are the restrictions of `a`, `b`; if `m, n`
  lie in the image, so do `μ a` and `ν b`. (The dual of `Retract.lean`.)
* `polar_reduction` (§15.1): on the interval `[m, n]` of a violator the restriction is a commuting **polar**
  configuration. `violator_of_interval`: conversely a violator on any interval `[z, z']` transports to `L` along
  the retraction `x ↦ (x ⊔ z) ⊓ z'`. So CL fails on `L` iff some interval of `L` carries a commuting polar
  configuration. (§24.1 states the pair-level reduction "on `L`"; the interval is necessary in general, as the
  README's summary has it.)
* `escape_finite` (§30.5): a finite sublattice containing `⊥, ⊤, m, n` and closed under `F, a, b` carries a
  violator; `escape_infinite`: if CL holds on all finite lattices, every such closure of a violator is infinite.
-/

namespace Mordor
universe u
variable {L : Type u} [CompleteLattice L] {F : L →o L →o L}

section Embed
variable {T : Type*} [CompleteLattice T] {e : T → L} (he : ∀ x y, e x ≤ e y ↔ x ≤ y)
  {G : T →o T →o T} (hG : ∀ x y, e (G x y) = F (e x) (e y))
include he hG

omit hG in
theorem embed_inj {x y : T} (h : e x = e y) : x = y :=
  le_antisymm ((he x y).1 h.le) ((he y x).1 h.ge)

theorem embed_a (ha : ∀ x, ∃ x', e x' = a F (e x)) (x : T) : e (a G x) = a F (e x) := by
  obtain ⟨x', hx'⟩ := ha x
  suffices h : a G x = x' by rw [h, hx']
  apply le_antisymm
  · show (G x).gfp ≤ x'
    apply OrderHom.gfp_le; intro c hc
    have h1 : e c ≤ F (e x) (e c) := hG x c ▸ (he _ _).2 hc
    exact (he _ _).1 (hx' ▸ le_a h1)
  · apply le_a; apply (he _ _).1
    rw [hG, hx', row_a]

theorem embed_b (hb : ∀ y, ∃ y', e y' = b F (e y)) (y : T) : e (b G y) = b F (e y) := by
  obtain ⟨y', hy'⟩ := hb y
  suffices h : b G y = y' by rw [h, hy']
  apply le_antisymm
  · apply b_le; apply (he _ _).1
    rw [hG, hy', col_b]
  · show y' ≤ (col G y).lfp
    apply OrderHom.le_lfp; intro c hc
    change G c y ≤ c at hc
    have h1 : F (e c) (e y) ≤ e c := hG c y ▸ (he _ _).2 hc
    exact (he _ _).1 (hy' ▸ b_le h1)

theorem embed_m (ha : ∀ x, ∃ x', e x' = a F (e x)) (hm : ∃ t, e t = m F) : e (m G) = m F := by
  obtain ⟨t, ht⟩ := hm
  suffices h : m G = t by rw [h, ht]
  apply le_antisymm
  · apply OrderHom.lfp_le_fixed
    exact embed_inj he (by rw [embed_a he hG ha, ht, a_m])
  · apply OrderHom.le_lfp; intro c hc
    have h1 : a F (e c) ≤ e c := embed_a he hG ha c ▸ (he _ _).2 hc
    exact (he _ _).1 (ht ▸ (a F).lfp_le h1)

theorem embed_n (hb : ∀ y, ∃ y', e y' = b F (e y)) (hn : ∃ t, e t = n F) : e (n G) = n F := by
  obtain ⟨t, ht⟩ := hn
  suffices h : n G = t by rw [h, ht]
  apply le_antisymm
  · apply OrderHom.gfp_le; intro c hc
    have h1 : e c ≤ b F (e c) := embed_b he hG hb c ▸ (he _ _).2 hc
    exact (he _ _).1 (ht ▸ (b F).le_gfp h1)
  · apply OrderHom.le_gfp
    exact (embed_inj he (by rw [embed_b he hG hb, ht, b_n])).ge

/-- A violator restricts to a violator on any closed substructure containing `m` and `n`. -/
theorem embed_violator (ha : ∀ x, ∃ x', e x' = a F (e x)) (hb : ∀ y, ∃ y', e y' = b F (e y))
    (hm : ∃ t, e t = m F) (hn : ∃ t, e t = n F)
    (hc : ∀ x, a F (b F x) = b F (a F x)) (hne : m F ≠ n F) :
    (∀ x, a G (b G x) = b G (a G x)) ∧ m G ≠ n G := by
  refine ⟨fun x => embed_inj he ?_, fun h => hne ?_⟩
  · rw [embed_a he hG ha, embed_b he hG hb, embed_b he hG hb, embed_a he hG ha, hc]
  · rw [← embed_m he hG ha hm, ← embed_n he hG hb hn, h]

end Embed

/-- The restriction of `F` to an interval between two common fixed points. -/
def restrictIcc (z z' : L) [Fact (z ≤ z')] (hz : F z z = z) (hz' : F z' z' = z') :
    Set.Icc z z' →o Set.Icc z z' →o Set.Icc z z' where
  toFun x := ⟨fun y => ⟨F x y, hz.ge.trans ((F.mono x.2.1 z).trans ((F x).mono y.2.1)),
      ((F x).mono y.2.2).trans ((F.mono x.2.2 z').trans hz'.le)⟩,
    fun _ _ h => (F x).mono h⟩
  monotone' _ _ h _ := F.mono h _

/-- **Polar reduction (§15.1).** For a violator, the restriction to `[m, n]` is a commuting polar configuration
whose derived maps are the restrictions of `a` and `b`. -/
theorem polar_reduction [Fact (m F ≤ n F)] (hc : ∀ x, a F (b F x) = b F (a F x)) (hne : m F ≠ n F) :
    ∃ G : Set.Icc (m F) (n F) →o Set.Icc (m F) (n F) →o Set.Icc (m F) (n F),
      (∀ x, (a G x : L) = a F x) ∧ (∀ y, (b G y : L) = b F y) ∧
      (∀ x, a G (b G x) = b G (a G x)) ∧
      a G ⊥ = ⊥ ∧ b G ⊥ = ⊥ ∧ a G ⊤ = ⊤ ∧ b G ⊤ = ⊤ ∧ (⊥ : Set.Icc (m F) (n F)) ≠ ⊤ := by
  have hmm : F (m F) (m F) = m F := by have h := row_a (F := F) (m F); rwa [a_m] at h
  have hnn : F (n F) (n F) = n F := by have h := col_b (F := F) (n F); rwa [b_n] at h
  let G := restrictIcc (F := F) (m F) (n F) hmm hnn
  have he : ∀ x y : Set.Icc (m F) (n F), (x : L) ≤ y ↔ x ≤ y := fun _ _ => Iff.rfl
  have hG : ∀ x y, ((G x y : Set.Icc (m F) (n F)) : L) = F x y := fun _ _ => rfl
  have ha : ∀ x : Set.Icc (m F) (n F), ∃ x' : Set.Icc (m F) (n F), (x' : L) = a F x := fun x =>
    ⟨⟨a F x, a_m.ge.trans ((a F).mono x.2.1), ((a F).mono x.2.2).trans a_n.le⟩, rfl⟩
  have hb : ∀ y : Set.Icc (m F) (n F), ∃ y' : Set.Icc (m F) (n F), (y' : L) = b F y := fun y =>
    ⟨⟨b F y, b_m.ge.trans ((b F).mono y.2.1), ((b F).mono y.2.2).trans b_n.le⟩, rfl⟩
  have hm : ∃ t : Set.Icc (m F) (n F), (t : L) = m F := ⟨⊥, rfl⟩
  have hn : ∃ t : Set.Icc (m F) (n F), (t : L) = n F := ⟨⊤, rfl⟩
  obtain ⟨hcG, _⟩ := embed_violator he hG ha hb hm hn hc hne
  refine ⟨G, embed_a he hG ha, embed_b he hG hb, hcG, ?_, ?_, ?_, ?_, ?_⟩
  · exact embed_inj he (by rw [embed_a he hG ha]; exact a_m)
  · exact embed_inj he (by rw [embed_b he hG hb]; exact b_m)
  · exact embed_inj he (by rw [embed_a he hG ha]; exact a_n)
  · exact embed_inj he (by rw [embed_b he hG hb]; exact b_n)
  · intro h; exact hne (congrArg Subtype.val h)

/-- **Interval violators transport to `L`** along the retraction `x ↦ (x ⊔ z) ⊓ z'`. -/
theorem violator_of_interval (z z' : L) [Fact (z ≤ z')] (G : Set.Icc z z' →o Set.Icc z z' →o Set.Icc z z')
    (hc : ∀ x, a G (b G x) = b G (a G x)) (hne : m G ≠ n G) :
    ∃ F' : L →o L →o L, (∀ x, a F' (b F' x) = b F' (a F' x)) ∧ m F' ≠ n F' := by
  have hzz : z ≤ z' := Fact.out
  let ι : Set.Icc z z' →o L := ⟨Subtype.val, fun _ _ h => h⟩
  let σ : L →o Set.Icc z z' := ⟨fun x => ⟨(x ⊔ z) ⊓ z', le_inf le_sup_right hzz, inf_le_right⟩,
    fun _ _ h => inf_le_inf_right _ (sup_le_sup_right h _)⟩
  have hσι : ∀ c, σ (ι c) = c := fun c => Subtype.ext (by
    show (c.1 ⊔ z) ⊓ z' = c.1
    rw [sup_eq_left.mpr c.2.1, inf_eq_left.mpr c.2.2])
  exact ⟨_, retract_fail hσι hc hne⟩

/-- **Escape Lemma (§30.5).** A finite sublattice containing `⊥, ⊤, m, n` and closed under `F, a, b` carries a
violator. -/
theorem escape_finite (S : Set L) (hfin : S.Finite) (hbot : ⊥ ∈ S) (htop : ⊤ ∈ S)
    (hsup : ∀ x ∈ S, ∀ y ∈ S, x ⊔ y ∈ S) (hinf : ∀ x ∈ S, ∀ y ∈ S, x ⊓ y ∈ S)
    (hFS : ∀ x ∈ S, ∀ y ∈ S, F x y ∈ S) (haS : ∀ x ∈ S, a F x ∈ S) (hbS : ∀ y ∈ S, b F y ∈ S)
    (hmS : m F ∈ S) (hnS : n F ∈ S) (hc : ∀ x, a F (b F x) = b F (a F x)) (hne : m F ≠ n F) :
    ∃ (T : Type u) (_ : CompleteLattice T) (_ : Finite T) (G : T →o T →o T),
      (∀ x, a G (b G x) = b G (a G x)) ∧ m G ≠ n G := by
  letI : Lattice S := Subtype.lattice (fun x y hx hy => hsup x hx y hy) (fun x y hx hy => hinf x hx y hy)
  letI : BoundedOrder S :=
    { top := ⟨⊤, htop⟩, le_top := fun x => (le_top : (x : L) ≤ ⊤)
      bot := ⟨⊥, hbot⟩, bot_le := fun x => (bot_le : ⊥ ≤ (x : L)) }
  letI : Fintype S := hfin.fintype
  letI : CompleteLattice S := Fintype.toCompleteLattice S
  let G : S →o S →o S := ⟨fun x => ⟨fun y => ⟨F x y, hFS x x.2 y y.2⟩, fun _ _ h => (F x).mono h⟩,
    fun _ _ h _ => F.mono h _⟩
  have he : ∀ x y : S, (x : L) ≤ y ↔ x ≤ y := fun _ _ => Iff.rfl
  have hG : ∀ x y, ((G x y : S) : L) = F x y := fun _ _ => rfl
  exact ⟨S, inferInstance, inferInstance, G, embed_violator he hG (fun x => ⟨⟨_, haS x x.2⟩, rfl⟩)
    (fun y => ⟨⟨_, hbS y y.2⟩, rfl⟩) ⟨⟨_, hmS⟩, rfl⟩ ⟨⟨_, hnS⟩, rfl⟩ hc hne⟩

/-- **Escape Lemma, contrapositive form (§30.5).** If CL holds on every finite lattice, then every substructure
of a violator that contains `⊥, ⊤, m, n` and is closed under `F, a, b, ⊔, ⊓` is infinite. -/
theorem escape_infinite (hCL : ∀ (T : Type u) [CompleteLattice T] [Finite T] (G : T →o T →o T),
      (∀ x, a G (b G x) = b G (a G x)) → m G = n G)
    (hc : ∀ x, a F (b F x) = b F (a F x)) (hne : m F ≠ n F)
    (S : Set L) (hbot : ⊥ ∈ S) (htop : ⊤ ∈ S)
    (hsup : ∀ x ∈ S, ∀ y ∈ S, x ⊔ y ∈ S) (hinf : ∀ x ∈ S, ∀ y ∈ S, x ⊓ y ∈ S)
    (hFS : ∀ x ∈ S, ∀ y ∈ S, F x y ∈ S) (haS : ∀ x ∈ S, a F x ∈ S) (hbS : ∀ y ∈ S, b F y ∈ S)
    (hmS : m F ∈ S) (hnS : n F ∈ S) : S.Infinite := fun hfin => by
  obtain ⟨T, _, _, G, hcG, hneG⟩ :=
    escape_finite S hfin hbot htop hsup hinf hFS haS hbS hmS hnS hc hne
  exact hneG (hCL T G hcG)

end Mordor
