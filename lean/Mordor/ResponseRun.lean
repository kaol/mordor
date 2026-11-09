import Mordor.ShortestRun
import Mordor.SeparatorAncestry

/-!
# The response process and its finite transfer (round 26, §34.3z¹³¹)

The *response process* uses the response `F x y` itself as the separator of every bad pair (a separator whenever the
pair is not stuck): `respStep T = meetClose (T ∪ {F x y | (x, y) bad in T})`, run from `{⊥, ⊤}` and frozen at goal
stages. Its legality refers only to `T`, the responses of its pairs, order and `D`; no maximality.

* `respRun_closed`: every stage is meet-closed and contains `⊥, ⊤`; `cut_of_resp_goal`: a goal stage gives a witness
  (`terminal_witness`).
* `subLattice`: a finite inf-closed `S ∋ ⊥, ⊤` is a finite bounded lattice in the induced order (joins are least upper
  bounds within `S`).
* `resp_transfer` (**finite transfer**): if every *finite* lattice of edge-height `≤ H` has a response run that reaches a
  goal by stage `N`, then so does every lattice of edge-height `≤ H`; hence Cut there (`cut_of_resp_bound`). The
  finite witness is the meet-closure of the first `N + 1` stages and their responses, with `F' = cl ∘ F`.
-/

namespace Mordor.ResponseRun
open Finset Classical Mordor.SeparatorStages Mordor.ShortestRun Mordor.FiniteQuotient Mordor.SeparatorAncestry

set_option linter.unusedSectionVars false

universe u

section Process

variable {α : Type u} [Lattice α] [BoundedOrder α] (F : α → α → α) (D : Set α)

/-- The bad pairs of a stage (classical). -/
noncomputable def bads (T : Finset α) : Finset (α × α) := (T ×ˢ T).filter fun p => Bad F D T p.1 p.2

/-- One response step. -/
noncomputable def respStep (T : Finset α) : Finset α := meetClose (T ∪ (bads F D T).image fun p => F p.1 p.2)

/-- The response run, frozen at goal stages. -/
noncomputable def respRun : ℕ → Finset α
  | 0 => {⊥, ⊤}
  | n + 1 => if Goal F D (respRun n) then respRun n else respStep F D (respRun n)

variable {F D}

theorem respRun_closed : ∀ n, ⊥ ∈ respRun F D n ∧ ⊤ ∈ respRun F D n ∧
    ∀ a ∈ respRun F D n, ∀ b ∈ respRun F D n, a ⊓ b ∈ respRun F D n
  | 0 => ⟨by simp [respRun], by simp [respRun], fun a ha b hb => by
      simp only [respRun, Finset.mem_insert, Finset.mem_singleton] at ha hb ⊢
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp⟩
  | n + 1 => by
    have ih := respRun_closed n
    simp only [respRun]
    split_ifs
    · exact ih
    · exact ⟨subset_meetClose _ (Finset.mem_union_left _ ih.1), top_mem_meetClose _, meetClose_closed _⟩

theorem cut_of_resp_goal (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) {n : ℕ} (hg : Goal F D (respRun F D n)) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y := by
  obtain ⟨hb, ht, hc⟩ := respRun_closed (F := F) (D := D) n
  rcases hg with h | ⟨x, y, hxy, hst⟩
  · exact terminal_witness hF hD hbot htop hb ht hc h
  · exact ⟨x, hxy.2.1, y, hxy.2.2.2.1, Or.inr hst⟩

end Process

section Sub

variable {α : Type u} [Lattice α] [BoundedOrder α] {S : Finset α}

/-- The lattice structure on a finite inf-closed subset containing `⊥, ⊤`. -/
noncomputable def subLattice (htS : ⊤ ∈ S) (hcl : ∀ a ∈ S, ∀ b ∈ S, a ⊓ b ∈ S) : Lattice {x // x ∈ S} :=
  { (inferInstance : PartialOrder {x // x ∈ S}) with
    inf := fun a b => ⟨a.1 ⊓ b.1, hcl _ a.2 _ b.2⟩
    inf_le_left := fun a b => (inf_le_left : a.1 ⊓ b.1 ≤ a.1)
    inf_le_right := fun a b => (inf_le_right : a.1 ⊓ b.1 ≤ b.1)
    le_inf := fun a b c hab hac => (le_inf hab hac : a.1 ≤ b.1 ⊓ c.1)
    sup := fun a b => ⟨cl S (a.1 ⊔ b.1), inf_mem_of_closed htS hcl _ (Finset.filter_subset _ _)⟩
    le_sup_left := fun a b => (le_sup_left.trans (le_cl S _) : a.1 ≤ cl S (a.1 ⊔ b.1))
    le_sup_right := fun a b => (le_sup_right.trans (le_cl S _) : b.1 ≤ cl S (a.1 ⊔ b.1))
    sup_le := fun a b c hac hbc => (cl_le c.2 (sup_le hac hbc) : cl S (a.1 ⊔ b.1) ≤ c.1) }

end Sub

section Transfer

variable {α : Type u} [Lattice α] [BoundedOrder α]

/-- A finite inf-closed subset containing `⊥, ⊤`. -/
class SubOK (S : Finset α) : Prop where
  top : ⊤ ∈ S
  bot : ⊥ ∈ S
  cl : ∀ a ∈ S, ∀ b ∈ S, a ⊓ b ∈ S

variable (S : Finset α) [h : SubOK S]

noncomputable instance subLat : Lattice {x // x ∈ S} := subLattice h.top h.cl
instance subTop : OrderTop {x // x ∈ S} := Subtype.orderTop (p := (· ∈ S)) h.top
instance subBot : OrderBot {x // x ∈ S} := Subtype.orderBot (p := (· ∈ S)) h.bot
instance subBounded : BoundedOrder {x // x ∈ S} := { }

/-- The embedding of `S` into `α`. -/
def ι : {x // x ∈ S} ↪ α := Function.Embedding.subtype _

theorem val_inf_finset : ∀ B : Finset {x // x ∈ S}, (B.inf id).1 = (B.map (ι S)).inf id := by
  intro B
  induction B using Finset.induction_on with
  | empty => rfl
  | insert a B ha ih =>
    rw [Finset.inf_insert, Finset.map_insert, Finset.inf_insert]
    show a.1 ⊓ _ = _
    rw [ih]; rfl

theorem map_meetClose [DecidableEq {x // x ∈ S}] [DecidableEq α] (A : Finset {x // x ∈ S}) :
    (meetClose A).map (ι S) = meetClose (A.map (ι S)) := by
  ext e
  simp only [Finset.mem_map, mem_meetClose_iff]
  constructor
  · rintro ⟨a, ⟨B, hB, rfl⟩, rfl⟩
    exact ⟨B.map (ι S), Finset.map_subset_map.2 hB, (val_inf_finset S B).symm⟩
  · rintro ⟨B, hB, rfl⟩
    obtain ⟨B', hB', rfl⟩ := Finset.subset_map_iff.1 hB
    exact ⟨B'.inf id, ⟨B', hB', rfl⟩, val_inf_finset S B'⟩

variable (F : α → α → α) (D : Set α)

/-- The induced bifunction `cl_S ∘ F` on `S`. -/
noncomputable def G' : {x // x ∈ S} → {x // x ∈ S} → {x // x ∈ S} := fun a b =>
  ⟨cl S (F a.1 b.1), inf_mem_of_closed h.top h.cl _ (Finset.filter_subset _ _)⟩

def D' : Set {x // x ∈ S} := {a | a.1 ∈ D}

variable {S}

theorem cl_le_iff {z s : α} (hs : s ∈ S) : cl S z ≤ s ↔ z ≤ s :=
  ⟨fun h' => (le_cl S z).trans h', fun h' => cl_le hs h'⟩

theorem cl_self {z : α} (hz : z ∈ S) : cl S z = z := le_antisymm (cl_le hz le_rfl) (le_cl S z)

theorem mem_map_iff {U : Finset {x // x ∈ S}} {x : {x // x ∈ S}} : x.1 ∈ U.map (ι S) ↔ x ∈ U :=
  Finset.mem_map' (ι S)

theorem bad_iff (U : Finset {x // x ∈ S}) (x y : {x // x ∈ S}) :
    Bad (G' S F) (D' S D) U x y ↔ Bad F D (U.map (ι S)) x.1 y.1 := by
  unfold Bad Separated
  rw [mem_map_iff, mem_map_iff]
  apply and_congr Iff.rfl; apply and_congr Iff.rfl; apply and_congr Iff.rfl; apply and_congr Iff.rfl
  apply not_congr
  constructor
  · rintro ⟨s', hs', h1, h2⟩
    exact ⟨s'.1, mem_map_iff.2 hs', (cl_le_iff s'.2).1 h1, h2⟩
  · rintro ⟨e, he, h1, h2⟩
    obtain ⟨s', hs', rfl⟩ := Finset.mem_map.1 he
    exact ⟨s', hs', (cl_le_iff s'.2).2 h1, h2⟩

theorem lift_bad {U : Finset {x // x ∈ S}} {a b : α} (hb : Bad F D (U.map (ι S)) a b) :
    ∃ x y : {x // x ∈ S}, x.1 = a ∧ y.1 = b ∧ Bad (G' S F) (D' S D) U x y := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 hb.1
  obtain ⟨y, -, rfl⟩ := Finset.mem_map.1 hb.2.2.1
  exact ⟨x, y, rfl, rfl, (bad_iff F D U x y).2 hb⟩

theorem goal_iff (U : Finset {x // x ∈ S}) (hresp : ∀ x ∈ U, ∀ y ∈ U, F x.1 y.1 ∈ S) :
    Goal (G' S F) (D' S D) U ↔ Goal F D (U.map (ι S)) := by
  have hst : ∀ x y, Bad (G' S F) (D' S D) U x y → (y ≤ G' S F x y ↔ y.1 ≤ F x.1 y.1) := fun x y hb => by
    show y.1 ≤ cl S (F x.1 y.1) ↔ _
    rw [cl_self (hresp x hb.1 y hb.2.2.1)]
  constructor
  · rintro (h' | ⟨x, y, hb, hy⟩)
    · left; intro a b hb
      obtain ⟨x, y, rfl, rfl, hb'⟩ := lift_bad F D hb
      exact h' x y hb'
    · right; exact ⟨x.1, y.1, (bad_iff F D U x y).1 hb, (hst x y hb).1 hy⟩
  · rintro (h' | ⟨a, b, hb, hy⟩)
    · left; intro x y hb; exact h' x.1 y.1 ((bad_iff F D U x y).1 hb)
    · right
      obtain ⟨x, y, rfl, rfl, hb'⟩ := lift_bad F D hb
      exact ⟨x, y, hb', (hst x y hb').2 hy⟩

theorem step_map (U : Finset {x // x ∈ S}) (hresp : ∀ x ∈ U, ∀ y ∈ U, F x.1 y.1 ∈ S) :
    (respStep (G' S F) (D' S D) U).map (ι S) = respStep F D (U.map (ι S)) := by
  unfold respStep
  rw [map_meetClose]
  congr 1
  ext e
  simp only [Finset.mem_map, Finset.mem_union, Finset.mem_image, bads, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨a, ha | ⟨p, ⟨⟨hp1, hp2⟩, hpb⟩, rfl⟩, rfl⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · refine Or.inr ⟨(p.1.1, p.2.1), ⟨⟨⟨p.1, hp1, rfl⟩, ⟨p.2, hp2, rfl⟩⟩, (bad_iff F D U p.1 p.2).1 hpb⟩, ?_⟩
      show F p.1.1 p.2.1 = cl S (F p.1.1 p.2.1)
      rw [cl_self (hresp _ hp1 _ hp2)]
  · rintro (⟨a, ha, rfl⟩ | ⟨q, ⟨-, hqb⟩, rfl⟩)
    · exact ⟨a, Or.inl ha, rfl⟩
    · obtain ⟨x, y, hx, hy, hb'⟩ := lift_bad F D hqb
      refine ⟨G' S F x y, Or.inr ⟨(x, y), ⟨⟨hb'.1, hb'.2.2.1⟩, hb'⟩, rfl⟩, ?_⟩
      show cl S (F x.1 y.1) = F q.1 q.2
      rw [cl_self (hresp _ hb'.1 _ hb'.2.2.1), hx, hy]

theorem run_map {N : ℕ} (hS : ∀ m ≤ N, ∀ a ∈ respRun F D m, ∀ b ∈ respRun F D m, F a b ∈ S) :
    ∀ n ≤ N, (respRun (G' S F) (D' S D) n).map (ι S) = respRun F D n := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [respRun, Finset.map_insert, Finset.map_singleton]; rfl
  | succ n ih =>
    intro hn
    have ih' := ih (by omega)
    have hresp : ∀ x ∈ respRun (G' S F) (D' S D) n, ∀ y ∈ respRun (G' S F) (D' S D) n, F x.1 y.1 ∈ S :=
      fun x hx y hy => hS n (by omega) _ (ih' ▸ mem_map_iff.2 hx) _ (ih' ▸ mem_map_iff.2 hy)
    have hg := goal_iff F D _ hresp
    rw [ih'] at hg
    simp only [respRun]
    by_cases hG : Goal F D (respRun F D n)
    · rw [if_pos (hg.2 hG), if_pos hG, ih']
    · rw [if_neg (fun h' => hG (hg.1 h')), if_neg hG, step_map F D _ hresp, ih']

theorem chainTo_val_sub : ∀ (k : ℕ) (z : {x // x ∈ S}), Mordor.Ground.chainTo z k → Mordor.Ground.chainTo z.1 k
  | 0, _, _ => trivial
  | k + 1, _, ⟨w, hw, hc⟩ => ⟨w.1, hw, chainTo_val_sub k w hc⟩

end Transfer

/-- **Finite transfer of a uniform response bound.** If every finite lattice of edge-height `≤ H` has a response run
that reaches a goal by stage `N`, every lattice of edge-height `≤ H` does. -/
theorem resp_transfer {α : Type u} [Lattice α] [BoundedOrder α] {H N : ℕ}
    (hfin : ∀ (β : Type u) [Lattice β] [BoundedOrder β] [Fintype β], Mordor.Ground.NoChain β (H + 1) →
      ∀ G : β → β → β, (∀ x x' y y', x ≤ x' → y ≤ y' → G x y ≤ G x' y') →
      ∀ E : Set β, (∀ x y, x ≤ y → y ∈ E → x ∈ E) → ⊥ ∈ E → ⊤ ∉ E → Goal G E (respRun G E N))
    (hn : Mordor.Ground.NoChain α (H + 1)) {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) :
    Goal F D (respRun F D N) := by
  let E : Finset α := (Finset.range (N + 1)).biUnion fun m =>
    respRun F D m ∪ (respRun F D m ×ˢ respRun F D m).image fun p => F p.1 p.2
  let S : Finset α := meetClose (insert ⊥ E)
  haveI hS : SubOK S := ⟨top_mem_meetClose _, subset_meetClose _ (Finset.mem_insert_self _ _), meetClose_closed _⟩
  have hresp : ∀ m ≤ N, ∀ a ∈ respRun F D m, ∀ b ∈ respRun F D m, F a b ∈ S := fun m hm a ha b hb =>
    subset_meetClose _ (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨m, Finset.mem_range.2 (by omega),
      Finset.mem_union_right _ (Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩, rfl⟩)⟩))
  have hnS : Mordor.Ground.NoChain {x // x ∈ S} (H + 1) := fun z hz => hn z.1 (chainTo_val_sub (H + 1) z hz)
  have hgoal := hfin {x // x ∈ S} hnS (G' S F)
    (fun x x' y y' hx hy => (cl_mono S (hF _ _ _ _ hx hy) : cl S (F x.1 y.1) ≤ cl S (F x'.1 y'.1))) (D' S D)
    (fun x y hxy hy => hD _ _ hxy hy) hbot htop
  have hmap := run_map F D hresp N le_rfl
  have hr : ∀ x ∈ respRun (G' S F) (D' S D) N, ∀ y ∈ respRun (G' S F) (D' S D) N, F x.1 y.1 ∈ S :=
    fun x hx y hy => hresp N le_rfl _ (hmap ▸ mem_map_iff.2 hx) _ (hmap ▸ mem_map_iff.2 hy)
  have := (goal_iff F D _ hr).1 hgoal
  rwa [hmap] at this

/-- **Uniform response bound ⇒ Cut** at edge-height `≤ H`, for every lattice (finite or not). -/
theorem cut_of_resp_bound {α : Type u} [Lattice α] [BoundedOrder α] {H N : ℕ}
    (hfin : ∀ (β : Type u) [Lattice β] [BoundedOrder β] [Fintype β], Mordor.Ground.NoChain β (H + 1) →
      ∀ G : β → β → β, (∀ x x' y y', x ≤ x' → y ≤ y' → G x y ≤ G x' y') →
      ∀ E : Set β, (∀ x y, x ≤ y → y ∈ E → x ∈ E) → ⊥ ∈ E → ⊤ ∉ E → Goal G E (respRun G E N))
    (hn : Mordor.Ground.NoChain α (H + 1)) {F : α → α → α} (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    {D : Set α} (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) :
    ∃ x ∈ D, ∃ y ∉ D, F x y ≤ x ∨ y ≤ F x y :=
  cut_of_resp_goal hF hD hbot htop (resp_transfer hfin hn hF hD hbot htop)

end Mordor.ResponseRun
