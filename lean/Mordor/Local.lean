import Mordor.Restrict
import Mordor.Height5

/-!
# Semi-commutation is local to `[m, n]` (log §34.3j)

The hypothesis of semi-CL need only hold on the interval between the two candidate fixed points:
`m = n ⟺ b (a x) ≤ a (b x)` for all `x ∈ [m, n]`, provided semi-CL (or the Cut Lemma) holds on the complete lattice
`[m, n]` itself. Found by exhaustive search over the laws between the two powers (`experiments/dialgebra/laws.py`:
the restricted law holds for exactly the `F` with `m = n` on C3, C4, B2), proved here via polar reduction.
On every complete lattice of edge-height ≤ 5 the proviso is discharged (`semi_interval5`).
-/

namespace Mordor
variable {L : Type*} [CompleteLattice L] {F : L →o L →o L}

/-- The restriction of `F` to `[m, n]`, with its derived maps the restrictions of `a`, `b`. -/
theorem restrict_mn [Fact (m F ≤ n F)] :
    ∃ G : Set.Icc (m F) (n F) →o Set.Icc (m F) (n F) →o Set.Icc (m F) (n F),
      (∀ x, (a G x : L) = a F x) ∧ (∀ y, (b G y : L) = b F y) ∧ ((m G : Set.Icc (m F) (n F)) : L) = m F ∧ ((n G : Set.Icc (m F) (n F)) : L) = n F := by
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
  exact ⟨G, embed_a he hG ha, embed_b he hG hb, embed_m he hG ha hm, embed_n he hG hb hn⟩

/-- **Locality of semi-CL.** If semi-CL holds on the interval `[m, n]`, then `m = n` iff semi-commutation holds
on `[m, n]`. -/
theorem semi_interval (hmn : ∀ G : Set.Icc (m F) (n F) →o Set.Icc (m F) (n F) →o Set.Icc (m F) (n F),
      haveI : Fact (m F ≤ n F) := ⟨m_le_n⟩
      (∀ x, b G (a G x) ≤ a G (b G x)) → m G = n G) :
    m F = n F ↔ ∀ x, m F ≤ x → x ≤ n F → b F (a F x) ≤ a F (b F x) := by
  haveI : Fact (m F ≤ n F) := ⟨m_le_n⟩
  constructor
  · intro h x h1 h2
    have hx : x = m F := le_antisymm (h ▸ h2) h1
    subst hx; rw [a_m, b_m, a_m]
  · intro hloc
    obtain ⟨G, ha, hb, hm, hn⟩ := restrict_mn (F := F)
    have hsemi : ∀ x, b G (a G x) ≤ a G (b G x) := fun x => by
      show (b G (a G x) : L) ≤ a G (b G x)
      rw [hb, ha, ha, hb]; exact hloc x x.2.1 x.2.2
    have := congrArg Subtype.val (hmn G hsemi)
    rwa [hm, hn] at this

/-- **Locality, discharged at edge-height ≤ 5.** On a complete lattice with no chain of seven elements,
`m = n` iff semi-commutation holds on `[m, n]`. -/
theorem semi_interval5 (hL : Ground.NoChain L 6) :
    m F = n F ↔ ∀ x, m F ≤ x → x ≤ n F → b F (a F x) ≤ a F (b F x) := by
  haveI : Fact (m F ≤ n F) := ⟨m_le_n⟩
  refine semi_interval fun G hsemi => semi_height5 (α := Set.Icc (m F) (n F)) ?_ G hsemi
  intro x hx
  -- a strict chain in the interval is a strict chain in `L`
  have key : ∀ (k : ℕ) (y : Set.Icc (m F) (n F)), Ground.chainTo y k → Ground.chainTo (y : L) k := by
    intro k; induction k with
    | zero => intro _ _; trivial
    | succ k ih => rintro y ⟨z, hz, hzk⟩; exact ⟨z, hz, ih z hzk⟩
  exact hL _ (key 6 x hx)

end Mordor
