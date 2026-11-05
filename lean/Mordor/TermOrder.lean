import Mordor.Stable
import Mathlib.Order.WellFoundedSet

/-!
# Work package B diagnostics: well-quasi-orders on the cross-closure (round 26, §34.3z¹⁰⁷)

* `finite_of_pwo_chainFinite`: in a poset with ACC, a partially well-ordered set is finite (a monotone subsequence of
  an injective sequence is a strictly increasing chain). Hence the brief's lemma B1 ("the cross-closure of a
  counterexample is a WQO") is not an intermediate step: by `crossClosure_infinite` it is *equivalent* to the
  nonexistence of a counterexample for that `F` (`crossClosure_not_pwo`).
* `kruskal_step_strict`: the subterm `F(⊥, ⊤)` homeomorphically embeds in `F(⊥, F(⊥, ⊤))`, yet when `F(⊥, ⊤) ∉ D`
  no witness forces `F ⊥ (F ⊥ ⊤) < F ⊥ ⊤`. So Kruskal embedding is order-*reversing* on this pair: the
  evaluation-sound syntactic relations are leaf substitutions (`⊥`-leaves upward, `⊤`-leaves downward), which are
  not well-quasi-orders (the row orbit terms `(F ⊥ ·)^[n] ⊤` are pairwise incomparable under them).
-/

namespace Mordor.TermOrder

/-- A partially well-ordered subset of a poset with ACC is finite. -/
theorem finite_of_pwo_chainFinite {α : Type*} [PartialOrder α] [WellFoundedGT α] {s : Set α}
    (h : s.PartiallyWellOrderedOn (· ≤ ·)) : s.Finite := by
  by_contra hinf
  let e := Set.Infinite.natEmbedding s hinf
  let f : ℕ → α := fun n => (e n : α)
  obtain ⟨g, hg⟩ := h.exists_monotone_subseq (f := f) (fun n => (e n).2)
  have hinj : ∀ m n, f (g m) = f (g n) → m = n := fun m n he =>
    g.injective (e.injective (Subtype.ext he))
  have hsm : ∀ n, f (g n) < f (g (n + 1)) := fun n =>
    lt_of_le_of_ne (hg n (n + 1) (Nat.le_succ n)) fun he => by have := hinj _ _ he; omega
  obtain ⟨n, hn⟩ := WellFounded.not_rel_apply_succ (r := (· > ·)) (fun n => f (g n))
  exact hn (hsm n)

/-- **B1 is the conjecture itself**: in a counterexample on a lattice with ACC, the cross-closure is not a WQO. -/
theorem crossClosure_not_pwo {α : Type*} [CompleteLattice α] [WellFoundedGT α] (F : α →o α →o α)
    (h : R F ≠ Set.univ) : ¬ (crossClosure F).PartiallyWellOrderedOn (· ≤ ·) := fun hp =>
  crossClosure_infinite h (finite_of_pwo_chainFinite hp)

/-- **Kruskal embedding is not evaluation-monotone.** -/
theorem kruskal_step_strict {α : Type*} [Lattice α] [BoundedOrder α] {F : α → α → α}
    (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y') {D : Set α} (hbot : ⊥ ∈ D)
    (nw : ∀ x ∈ D, ∀ y ∉ D, ¬ F x y ≤ x ∧ ¬ y ≤ F x y) (hv : F ⊥ ⊤ ∉ D) :
    F ⊥ (F ⊥ ⊤) < F ⊥ ⊤ :=
  lt_of_le_of_ne (hF _ _ _ _ le_rfl le_top) fun he => (nw ⊥ hbot _ hv).2 he.ge

end Mordor.TermOrder
