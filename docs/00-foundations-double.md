# Mordor — Double-Categorical Axioms Framework (draft, round 26)

This document raises the axioms of [`00-foundations.md`](00-foundations.md) (v3.8) to double categories:
- horizontal axioms are monads,
- vertical axioms are comonads,
- every axiom is a square,
- dialgebraic axioms are cells between two double functors,
- bounds are tabulators and cotabulators,
- interaction rules are interchange, mates and companion/conjoint cells.

It starts from an outside draft (ChatGPT, 2026-11) and corrects it. The corrections are listed in §0. Status tags are
as in the foundations: **Def** (definition), **Post** (postulate on the ambient double category), **Thm** (proved,
with a Lean name where mechanized), **Cond** (holds under a stated condition), **False** (refuted), **Open**.

The single most important point, for the research program: **the thin model of one complete lattice is a quintet
double category**, so a "no quintet" *axiom* would exclude every model where Mordor's results live. The model that
does carry the Cut Lemma is not a quintet: it is the **equipment of monotone maps and down-set relations** on L
(§7). In it the open bridge (§7.6 of the foundations) is precisely a **representability condition**: the initial
algebra R(F) = μΘ, a presheaf on L, must be representable (a principal down-set). That is the framework's one
genuine reading of the problem, and it gives no new proof (§8).

---

## 0. Corrections to the draft

| # | Draft | Problem | Here |
|---|---|---|---|
| C1 | NC1 "no quintet reduction" as an axiom | The thin model of a lattice L (the setting of all research results, foundations §1.1) is the quintet Q(L): horizontal and vertical arrows are both ≤, and every boundary commutes. NC1 would exclude it. | NC1 is a *non-assumption*: nothing may be derived from horizontal = vertical. Quintets are admissible models. §7.1 |
| C2 | Hμ4: "a unique horizontal algebra morphism fold(a) : μS ⇝ A", drawn as the *vertical* sides of its square | Type error. For a horizontal endo-arrow, algebra morphisms are vertical (Fiore–Gambino–Kock's convention). Dually Vν4's ana(c) is drawn horizontal but declared vertical. | Algebras of horizontal monads have vertical morphisms; coalgebras of vertical comonads have horizontal morphisms. §2, §3 |
| C3 | "Tabulator of an axiom cell", Bd1 = Tab(η_T), … | Tabulators and cotabulators are defined for horizontal (loose) arrows, not for cells. A cell α : h ⇒ k induces a vertical arrow Tab(h) → Tab(k). | Bounds are tabulators of the axiom arrows, plus the induced arrows of the axiom cells. §5 |
| C4 | Bd1–Bd8 replace the foundations' bounds | The order-theoretic bounds (Knaster–Tarski, μ ≤ ν, ordinal approximation) are not tabulators. Dropping them loses I1 (m ≤ n). | Bd1–Bd9 of the foundations are kept as the thin layer; tabulators are an additional universal layer. §5 |
| C5 | "Double-categorical Mordor Commutation Theorem" | Its hypothesis 6 is the Cut condition. In the thin model hypotheses 1–5 hold or are vacuous, and the theorem is `Source.guard` (Cut ∧ law ⟹ m = n), already proved. | Stated as a corollary (§8); `Axioms.Double.double_commutation_thin`. |
| C6 | Fiore–Gambino–Kock "Theorem 10.3" (representability of the parameterized algebra presheaf ⟺ Eilenberg–Moore objects) | Cited by the draft; the theorem number and exact form are **not checked here**. | Kept as a cited postulate shape (§5.2), tagged Lit/unverified. |
| C7 | The mixed distributive law λ : T ⊙ D_* ⇒ D_* ⊙ T | Moving D to the horizontal direction through its companion is a quintet-style reduction for the arrows involved. Fine, but it is the *only* place where the two directions interact. | Stated as such (§6.4). |

---

## 1. Ambient

| Symbol | Meaning |
|---|---|
| 𝔻 | A pseudo double category: objects; horizontal arrows h : X ⇸ Y (*construction*); vertical arrows v : X → Y (*observation*); squares. |
| ⊙_h, ⊙_v; I^h_X, I^v_X | Horizontal and vertical composition and identities. |
| 𝔻_h, 𝔻_v | The horizontal bicategory (objects, horizontal arrows, globular squares) and the vertical 2-category. |
| F : 𝔻 × 𝔻 → 𝔻 | The signature, a double functor of two variables: X the making (μ) variable, Y the watching (ν) variable (foundations §1.2). |
| S, B : 𝔻 → 𝔻 | One-variable signatures: syntax and behaviour. |

**A0 (Post).** Squares are primitive; no identification of horizontal with vertical arrows is assumed. Companions and
conjoints (§6.2) exist only where stated.

**A1 (Post, as needed).** The free horizontal monad T_S on S_h and the cofree vertical comonad D_B on B_v exist
where used (Fiore–Gambino–Kock's free-monad construction in double categories is the model).

---

## 2. Horizontal axioms: monads (μ-layer)

A **horizontal monad** on X is T : X ⇸ X with squares η : I^h_X ⇒ T and μ : T ⊙_h T ⇒ T, both with vertical identity
sides, satisfying associativity and unit laws as equalities of pasted squares (**Def**). Its algebras are pairs
(A, α : A-boundary square), and their **morphisms are vertical arrows** with a square (C2).

| # | Square | Thin reading (L complete, Q(L)) | Status |
|---|---|---|---|
| Hμ1 | unit η : I^h ⇒ T | x ≤ T x for the closure T of f | Def |
| Hμ2 | multiplication μ : T ⊙_h T ⇒ T, with associativity and unit pastings | T T x ≤ T x | Def |
| Hμ3 | Lambek: the structure square of the initial S-algebra is invertible | f(μf) = μf | Thm (thin: `Axioms.Thin.mu1`; categorical: `Cat.mu1`) |
| Hμ4 | fold: for each algebra a there is a unique vertical v with the square in ; v = S v ; a | f(A) ≤ A ⟹ μf ≤ A | Thm (`Thin.mu2`, `Cat.mu2`) |
| Hμ5 | induction: a sub-algebra square into the initial algebra with mono vertical side is invertible | no proper pre-fixed point below μf | Thm (`Thin.mu3`, `Cat.mu3`) |
| Hμ6 | least bound: the comparison square from the initial algebra into every pre-fixed object | μf = ⋀{x ∣ f x ≤ x} | Thm (`Thin.mu4`, `mu5`) |

---

## 3. Vertical axioms: comonads (ν-layer)

A **vertical comonad** on X is D : X → X with squares ε : D ⇒ I^v_X and δ : D ⇒ D ⊙_v D, both with horizontal identity
top and bottom (**Def**). Its coalgebras have **horizontal morphisms** (C2).

| # | Square | Thin reading | Status |
|---|---|---|---|
| Vν1 | counit ε : D ⇒ I^v | D x ≤ x for the interior D of g | Def |
| Vν2 | comultiplication δ, with coassociativity and counit pastings | D x ≤ D D x | Def |
| Vν3 | Lambek: the final coalgebra's structure square is invertible | g(νg) = νg | Thm (`Thin.nu1`, `Cat.nu1`) |
| Vν4 | ana: for each coalgebra c a unique horizontal arrow with c ; B h = h ; out | x ≤ g x ⟹ x ≤ νg | Thm (`Thin.nu2`, `Cat.nu2`) |
| Vν5 | bisimulation: a relation square lifting through B is contained in the diagonal of νB | trivial | Thm (`Cat.nu3`) |
| Vν6 | greatest bound | νg = ⋁{x ∣ x ≤ g x} | Thm (`Thin.nu4`, `nu5`) |

---

## 4. Dialgebraic axioms: cells between two double functors

Let 𝔻𝔼𝕟𝕕(𝔻) be the double category of double endofunctors, horizontal and vertical transformations, and
modifications. An **(S, B)-dialgebra** on X is a horizontal arrow d_X : S X ⇸ B X together with naturality squares
for vertical arrows (and globular squares for horizontal ones) (**Def**). Dialg(S, B) is the resulting category,
with vertical morphisms.

| # | Statement | Thin reading | Status |
|---|---|---|---|
| D1 | **Left universal square:** an initial dialgebra (μ^{S,B}, d₀); for each (A, d_A) a unique vertical f with d₀ ; B f = S f ; d_A | least x with f x ≤ g x | Cond: holds when B has a left adjoint B*, with μ^{S,B} = μ(B* ∘ S) (`Dial.isLeast_dial`); categorical: `Cat.Dialg.d1` |
| D2 | **Right universal square:** a final dialgebra (ν^{S,B}, d₁) | greatest x with f x ≤ g x | Cond: S has a right adjoint (`Dial.isGreatest_dial`, `Cat.Dialg.d2`) |
| D3 | dialgebraic induction | — | Def given D1 (`Cat.Dialg.d3`) |
| D4 | dialgebraic coinduction | — | Thm (`Cat.Dialg.d4`) |
| D5 | duality: Dial(S, B) on 𝔻 ≃ Dial(Bᵒᵖ, Sᵒᵖ)ᵒᵖ on 𝔻 with both directions reversed | μ^{f,g} on L = ν^{g,f} on Lᵒᵖ | Thm (`Dial.d5`, `Cat.Dialg.d5Equiv`) |
| D6 | degeneracy | μ^{id,id} = ⊥, ν^{id,id} = ⊤ | Thm (`Cat.Dialg.d6`) |

**The failure zones** (foundations §3: δ₀ iso ⟺ f(A₀) ∈ Im g) are the statement that the left universal square is
also a *Lambek* square. They are a property of the cell, not of the pair (S, B).

---

## 5. Bounds

### 5.1 Order-theoretic bounds (kept)

Bd1–Bd9 of the foundations hold verbatim in the thin model. In particular Bd1 (μ ≤ ν) and I1 (m ≤ n) are the
comparison squares from left universal to right universal objects (C4).

### 5.2 Universal bounds: tabulators and cotabulators

For a horizontal arrow h : X ⇸ Y, a **tabulator** Tab(h) is an object with vertical arrows to X and Y and a square
from I^h_{Tab h} to h, universal among such squares. A **cotabulator** is dual (**Def**). An axiom *cell*
α : h ⇒ k with identity sides induces a vertical arrow Tab(α) : Tab(h) → Tab(k) (C3).

| Bound | Universal object | Thin reading in the equipment E(L) (§7) |
|---|---|---|
| Tb1 | Tab(T) for the closure monad T | the graph {(x, y) ∣ y ≤ T x} with its two projections |
| Tb2 | Cotab(D) for the interior comonad | the cograph (collage) of D |
| Tb3 | Tab(d₀), Cotab(d₁) | the poset of pairs related by the initial / final dialgebra relation |
| Tb4 | Tab(α) for the interaction cell α | the inclusion of graphs that α asserts |

**Representability (Lit; theorem number unverified).** As cited by the draft: Fiore–Gambino–Kock show that
Eilenberg–Moore objects exist in 𝔻 iff a parameterized presheaf Alg₋ : 𝔻_hᵒᵖ × V₁Mnd(𝔻) → Span is horizontally
representable, equivalently iff the inclusion of objects into monads has a horizontal right double adjoint.

**Non-degeneracy (Post).** The framework is non-degenerate when Alg₋ and its vertical dual Coalg₋ are representable
and Tab, Cotab exist on the axiom arrows. In E(L) all of them exist: E(L) has all tabulators (graphs of relations)
and Eilenberg–Moore objects (the posets of algebras, i.e. pre-fixed points) (**Thm**, elementary, not mechanized).

---

## 6. Interaction rules

| # | Rule | Thin reading | Status |
|---|---|---|---|
| I1′ | **Interchange** (α ⊙_h β) ⊙_v (γ ⊙_h δ) = (α ⊙_v γ) ⊙_h (β ⊙_v δ) | automatic (thin) | Post (structure of 𝔻) |
| I2′ | **Companions and conjoints**: a vertical (resp. horizontal) arrow f with f_* and f^* and their binding squares, f_* ⊣ f^* | in E(L): f_* D = ↓f(D), f^* D = f⁻¹(D), with ↓f(D) ⊆ E ⟺ D ⊆ f⁻¹(E) for down-sets E | Thm (`Axioms.Double.companion_conjoint`) |
| I3′ | **Mates**: under an adjunction l ⊣ r of companions, a square σ has a mate σ^♭ obtained by pasting units and counits; σ ↦ σ^♭ is a bijection | sup ⊣ ↓ (`yoneda_adj`); the mates of the identity squares of a_* and b^* are the comparisons ⋁a_*D ≤ a(⋁D) and ⋁b^*D ≤ ⋁{y ∣ b y ≤ ⋁D} | Thm (`mate_companion`, `mate_conjoint`; their sum is `Orbit.step_lax`) |
| I4′ | **Mixed distributive law** λ : T ⊙_h D_* ⇒ D_* ⊙_h T with the four compatibility pastings (C7) | for the bifunctor: the derived law b ∘ a ⇒ a ∘ b (`Source.DerivedLaw`) | Def |
| I5′ | **Fusion**: fold and ana fuse when the mate of the comparison is invertible (weaker than representability, §8) | strict fusion on principal down-sets (`step_principal`) and along the orbit on top-closed lattices (`orbit_tight`); lax in general | Cond |
| I6′ | **Guarded collapse**: a mixed law plus the Cut guard make the comparison invertible | Cut ∧ λ ⟹ m = n | Thm (`Source.guard`); unguarded: False (`Source.i11_false`) |

---

## 7. The models

### 7.1 Q(L): the quintet of a lattice (C1)

A complete lattice L, as a 2-category with one 2-cell per inequality, gives the quintet double category Q(L). Its
horizontal and vertical arrows are both ≤, and a square exists iff its boundary is a commuting square of
inequalities, i.e. always. Every row of §2–§6 has its thin reading here. This is the model of foundations §1.1, so the
framework must admit it.

### 7.2 E(L): the equipment of a lattice (the model of the Cut Lemma)

- **Objects:** posets (here 1 and L).
- **Horizontal arrows:** monotone maps.
- **Vertical arrows:** down-set relations (profunctors into Prop). A down-set D of L is a vertical arrow 1 → L.
- **Squares:** inclusions of relations along the maps.
- Every horizontal arrow has a companion and a conjoint, so E(L) is an equipment. It is **not** a quintet, because
  vertical arrows are relations.

In E(L) the Cut Lemma is a statement about one endo-proarrow (**Thm**, `Axioms.Double.step_eq`):

  Θ = ↓⊥ ∪ a_* ∪ b^*,  R(F) = μΘ (the initial algebra, Hμ4),  Cut(F) ⟺ R(F) = L (`Reach.cutMaps_iff_R`).

The Yoneda pair sup ⊣ ↓ binds the down-set level to the element level (`yoneda_adj`).

---

## 8. What the framework says about the Commutation Lemma

**Corollary (C5; Thm, `Axioms.Double.double_commutation_thin`).** The draft's "double-categorical commutation
theorem", read in Q(L) or E(L), is `Source.guard`: Cut(F) ∧ λ ⟹ m = n. Its other hypotheses (monads, comonads,
representability, tabulators) hold or are vacuous in the thin model. It adds no hypothesis that helps prove the guard.

**The bridge as a representability condition (Thm, `Axioms.Double.cut_iff_representable`, DCC).**

> Cut(F) ⟺ the initial Θ-algebra R(F) = μΘ is representable, i.e. R(F) = ↓r for some r.

- So the framework's own non-degeneracy demand, that the relevant presheaf be representable, is in E(L)
  *exactly* the Commutation Lemma's bridge, applied to one specific presheaf.
- In terms of sup ⊣ ↓: R(F) ⊆ ↓⋁R(F) always (the unit). Representability is invertibility of that unit at μΘ,
  i.e. ⋁R(F) ∈ R(F) (`sSup_R_mem_iff`); under ACC it is join-closure (`cutMaps_iff_joinClosed`).
- **The mate is a different, weaker condition.** The mate of Θ's identity square under sup ⊣ ↓ is lax for every F
  (I3′). Its invertibility at R(F) says that ⋁R(F) is κ⁺-closed, which under DCC gives only ⋁R(F) = ⊤
  (`eq_top_of_kstep`), not ⊤ ∈ R(F). The orbit always reaches ⊤ anyway (`rk_eventually_top`). The gap between
  "the mate is invertible" and "the unit is invertible" is the gap between the join layer and the membership layer
  (foundations §7.5, I11: "taking sups loses membership").
- These are correct and compact restatements, and **they are not leverage**: representability of μΘ is the
  order-theoretic statement already open, and no general criterion for representability of an initial algebra in an
  equipment applies without something like ACC + join-closure, which is the conjecture.

**Where a double-categorical gain could come from (Open).** E(L) has more structure than §7.2 uses: tabulators of
a_* and b^* (graphs) and a collage. A proof along these lines would need a property of the *tabulator* of Θ that
forces the mate to be invertible, and that is visible only in the double category. No such property is known.
Candidates must exclude some F (§34.3z⁵⁶ design rule): on every lattice with an infinite chain, some F has
non-representable μΘ (Theorem A with `cut_iff_representable`).

---

## 9. Mechanization

| Row | Lean | Notes |
|---|---|---|
| Hμ3–Hμ6, Vν3–Vν6, D1–D6 | `Axioms/Thin.lean`, `Axioms/Cat.lean`, `Dialgebra.lean` | inherited from the foundations; the double-categorical forms are not mechanized (Mathlib has no double categories) |
| I2′ | `Axioms.Double.companion_conjoint` | companion ⊣ conjoint on down-sets |
| I3′ | `Axioms.Double.yoneda_adj`, `mate_companion`, `mate_conjoint` | the mates are lax |
| §7.2 | `Axioms.Double.step_eq` | the Cut closure step is ↓⊥ ∪ a_* ∪ b^* |
| §5.2, §8 | `Axioms.Double.cut_iff_representable` | Cut ⟺ μΘ representable (DCC) |
| I6′, §8 | `Axioms.Double.double_commutation_thin` (= `Source.guard`) | the guard is the content |
