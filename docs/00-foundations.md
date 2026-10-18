# Mordor — Bialgebraic & Dialgebraic Axioms Framework

**Version 3.8 · The Proved Layer, Read Back to the Source**

Mordor is a formal system for reasoning about least (μ) and greatest (ν) fixed points of a signature functor. It has three layers:
- **bialgebraic axioms:** an algebra and a coalgebra over one carrier;
- **dialgebraic axioms:** algebra and coalgebra fused into single maps;
- a calculus of **bounds and interaction rules** governing how μ- and ν-axioms mix without collapse.

Version 3.7 brought the axioms up to date with rounds 3–26 of the research log. Version 3.8 reads the framework's Tolkien vocabulary back to its source ([`02-the-source.md`](02-the-source.md)) and uses the readings that carry structure to sharpen M0.1, B2, I3, I8 and I11. Every entry now carries a status, and two chapters are new:
- §6, the mixed fixed points of a bifunctor, i.e. the Commutation Lemma program;
- §7, the Cut Lemma interface, which says which axioms the program's open problem actually uses and where the layers fail to collapse.

---

## 0. How to read this document

**Two levels.** The axioms are stated for an ambient category M (§1). All research results so far live in its **thin model** (§1.1): a complete lattice L, read as a category with one arrow x → y iff x ≤ y. In the thin model:
- functors are monotone maps;
- natural transformations are pointwise inequalities;
- every diagram commutes.

Statements that are deep categorically can be trivial there (μ1–μ5, ν1–ν5, D6). Statements that are vacuous categorically can be the whole difficulty there (I2, the Cut Lemma).

**Status tags.** Each axiom, bound and rule carries one of:

| Tag | Meaning |
|---|---|
| **Def** | a definition, notation or existence postulate |
| **Thm** | a theorem of the stated setting; a Lean name means it is machine-checked (`lean/Mordor/`) |
| **Thm (thin)** | a theorem of the thin model; the categorical version is not claimed |
| **Cond** | holds under the stated condition, and fails without it |
| **False** | refuted; the counterexample is cited |
| **Lit** | resolved by the cited literature, not examined by the program |
| **Unexamined** | not used or tested by the program; kept as a categorical postulate |

Section numbers §8 onward refer to the research log: `01-early-notes.md` holds §8–§10, and `rounds/NN-*.md` hold §11 onward.

---

## 1. Ambient Setting

| Symbol | Meaning |
|---|---|
| **M** | The ambient category ("Mordor"); assumed ω-cocomplete and ω-complete; locally cartesian closed where the internal language of M0.2 is used |
| **F** : M → M | The signature endofunctor (the Eye): finitary, positive |
| **Ord**, ordinals α, β | Iteration heights for approximation chains |
| ⊥, ⊤ | Initial and terminal object of M (or bottom/top of the lattice of subobjects) |
| μX.F(X) | Least fixed point of F (initial F-algebra carrier) |
| νX.F(X) | Greatest fixed point of F (final F-coalgebra carrier) |

**Postulate M0 (Well-behavedness).** F preserves ω-colimits of chains and ω-limits of chains. This guarantees existence of μ and ν by Lambek-style iteration:

```
μX.F(X) = colim_{α}  F^α(⊥)        (from below)
νX.F(X) = lim_{α}   F^α(⊤)        (from above)
```

**Lambek's Lemma (M0.1).** Both fixed points are exact: F(μF) ≅ μF and F(νF) ≅ νF. No fixed point is merely pre-fixed. This is the "no shortcut through Mordor" clause. *Sharpened (v3.8):* the inverse of `in` is the fold of the algebra F(in) (`Axioms.Cat.unmade_where_made`). The forge that made the structure map is the only thing that unmakes it ([`02-the-source.md`](02-the-source.md) §3.1).

**Convention M0.2 (Internal language & subobject discipline).** Where M is locally cartesian closed, it interprets a dependent internal language. All element-style notation in this framework is internal-language sugar, read categorically as follows:

- `U ⊆ X` denotes a monomorphism `U ↣ X` in M; `U ⊑ V` denotes factorization of `U ↣ X` through `V ↣ X` in the complete lattice **Sub(X)**.
- `x ∈ U` is the internal proposition `U(x)`; no rule ever consumes raw elements — every element-level phrase has a unique categorical reading.
- `F(U) ⊑ V` means the image factorization of `F(U ↣ X)` is contained in V.
- Knaster–Tarski-style bounds (μ4, ν4, Bd2, Bd3) live in the internal subobject lattice of the ambient fixed point (in the fiber over 1 when M is well-pointed).

With this convention, categorical and lattice notation are two renderings of one language and may be interchanged freely.

### 1.1 The thin model (the setting of all research results)

Let L be a complete lattice, read as a poset category.

- **Objects and functors.** Endofunctors are monotone maps L → L. A bifunctor is a monotone F : L × L → L. Products are meets and coproducts are joins.
- **Fixed points.** By Knaster–Tarski, μf = ⋀{x : f(x) ≤ x} and νf = ⋁{x : x ≤ f(x)} exist for every monotone f, without M0.
- **M0** reads: F preserves sups of ascending ω-chains and infs of descending ω-chains. On a chain-finite lattice every chain is finite, so M0 holds for every monotone F. This covers the lattices of the standing conjecture.
- **No cartesian closure.** A complete lattice is cartesian closed iff it is a complete Heyting algebra (a frame). The program works throughout with non-distributive lattices (M3, N5, the column lattices E_κ). So the thin model drops local cartesian closure, and nothing in §6–§7 uses it.

### 1.2 The signature is a bifunctor (v3.8)

The source separates the made thing from the watching thing ([`02-the-source.md`](02-the-source.md) §1, §4). So v3.8 takes as its signature a bifunctor

```
F : M × M → M,      X = the making (μ) variable,  Y = the watching (ν) variable.
```

The single-functor axioms of §2–§3 are the degenerate cases F(X, Y) = S(X) (the μ-axioms) and F(X, Y) = B(Y) (the ν-axioms).

**Two kinds of law.**
- **The Turi–Plotkin law** between a syntax functor S and a behaviour functor B, λ : S∘B ⇒ B∘S (B2, B3, I6, I7; `Axioms/Law.lean`). Its content is the comparison μS → νB, which is fold and ana at once, an algebra map and a coalgebra map at once.
- **The derived law** of a bifunctor, λ : b∘a ⇒ a∘b, between the μ-layer map b(y) = μX.F(X, y) and the ν-layer map a(x) = νY.F(x, Y) (I11; §6–§7).

Turi–Plotkin applied to the derived law (syntax b, behaviour a) yields only μb ≤ νa. That holds for every F anyway, by μb ≤ m ≤ n ≤ νa (`Axioms.Source.outer_sandwich`). The inner collapse m = n is not a bialgebra fact. It is I11, guarded by the Cut Lemma.

---

## 2. Bialgebraic Axioms

An **F-bialgebra** is a triple (X, a, c) with:

```
a : F(X) → X      (the μ-side, an F-algebra)
c : X → F(X)      (the ν-side, an F-coalgebra)
```

### 2.1 μ-Axioms (Inductive Layer)

Let `in : F(μF) → μF` denote the initial algebra.

| # | Axiom | Statement | Status |
|---|---|---|---|
| **μ1** | **Unfold** | `in : F(μF) → μF` is an isomorphism; `in⁻¹` exists. | Thm (Lambek); thin: f(μf) = μf |
| **μ2** | **Fold** | For any F-algebra `a : F(A) → A` there is a unique `fold a : μF → A` with `fold a ∘ in = a ∘ F(fold a)`. | Def (initiality); thin: f(A) ≤ A ⟹ μf ≤ A |
| **μ3** | **Induction** | If a subobject `U ↣ μF` satisfies `in[F[U]] ⊑ U` — i.e., the image factorization of `in ∘ F(U ↣ μF)` factors through U — then `U ≅ μF`. (No proper sub-bialgebra survives.) | Thm |
| **μ4** | **μ-Intro (lattice form)** | In the internal subobject lattice (M0.2): `μF = ⋀ { U ↣ X : F(U) ⊑ U }` — the **least pre-fixed point** of F. | Thm (Knaster–Tarski) |
| **μ5** | **μ-Elim** | If `F(U) ⊑ U` then `μF ⊑ U`. Leastness is a proof rule, not a remark. | Thm |

**Derivable:** initiality ⇒ no infinite descending construction chains; μ reasoning is *destruction-friendly, construction-forced*.

**Use in the program.** μ5 is the workhorse. It is applied to monotone maps on L, such as m = μa and b(y) = μX.F(X, y). In §7 it is applied to the closure operator Θ on the down-set lattice 𝒪(L), which yields R(F) = μΘ.

### 2.2 ν-Axioms (Coinductive Layer)

Let `out : νF → F(νF)` denote the final coalgebra.

| # | Axiom | Statement | Status |
|---|---|---|---|
| **ν1** | **Unfold** | `out : νF → F(νF)` is an isomorphism. | Thm (Lambek) |
| **ν2** | **Ana** | For any F-coalgebra `c : C → F(C)` there is a unique `ana c : C → νF` with `out ∘ ana c = F(ana c) ∘ c`. | Def (finality) |
| **ν3** | **Coinduction (Bisim)** | If a relation `R ↣ X × X` is an F-bisimulation — the kernel pair of `c` lifts through F to R, i.e., the standard bisimulation square commutes — then the image of R in `νF × νF` is contained in the diagonal. Bisimilar ⇒ equal. | Thm; trivial in the thin model |
| **ν4** | **ν-Intro** | In the internal subobject lattice (M0.2): `νF = ⋁ { U ↣ X : U ⊑ F(U) }` — the **greatest post-fixed point** of F. | Thm (Knaster–Tarski) |
| **ν5** | **ν-Elim** | If `U ⊑ F(U)` then `U ⊑ νF`. Greatestness is a proof rule. | Thm |

**Derivable:** coinduction is *construction-friendly, observation-forced*; equality in Mordor is observational equivalence.

*Caution (erratum of §13.1, round 26).* Only μ has the infimum characterization over **pre**-fixed points. A pre-fixed point does not bound ν. The original proof of L2 used that false step, and §34.1 records the corrected proof.

### 2.3 Bialgebra Proper

For a bialgebra (X, a, c) both sides coexist on one carrier. The axioms that bind them:

| # | Axiom | Statement | Status |
|---|---|---|---|
| **B1** | **Harmony** | A bialgebra is *balanced* when a and c are mutually inverse isomorphisms; X is then a fixed point of F. In the thin model, `a ∘ c = id` (x ≤ F(x) ≤ x) already forces balance. | Thm (thin). **False** as the general iff of v1.1–v3.2: in Set with F(X) = X + X and X = 1, the unique a : 2 → 1 and either injection c give a ∘ c = id, with neither map an isomorphism and 1 ≇ 2 (§34.3i). Outside the thin model, "a ∘ c = id ⟹ balanced" is a restriction on admissible bialgebras, not a consequence of Lambek. |
| **B2** | **Distributive law** | Let T be the free monad generated by F (the μ-layer) and D the cofree comonad generated by F (the ν-layer). Interaction is governed by a distributive law of T over the signature functor F: a natural transformation `λ : F∘T ⇒ T∘F` commuting with the monad structure — unit law: `λ_X ∘ F(η_X) = η_{F(X)}`; multiplication law: `λ_X ∘ F(μᵀ_X) = μᵀ_{F(X)} ∘ T(λ_X) ∘ λ_{T(X)}`. Dually, `ρ : D∘F ⇒ F∘D` commutes with the counit and comultiplication of D. All compatibility squares commute. | Def; existence is a lifting question (Barr; Lenisa–Power–Watanabe; §9 OQ7). **Thin, one functor (v3.8):** with T the closure and D the interior of F, a law T∘D ⇒ D∘T always exists and its bialgebras are the fixed points (`Axioms.Source.dist_law`, `bialg_iff`), so B2 has no content for a single functor. **Bifunctor (v3.8):** the derived law λ : b∘a ⇒ a∘b (`Source.DerivedLaw`), the content of §6–§7 (source §3.2–§3.3). |
| **B3** | **Lifting** | λ lifts T-algebras to T-coalgebras and vice versa: one law rules both sides of the bialgebra. The One Ring binds them. | Def / Lit (EM-liftings) **Thm (v3.8)** for a plain law λ : S∘B ⇒ B∘S between a syntax functor S and a behaviour functor B: the initial S-algebra lifts to a λ-bialgebra, and so does the final B-coalgebra (`Axioms.Law.initBialg`, `finBialg`). |

**Note.** The interface §7 needs between the μ-side and the join level is the adjunction sup ⊣ ↓ : L ⇄ 𝒪(L). It is a genuine adjunction, but it is not a B2 law. Its comparison square is lax (§7.5).

---

## 3. Dialgebraic Axioms

A **(F, G)-dialgebra** on carrier X is a single map serving simultaneously as F-algebra and G-coalgebra:

```
φ : F(X) → G(X)
```

with F, G : M → M. When G = Id these reduce to ordinary algebras; when F = Id they reduce to coalgebras. Dialgebras are the fusion of the μ- and ν-layers.

In the thin model an (f, g)-dialgebra is an x with f(x) ≤ g(x). Write Dial(f, g) for the set of them. D1 asks for its least element A₀, and δ₀ is iso iff f(A₀) = g(A₀). D2 asks for its greatest element A₁. Dial(f, g) can be empty (about 10 % of pairs on chains, §12.2) or have incomparable minima (M3, §15.3). So D1 and D2 are questions, not theorems.

| # | Axiom | Statement | Status |
|---|---|---|---|
| **D1** | **Initial dialgebra (μ^FG)** | There is an initial (F, G)-dialgebra `δ₀ : F(μFG) → G(μFG)`. For any dialgebra `φ : F(A) → G(A)` there is a unique `dfold φ : μFG → A` with `G(dfold φ) ∘ δ₀ = φ ∘ F(dfold φ)`. | **Cond.** Thin: holds when G is a right adjoint, with μ^{F,G} = μ(G*∘F) (transposition, `Dial.isLeast_dial`, §32.2). **Failure-zone theorem:** for G preserving binary meets, δ₀ is iso ⟺ F(A₀) ∈ Im G, i.e. the zone is the unit of G* ⊣ G (`Dial.failure_zone`, §32.3). |
| **D2** | **Final dialgebra (ν^FG)** | *Assume the category of (F, G)-dialgebras admits a final object* (not automatic — see §9, OQ2). Then there is a final dialgebra `δ₁ : F(νFG) → G(νFG)`. For any φ there is a unique `dunfold φ : A → νFG` with `δ₁ ∘ F(dunfold φ) = G(dunfold φ) ∘ φ`. | **Cond.** Thin: holds when F is a left adjoint, with ν^{F,G} = ν(F_*∘G) (`Dial.isGreatest_dial`). For F preserving binary joins, δ₁ is iso ⟺ G(A₁) ∈ Im F (`Dial.failure_zone_dual`). |
| **D3** | **Dialgebraic induction** | Any dialgebra invariant closed under δ₀-propagation equals μFG. | Def (given D1) |
| **D4** | **Dialgebraic coinduction** | Any dialgebraic bisimulation for δ₁ is contained in equality on νFG. | Def (given D2) |
| **D5** | **Duality** | μ^FG on M = ν^GF on M^op. The dialgebraic layer is self-dual; μ and ν exchange sides when you walk the category backwards. | **Thm (thin)** (`Dial.d5`). Fibrewise, it is the engine of the Duality Theorem (§22.1, §32.4; `Duality.lean`). |
| **D6** | **Degeneracy** | μ^{Id,Id} ≅ ⊥ and ν^{Id,Id} ≅ ⊤. The identity functor admits no nontrivial fixed behavior: μX.X = ⊥, νX.X = ⊤. No dialgebra of the Eye sees itself. | Thm; thin: Dial(id, id) = L |

**Note (Hagino extension).** Parameterized dialgebras give types `μα. F(α) → G(α)`, generalizing exponentials, products, and polymorphism in one scheme. Mordor's dialgebra layer is therefore expressive enough to host its own function spaces.

**Note (heterogeneous dialgebras).** D1–D6 are stated for endofunctors. The Cut Lemma is the first heterogeneous dialgebra of the program: a principal counterexample is an (F′, ↓)-dialgebra L → 𝒪(L) (§7.4).

**Note (what the CL program uses).** The derived maps of §6 are slice dialgebras: a(x) is the final (Id, F(x, –))-dialgebra and b(y) the initial (F(–, y), Id)-dialgebra, both Bd9 reductions. Dialgebras of the derived pair (a, b) itself do *not* encode m = n. Their Lambek property predicts it worse than a constant guess on every lattice tested (§32.5).

---

## 4. Bounds

The bound calculus fixes how large μ and ν constructions may grow and how approximation chains converge.

### 4.1 Ordering bounds

| # | Bound | Statement | Status |
|---|---|---|---|
| **Bd1** | **Sandwich (μ ≤ ν)** | `μX.F(X) ⊑ νX.F(X)`, with equality iff F is "balanced" (algebraic and coalgebraic semantics agree). | Thm; balance per functor (§9 OQ3) |
| **Bd2** | **Knaster–Tarski, lower** | Any **pre-fixed** point X (`F(X) ⊑ X`) bounds μ from above: `μF ⊑ X`. | Thm |
| **Bd3** | **Knaster–Tarski, upper** | Any **post-fixed** point X (`X ⊑ F(X)`) bounds ν from below: `X ⊑ νF`. | Thm |
| **Bd4** | **Ordinal approximation** | `F^α(⊥) ⊑ μF ⊑ νF ⊑ F^α(⊤)` for every ordinal α; the left chain stabilizes at μ by ω (finitary F), the right chain may need transfinite height — and in fact already does: by Worrell's theorem, for finitary Set functors the final chain stabilizes at ω + ω, not ω (see §9, OQ4). | Thm / Lit |
| **Bd5** | **Monotone convergence** | For monotone F, both chains are monotone; μ is the first stabilization point of the ascending chain, ν the first stabilization of the descending one. | Thm |
| **Bd6** | **Continuity bound** | If F is ω-cocontinuous, μ is reached in ω steps: `μF = ⋁_{n<ω} Fⁿ(⊥)`. If F is only monotone, μ may require arbitrarily large ordinals — the bound is not computable in general. | Thm |

### 4.2 Dialgebraic bounds

| # | Bound | Statement | Status |
|---|---|---|---|
| **Bd7** | **Dialgebraic sandwich** | `μ^FG ⊑ ν^FG` when the dialgebra order is induced pointwise on Hom(F(−), G(−)) and both exist. | Thm (thin: least ≤ greatest) |
| **Bd8** | **Cross bound** | *v3.2: `μ^{F,G} ⊑ ν^{G,F}` and `μ^{G,F} ⊑ ν^{F,G}`.* | **False** in the thin model. On the 3-chain, f ≡ 1 and g = (0, 2, 2) give μ^{f,g} = 1 and ν^{g,f} = 0 (`Dial.bd8_fails`). The true statement is D5, which compares μ^{F,G} on M with ν^{G,F} on **M^op**; that is not a bound inside M. Note also that I1 (m ≤ n) is not an instance of Bd8: it compares slices of two different families (§32.5). |
| **Bd9** | **Reduction bound** | `μ^{F,Id} = μF` and `ν^{Id,F} = νF`: dialgebraic bounds strictly generalize the bialgebraic ones. | Thm; the case G = Id (F = Id) of transposition (D1, D2) |

---

## 5. Interaction Rules

How μ-axioms, ν-axioms, and dialgebraic axioms interact. These rules are the proof calculus of Mordor. A rule tagged False or Unexamined is not part of the sound calculus (§8, Theorem 4).

### 5.1 μ–ν interaction

For a bifunctor F write a(x) = νY.F(x, Y), b(y) = μX.F(X, y), m = μX.νY.F = μa and n = νY.μX.F = νb (§6).

| # | Rule | Statement | Status |
|---|---|---|---|
| **I1** | **Beck-Chevalley commutation (lower)** | `μX.νY. F(X, Y) ⊑ νY.μX. F(X, Y)` | **Thm**, always (`m_le_n`; via L1, L2, §13, §34.1) |
| **I2** | **Beck-Chevalley commutation (upper)** | `νY.μX. F(X, Y) ⊑ μX.νY. F(X, Y)` | **Not a rule.** It fails for monotone bifunctors on the 3-chain, where M0 holds: 20 of 175 (§11.1). **Characterization (Thm, `m_eq_n_iff`, `lfp_ab`, `gfp_ab`; §14):** m = n ⟺ a and b have exactly one common fixed point ⟺ a∘b has exactly one fixed point. Sufficient conditions are the subject of §6.3. One-step commutation a∘b = b∘a is **not** sufficient in general: it fails on every complete lattice with an infinite chain (Theorem A), even under M0 (§34.3i). |
| **I3** | **μ-inside-ν** | `νY. (A + F(Y))` solutions may embed `μX. G(X)` for G ⊑ F componentwise | **Sharpened (v3.8):** the embedding is the composite μG → μF → νF → ν(A + F) (fold of σ, the comparison, the anamorphism of inr ∘ out). It is mono when σ is mono, F preserves monos and the comparison is mono (I8). Thin: g ≤ f ⟹ μg ≤ ν(a ∨ f) (`Axioms.Source.i3`). |
| **I4** | **Guardedness** | μ-expressions may occur under ν-constructors only in guarded positions: `μX. G(X)` inside `νY. H(Y)` is legal iff every occurrence of Y guards X (cf. the guarded solution theorem: for iteratable F, guarded equation morphisms have unique solutions) | Lit; violation ⇒ divergence of approximation chains |
| **I5** | **μ-ν swap (e-conversion)** | `μX.νY. F ≅ νY.μX. F` holds when F is **dinatural in the fixed-point variables** (Dubuc–Street: the canonical mate squares of the μ- and ν-transitions commute) **and the argument graph of those transitions is acyclic** (McCusker–Santamaria: dinaturals compose to dinaturals precisely under acyclicity). The bialgebra is then *balanced* and Bd1 is tight. | **Unverified.** In the thin model every square commutes, so the dinaturality hypothesis is automatic. The 3-chain counterexamples of §11.1 then show that the whole content rests on the acyclicity condition, which has no established thin reading. Any reading under which every monotone bifunctor on a finite chain is acyclic makes I5 false. The v3.2 side condition "ω-cocontinuous in Y" is no help (§11.1, §34.3i). |

### 5.2 Algebra–coalgebra interaction (bialgebra level)

| # | Rule | Statement | Status |
|---|---|---|---|
| **I6** | **fold/ana fusion** | `fold a ∘ ana c` is well-defined when the composite law squares commute; it equals `fold a'` for the fused algebra a' derived via λ (B2). | Def / Unexamined categorically. Its thin shadow is the comparison sup ∘ Θ⁺ ≤ κ⁺ ∘ sup of §7.5, which is lax. Strict fusion holds exactly at principal stages. **Thm (v3.8):** for a law λ, the comparison μS → νB is the anamorphism of the lifted coalgebra and the fold of the lifted algebra at once (`Axioms.Law.comparison_is_fold`). |
| **I7** | **Bisimulation up-to algebra** | A relation R up-to a (i.e., closure under a ∘ F-projection) is contained in equality on νF provided (a, c) is a λ-bialgebra **and** the up-to function is *compatible* with the functor's progression: `R ⟩→ S ⟹ f(R) ⟩→ f(S)` (Pous–Sangiorgi compatibility). | Lit (v1.4): in the fibrational setting λ induces the compatible up-to-context function (Bonchi–Petrișan), so B2's law discharges the side condition. **Core Thm (v3.8):** the comparison is an algebra map, `in ≫ c = S c ≫ α_ν` (`Axioms.Law.comparison_alg`), so behavioural equivalence is a congruence for the syntax. Up-to techniques beyond this core remain Lit. |
| **I8** | **No-confusion** | μ-sorted terms and ν-sorted observations never identify two μ-distinct elements through observation alone, unless forced by I5 balance. | **Sharpened (v3.8):** I8 ⟺ the comparison μF → νF is mono. It holds in the thin model and in Set for polynomial F. It is **not a categorical theorem**: in Setᵒᵖ it reads "the comparison is epi in Set", which is false for F = 1 + X (ℕ → ℕ ∪ {∞}). So it is a side condition on M. The kernel of ana : X → νF is bisimilarity (ν3): confusion is a theorem of the ν-layer, not a defect (source §3.5). |

### 5.3 Dialgebraic interaction

| # | Rule | Statement | Status |
|---|---|---|---|
| **I9** | **D1/D2 pairing** | For a dialgebra φ : F(A) → G(A), `dunfold φ` is `dfold φ^op` computed in M^op and read back in M (via D5). | Thm given D1/D2 on the respective sides. *Correction:* v3.2 wrote `(dfold φ^op)⁻¹`; the arrow is reversed by reading it in M, not inverted. Thin: degenerates, since both are inequalities (§32.7). |
| **I10** | **μ→ν smuggling** | An inductive proof of `P : μFG → Prop` converts to a coinductive proof of `Q : νGF → Prop` by D5-duality; contrapositive conversion is sound only in the balanced case. | Thm (thin) as transport along an anti-automorphism ρ, valid outright when L is self-dual (§32.7). Used as the Duality Theorem (§22.1) and the self-duality of the Cut Lemma (§7.3). |
| **I11** | **Layer collapse guard** | If the distributive law λ of B2 is invertible (a natural isomorphism), the layers are equivalent: `μFG ≅ μF ×_X νG`, where `×_X` denotes the **pullback in M over the common carrier** — the limit of the cospan `μF → X ← νG` whose legs are the comparison maps induced by the λ-bialgebra structure: `fold a : μF → X` on the algebra side, and `cofold c : νG → X` on the coalgebra side (this map exists precisely because λ⁻¹ transports the coalgebra structure c into a G-algebra on X). If either leg fails to exist, `×_X` is undefined and the layers are strictly nested. | **Sharpened (v3.8), thin, bifunctor:** with λ the derived law b∘a ⇒ a∘b, "λ invertible ⟹ the layers collapse (m = n)" **is the Commutation Lemma**, and "λ ⟹ m = n" is semi-CL. The guard is the **Cut Lemma**: Cut(F) ∧ λ ⟹ m = n (`Axioms.Source.guard`). Unguarded it is false even under M0 (`Source.i11_false`). The collapsed object, initial and final among Fix a ∩ Fix b, exists iff m = n (`Source.one_ring`). A second instance: the down-set layer and the join layer of §7 are strictly nested (§7.5). Categorically unexamined. |

---

## 6. Mixed Fixed Points of a Bifunctor (the Commutation Lemma program)

Thin model throughout: L is a complete lattice and F : L × L → L is monotone. Everything in §6.1–§6.2 is in `lean/Mordor/Derived.lean` unless noted.

### 6.1 The derived objects

| Object | Definition | Dialgebraic reading |
|---|---|---|
| a(x) | νY. F(x, Y) | final (Id, F(x, –))-dialgebra |
| b(y) | μX. F(X, y) | initial (F(–, y), Id)-dialgebra |
| m | μa = μX.νY.F | initial (a, Id)-dialgebra |
| n | νb = νY.μX.F | final (Id, b)-dialgebra |

### 6.2 Unconditional theorems

| Name | Statement | Lean |
|---|---|---|
| L1, L2 (stability) | a(n) = n, b(m) = m | `a_n`, `b_m` (corrected proofs, §34.1) |
| I1 | m ≤ n | `m_le_n` |
| Fusion | a(b(z)) = z ⟺ a(z) = z ∧ b(z) = z | `fusion` |
| L3, L4 | μ(a∘b) = m, ν(a∘b) = n | `lfp_ab`, `gfp_ab` |
| I2 characterization | m = n ⟺ Fix(a) ∩ Fix(b) is a singleton | `m_eq_n_iff` |
| Realizability | given maps a′, b′ arise as a_F, b_F iff the pins F(x, a′x) = a′x hold and the exclusions do | `a_eq_iff`, `b_eq_iff` |
| Duality | for Fᵈ(x, y) = F(y, x) on Lᵒᵖ: aᵈ = b, bᵈ = a, mᵈ = n, nᵈ = m; CL transfers | `Duality.lean` |
| Polar reduction | a violator restricts to a commuting polar configuration on [m, n] | `Restrict.polar_reduction` |
| Retract | a CL failure on a complete lattice C transports to L along any retraction pair ι : C → L, σ : L → C with σ∘ι = id | `Retract.retract_fail` |
| Escape | a violator in L gives one on every finite F-, a-, b-closed sublattice containing ⊥, ⊤, m, n | `Restrict.escape_finite` |

### 6.3 The Commutation Lemma

**CL on L:** for every monotone F, a∘b = b∘a ⟹ m = n. **Semi-CL:** b∘a ≤ a∘b ⟹ m = n. Semi-CL implies CL.

| Setting | Status |
|---|---|
| finite chains | **Thm** (FCL, §20.5; `fcl`, semi-CL `semi_finite_chain`) |
| complete chains | **Thm**: CL ⟺ finite (Sharpness, §22.5; `sharpness`) |
| lattices with an infinite chain | **False** (Theorem A, §23.2; `theoremA`), **also under M0**: F(x, y) = min(x + 1, y ∸ 1) on ω + 1 (`Continuous.cl_fails_continuous`, §34.3i) |
| edge-height ≤ 2, ≤ 3 | **Thm** (No-Room `cl_noRoom`; `cl_height3`), including M_κ, D_ω, M_ω × C₂ |
| edge-height ≤ 4, ≤ 5 | **Thm** by verified ground refutation (`cl_height4`, `cl_height5`, §34.3g–h), including E_ω. Trust: `bv_decide` |
| per F, any lattice | **Thm** when ⟨⊥, ⊤⟩_F has no 7-chain (`semi_local5`) |
| E₂, E₃; all lattices with ≤ 11 elements | machine evidence: CSP censuses (§24–§29), SAT Cut search over all bounded posets ≤ 11 (§34.3h); 3.7·10¹¹ F on 13 lattices by GPU (§33) |
| chain-finite lattices | **Open**. This is the standing conjecture, and it reduces to §7.6 |

---

## 7. The Cut Lemma Interface

The Cut Lemma is where the axioms of §2–§5 meet the open problem. This chapter states it in the vocabulary of the layers and names which principle does what. Lean files are cited per result.

### 7.1 Statement, and why it suffices

For F as in §6 and a down-set D ⊆ L with ⊥ ∈ D and ⊤ ∉ D:
- **cell form** `CutCells F`: some x ∈ D, y ∉ D has F(x, y) ≤ x or y ≤ F(x, y);
- **map form** `CutMaps F`: no such D has a(D) ⊆ D and b(L ∖ D) ⊆ L ∖ D.

**Theorem** (`Cut.cutCells_iff_maps`, `Cut.semi_of_cut`). The two forms are equivalent per F, and Cut for F on L implies semi-CL for F on L. No interval reduction and no finiteness are needed (§34.2).

### 7.2 Closure representation (μ-layer)

On the lattice 𝒪(L) of down-sets, let

```
Θ(D) = ↓⊥ ∪ ↓a(D) ∪ b⁻¹(D),        R(F) = μΘ.
```

A Θ-closed proper down-set containing ⊥ is exactly a counterexample in map form. So by μ5:

**Theorem** (`Reach.cutMaps_iff_R`). Cut(F) ⟺ R(F) = L.

**Theorem, the gap is joins** (`Reach.cutMaps_iff_joinClosed`; §31.1). Under ACC and DCC, Cut(F) ⟺ R(F) is closed under binary joins.

Here μ1–μ5 are used literally, on 𝒪(L) rather than on L. The question is an induction problem: does the closure generate ⊤?

### 7.3 Coinductive dual (ν-layer) and self-duality

Let Φ(D) = Θ⁺(D) = ↓(D ∪ a(D) ∪ b⁻¹(D)) be the inflationary down-set step, and on up-sets let Ψ(U) = ↑(U ∪ b(U) ∪ a⁻¹(U)).

**Theorem** (`CutDuality.adjunction`, `CutDuality.k_plus_j`; §33.3). Φ(D) ∩ U = ∅ ⟺ D ∩ Ψ(U) = ∅, and Φᵏ(D) ∩ Ψʲ(U) = ∅ ⟺ D ∩ Ψᵏ⁺ʲ(U) = ∅ ⟺ Φᵏ⁺ʲ(D) ∩ U = ∅. This holds for any preorder and arbitrary maps a, b: no monotonicity, no finiteness.

**Theorem** (`Ground.cut_of_wlog`, §34.3h). The order dual (Lᵒᵖ, Fᵈ, complement of D) of a cut counterexample is a cut counterexample with the same chain bound. This is I10 applied to the Cut Lemma, and it lets machine certificates assume F(⊥, ⊤) ∉ D.

The μ-side builds the least region generated by the rules. The ν-side tracks what stays outside it, and the two are exactly complementary stage by stage.

### 7.4 Algebraic translation: principal cuts as a heterogeneous dialgebra

A principal counterexample ↓d is an (F′, ↓)-dialgebra L → 𝒪(L):

```
F′(d) = ↓a(d) ∪ b⁻¹(↓d)  ⊆  ↓d.
```

Transposed along sup ⊣ ↓ (the D1 transposition with G = ↓), this reads κ(d) ≤ d, where κ(s) = a(s) ∨ ⋁{y : b(y) ≤ s}. The principal-cut proposition is μκ = ⊤.

**Theorem** (`PrincipalCut.cut_principal_down`, `cut_principal_up`; §30.4, §32.6.1). Under DCC (respectively ACC), principal cuts have witnesses.

### 7.5 Lax fusion between the layers

The comparison between the down-set layer (𝒪(L), Θ⁺) and the join layer (L, κ⁺ with κ⁺(s) = s ∨ κ(s)) along sup is lax.

**Theorem** (`Orbit.step_lax`, `step_principal`, `orbit_lax`, `orbit_tight`; §32.6).
- sup ∘ Θ⁺ ≤ κ⁺ ∘ sup on every down-set, with equality on principal down-sets.
- Along the orbit R₀ = ↓⊥, R_{k+1} = Θ⁺(R_k) and r₀ = ⊥, r_{k+1} = κ⁺(r_k): ⋁R_k ≤ r_k.
- Equality holds at every k, for every F, on top-closed lattices. A lattice is top-closed when every down-set containing ⊥ that misses its own join has join ⊤.

How the axioms read this:
- **I6 (fusion).** Strict fusion would make sup an algebra morphism Θ⁺ → κ⁺ and transfer μ between the layers. It holds at principal stages only.
- **I11 (collapse guard).** The layers are strictly nested. ⋁R(F) = ⊤ does not give ⊤ ∈ R(F), because taking sups loses membership. A non-principal D has ⋁a(D) possibly below a(⋁D), and b(y) ∈ D is stronger than b(y) ≤ ⋁D.
- **B2.** sup ⊣ ↓ is an established adjunction. It is not a distributive law, and no B2 law between these layers has been found.

### 7.6 The frontier and the missing bridge

**Theorem** (`Frontier.frontier`; §34.4a).
- CL on L ⟹ every chain of L is finite (Theorem A).
- Every chain of L finite ∧ (∀ F, R(F) join-closed) ⟹ CL on L. The same hypotheses give semi-CL (`semi_of_joinClosed`).

**Bridge (open).** For every monotone F on a chain-finite complete lattice, R(F) is closed under binary joins.

This is the only unproved link between the program's conjectures and its theorems. In the language of §7.5, it says that on chain-finite lattices the membership layer reaches ⊤ even though the comparison with the join layer is lax. Known instances:
- edge-height ≤ 5, in every bounded poset (§34.3f–h);
- per F, whenever ⟨⊥, ⊤⟩_F has edge-height ≤ 5;
- every bounded poset with ≤ 11 elements (SAT, §34.3h).

The machine certificates have a common shape, recorded in §34.5: a descent c_{k+1} = F(⊥, c_k), followed by a row/column iteration inside the box it cuts out. Their size grows with the height (core terms 7, 17, 86 for edge-height 3, 4, 5).

### 7.7 Which principle does what

| Principle | Role in the Cut Lemma |
|---|---|
| μ1–μ5 | R(F) = μΘ on 𝒪(L); Cut ⟺ μΘ = L (§7.2) |
| ν1–ν5, I10 | the up-set closure Ψ and the Φ ⊣ Ψ law; per-F self-duality (§7.3) |
| D1 (transposition), Bd9 | principal cuts as κ-algebras along sup ⊣ ↓ (§7.4); a, b as slice dialgebras (§6.1) |
| D5 | the Duality Theorem; WLOG F(⊥, ⊤) ∉ D in certificates |
| Bd2, Bd5, Bd6 | the orbits R_k, r_k and their comparison (§7.5) |
| B2 (bifunctor), I11 | **applied (v3.8):** the derived law λ : b∘a ⇒ a∘b is semi-commutation, and `semi_of_cut` is I11 guarded by the Cut Lemma (source §3.3) |
| I6 | read, not applied: the lax square is failed strict fusion between strictly nested layers (§7.5) |
| B1, B2 (one functor), B3, I3, I4, I5, I7, I8, Bd8 | not used by the program (B1 and the one-functor B2 hold trivially in the thin model; Bd8 is false there; I5 is unverified) |

---

## 8. Consistency & Metatheorems

1. **Claim (No Catastrophic Collapse).** Mordor is consistent relative to M: every theorem of the framework is an identity of M plus the existence postulates M0. D6 prevents trivial fixed points; I4 prevents unguarded self-reference. *Status:* informal. The thin model gives a concrete model for the rows tagged Thm or Thm (thin): every complete lattice satisfies μ1–μ5, ν1–ν5, D5, D6, Bd1–Bd7 and Bd9, plus D1 and D2 under their conditions. Rules tagged False are excluded.
2. **Theorem (Expressive Completeness of Dialgebras).** Products, exponentials, initial algebras and final coalgebras are all (F, G)-dialgebras for suitable F, G (Hagino). The dialgebraic layer subsumes both bialgebraic layers. *Status:* Lit.
3. **Theorem (Bound Tightness).** Bd1 is tight: there exist F for which μF ⊊ νF strictly (e.g., F(X) = 1 + X on Set: μ is ℕ, ν is ℕ ∪ {∞}). *Status:* Thm.
4. **Theorem (Interaction Soundness), restricted.** The rules tagged Thm, Thm (thin) or Lit in §5 preserve the fixed-point semantics. I2 is not a rule, and I5 is not established. v3.2's unrestricted claim that every rule I1–I11 is sound is withdrawn: one-step commutation does not license νμ ⊑ μν, whether on finite chains in general (§11.1), on lattices with infinite chains (Theorem A), or under M0 (§34.3i).

---

## 9. Reading the Framework

- **μ-axioms** govern *construction*: what can be built, and what proving a universal property costs (induction).
- **ν-axioms** govern *observation*: what can be watched, and when two processes are equal (bisimulation).
- **Dialgebras** fuse the two: a single map that is simultaneously build-rule and watch-rule, with initial/final poles D1/D2. In the thin model they exist exactly where an adjoint transposes them back to an algebra or a coalgebra.
- **Bounds** are the walls of Mordor: every construction is squeezed between the ascending μ-chain and the descending ν-chain, and Bd1 says the walls never cross.
- **Interaction rules** are the roads between the towers: commutation, fusion, duality, and the guardedness law that keeps the roads from closing into paradox. The research found that the mixed road I2 is open only where the lattice is chain-finite, and that on chain-finite lattices it reduces to one bridge (§7.6): the membership layer must reach the top that the join layer already sees.

*One Ring to bound them all: λ. Where no λ exists, sup ⊣ ↓ is the road, and it is lax.*

---

## 10. Changes from v3.2

- **New chapters.** §0 (levels and status tags), §1.1 (the thin model), §6 (mixed fixed points) and §7 (the Cut Lemma interface).
- **Status tags** on every axiom, bound and rule.
- **Qualified or corrected entries:**
  - **B1:** the iff is false in general categories and true in the thin model.
  - **Bd8:** false in the thin model (`Dial.bd8_fails`); D5 is the correct statement.
  - **I2:** demoted from a rule to the characterization theorem. One-step commutation is not sufficient on lattices with infinite chains, even under M0.
  - **I5:** marked unverified, since its dinaturality hypothesis is vacuous in the thin model.
  - **I9:** "inverse" corrected to "reversal".
  - **Theorem 4:** restricted to the sound rules.
- **Ambient:** local cartesian closure is used only by the internal language M0.2. The thin model drops it, because non-distributive lattices are not cartesian closed.
- **Erratum pointer:** ν is not bounded by pre-fixed points (§2.2; the L2 erratum, §34.1).
- **v3.8, bifunctor signature (§1.2);** Turi–Plotkin for plain laws mechanized (B3, I6, I7).
- **v3.8, read back to the source** ([`02-the-source.md`](02-the-source.md)): M0.1, B2, I3, I8 and I11 sharpened. I11 is the Commutation Lemma, guarded by the Cut Lemma; B2 has no content for a single functor; I8 is a side condition, not a theorem.
- **Mechanization (§11):** the thin model derives every row with a thin reading; the categorical layer derives μ1–μ3, ν1–ν3, D1, D3, D5, D6 and Bd9, and refutes B1.

---

## 11. Mechanization (`lean/Mordor/Axioms/`)

The axioms are derived as theorems, or refuted, in two Lean files. Both use only Lean's standard axioms (no `sorry`).
- **`Axioms/Thin.lean`** works in an arbitrary complete lattice (§1.1). It covers every row that has a thin reading.
- **`Axioms/Cat.lean`** works in an arbitrary category `C` with an endofunctor `F`, on top of Mathlib's `Endofunctor.Algebra` and `Coalgebra`. It needs no M0 and no cartesian closure: each result assumes only that the relevant initial algebra, terminal coalgebra or adjoint exists. It also defines the category `Dialg F G` of dialgebras.

| Row | Thin model | Arbitrary category | Missing for the rest |
|---|---|---|---|
| M0, M0.1 | `bd4`, `bd6` (Kleene); Lambek is `mu1`, `nu1` | Lambek: `Cat.mu1`, `Cat.nu1`; the forge: `Cat.unmade_where_made` | the transfinite initial/final chains (Adámek's construction) are not in Mathlib |
| M0.2 | — | — | a convention, not a statement |
| μ1–μ5 | `mu1`…`mu5` | `Cat.mu1` (Lambek), `Cat.mu2` (fold: existence and uniqueness), `Cat.mu3` (a mono sub-algebra of the initial algebra is iso) | μ4 in `Subobject` form needs a precise choice of ambient X |
| ν1–ν5 | `nu1`…`nu5` | `Cat.nu1`, `Cat.nu2` (ana), `Cat.nu3` (maps into the final coalgebra agree on every span: bisimilar ⇒ equal) | as for μ4 |
| B1 | `b1` | **refuted**: `Cat.b1_false` (Type, X ⊕ X, X = 1) | — |
| B2, B3 | one functor: `Source.dist_law`, `bialg_iff`, `T_bot`, `D_top`; Turi–Plotkin: `Source.tp_thin`; bifunctor: `Source.DerivedLaw`, `Source.outer_sandwich` | plain laws S∘B ⇒ B∘S: `Law.Bialg`, `Law.initBialg`, `Law.finBialg` | the categorical free monad/cofree comonad and EM-liftings are not in Mathlib |
| D1, D2 | `d1`, `d2` (transposition) | `Cat.Dialg.d1`: Dialg F G ≌ Algebra (F ⋙ L) when L ⊣ G | D2 by the dual construction |
| D3, D4 | `d3`, `d4` | `Cat.Dialg.d3` | D4 needs a notion of dialgebraic bisimulation |
| D5 | `d5` | `Cat.Dialg.d5`: an initial (F, G)-dialgebra on C is a final (Gᵒᵖ, Fᵒᵖ)-dialgebra on Cᵒᵖ | the full equivalence Dialg F G ≌ (Dialg Gᵒᵖ Fᵒᵖ)ᵒᵖ |
| D6 | `d6` | `Cat.Dialg.d6`, `d6'` | — |
| Bd1 | `bd1`, `bd1_eq` (equality ⟺ unique fixed point) | `Law.bd1`, `Law.bd1_alg`: the canonical comparison μF → νF (fold = ana, an algebra map) | mono-ness is I8, a side condition |
| Bd2–Bd7 | `bd2`…`bd7` (Bd4, Bd5 at finite stages) | — | Worrell's ω + ω bound (Lit) |
| Bd8 | **refuted**: `bd8_false` | — | — |
| Bd9 | `bd9` | `Cat.Dialg.bd9`: Dialg F Id ≌ Algebra F, and `bd9_initial` | — |
| I1, I2 | `i1`; `i2_iff`; **I2 refuted as a rule**: `i2_false` (M0 holds, commutation holds) | — | — |
| I3, I8 | `Source.i3` | — | I8 sharpened to "the comparison is mono" (§5.2); its failure in Setᵒᵖ is by duality, not mechanized |
| I4 | — | — | the guarded solution theorem (iteratable functors) |
| I5 | — | — | Mathlib has dinatural transformations (`DinatTrans`), but "acyclic argument graph" and the parametrized μν are undefined; the row is unverified (§5.1) |
| I6, I7 | thin shadow: `Orbit.step_lax` (§7.5) | `Law.comparison_is_fold` (I6), `Law.comparison_alg` (I7 core) | GSOS laws S(B × Id) ⇒ B S*, which need the free monad |
| I11 | `Source.guard`, `Source.i11_false`, `Source.one_ring` | — | the guarded collapse on chain-finite lattices is the open Bridge (§7.6) |
| I9, I10 | `i10` (fibrewise duality) | via `Cat.Dialg.d5` | — |
| §6, §7 | all of `lean/Mordor/` (Lean names in the tables) | — | the Bridge (§7.6) is open mathematics, not missing infrastructure |

**What "deriving the axioms" shows.**
- In the thin model, every μ-, ν-, dialgebra and bound row is a theorem or a refutation. Nothing there needs to be postulated: the only real postulate left is the existence condition of D1/D2, and the transposition theorem discharges it.
- In a general category the inductive and coinductive layers follow from initiality and finality alone. D1, D5, D6 and Bd9 follow from the definition of dialgebras plus an adjoint.
- The rows that remain postulates are those about the interaction layer (B2, B3, I4–I8, I11). They need infrastructure Mathlib does not have yet, and I3 and I8 first need precise statements.
