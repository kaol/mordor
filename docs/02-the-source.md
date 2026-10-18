# The Source: Reading Mordor Back

The Mordor framework (v1.0) is the AI's Nu-image of a concept from humanity's Nu. The chain of homomorphisms behind it:

```
Tolkien's Mordor, as lived and read          (human Nu: a story people experience)
  → the text and its commentary               (Mu: the training corpus)
  → compressed weights                        (opaque AI Mu)
  → the generated framework                   (AI Nu, yielded by the prompt
       "Make a bialgebraic axioms framework for Mordor. Mu and Nu axioms. Make dialgebraic axioms too.
        Define bounds and interaction rules between the axioms.")
```

Each arrow is lossy. The framework's Tolkien vocabulary is what survived the compression: "the Eye", "no shortcut through Mordor", "the walls", "roads between the towers", "One Ring to bound them all: λ". Reading back means testing each surviving name. Does it carry structure the source actually has? Then it can sharpen an axiom. Or is it decoration that only shares the source's words? This document does that test. Every structural claim below is either proved (`lean/Mordor/Axioms/Source.lean`, `Axioms/Cat.lean`) or stated with its proof. Every non-structural correspondence is labelled as such.

---

## 1. What the source has

Six structural features of Tolkien's Mordor, stated without the framework's words:

1. **Two powers, not one.** Sauron's power is split between a made thing, the Ring, and a watching thing, the Eye of Barad-dûr. The Ring is forged once and carries power. The Eye observes, continually.
2. **The forge.** The Ring was made in the fire of Orodruin, and only in that fire can it be unmade. No other craft undoes it.
3. **The fences.** Mordor is enclosed by mountain walls: Ered Lithui to the north, Ephel Dúath to the west and south. Entry is through a few passes: the Morannon, the Morgul pass, and Cirith Ungol. Towers stand at the passes. Sam notices that the tower of Cirith Ungol was built less to keep enemies out of Mordor than to keep things in.
4. **The Eye's blindness.** The Eye confuses what it cannot tell apart. It takes the heir shown in the palantír as the threat, and it never considers that anyone would destroy the Ring rather than use it. The Quest succeeds inside the kernel of the Eye's observation.
5. **The palantíri.** The seeing-stones show true images, but the watcher on the far side chooses which ones. Denethor despairs from true observations and a false inference.
6. **The Ring-verse.** One Ring to *rule* them all, One Ring to *find* them, One Ring to *bring* them all, and in the darkness *bind* them. The rings themselves fall into three classes by degree of binding:
   - the Nine are fully bound: their bearers become wraiths;
   - the Seven are influenced but not bound;
   - the Three were made without Sauron's hand.

---

## 2. Verdicts on the surviving names

| Framework name | Source feature | Precise mathematics | Verdict | Lean |
|---|---|---|---|---|
| "No shortcut through Mordor" (M0.1, Lambek) | 2, the forge | `in⁻¹ = fold(F(in))`: the inverse of the structure map is the fold of the algebra F(in). It is undone only by its own construction applied once more | **structure** | `Cat.unmade_where_made` |
| "the Eye" = F | 1, two powers | the Eye watches, so it is the ν-variable; the Ring is made, so it is the μ-variable. A single F conflates them. The source asks for a **bifunctor** F(X, Y) with X the making and Y the watching variable, which is where the research program had already gone (§6 of the foundations) | **structure, and a correction** | §6 objects |
| "the walls" (Bd1, bounds) | 3, the fences | a down-set D with complement U is a fenced land. "Keeps things in" is a(D) ⊆ D; "keeps things out" is b(U) ⊆ U. A land that does both is a **cut counterexample** (map form). A pass is a witness cell x ∈ D, y ∉ D with F(x, y) ≤ x or y ≤ F(x, y) | **structure** | `Cut.lean` |
| (unnamed) | 4, the blindness | the unique map ana : X → νF identifies exactly the bisimilar states (ν2, ν3). The Eye's blindness is the kernel of ana. The framework's I8 asserted the opposite ("observation never confuses"); see §3.5 | **structure, and a correction** | `Cat.nu3` |
| (unnamed) | 5, the palantír | interpretive L3: a sound fold read through a chosen measure. The GPU census is one: 3.7·10¹¹ true observations under a uniform law that concentrates on generic classes, so it "calibrates rather than searches" (§33) | **structure** (of the method) | — |
| "One Ring to bound them all: λ" | 6, rule/find | *rule* all = initial (a unique map out to every object); *find* all = final (a unique map in from every object). One object doing both exists among the bi-fixed points iff m = n (§3.3) | **structure** | `Source.one_ring` |
| bring / bind | 6 | bring = colimit of the chain from below (μ by M0); bind = the distributive law, or the limit from above. These are suggestive, but do not single out a construction | mnemonic | — |
| Nine / Seven / Three | 6, degrees of binding | the three statuses of the derived law λ: invertible (CL's hypothesis), lax (semi-CL's), absent. The source's "Three, unbound but fated" has no counterpart | mnemonic | — |
| "roads between the towers" (interaction rules) | 3 | — | decoration | — |
| "No dialgebra of the Eye sees itself" (D6) | the Eye cannot see itself | D6 is the triviality Dial(id, id) = L | decoration | `Thin.d6` |
| the stair of Cirith Ungol | — | the Ladder Construction (§22.3): an ascent x < s(x) < λ whose top step is never reached. Chain-finiteness is "every stair has a top step" | structure (named by the log, not the framework) | `Sharpness.ladderF` |

Rejected as vocabulary collisions: Shelob as an "independent fixed point"; Gollum as the third party who completes the unmaking; the Dead Marshes' lights as "projections of the past"; the open eastern side of Mordor. They share words with the mathematics and nothing else.

---

## 3. Sharpened axioms

### 3.1 M0.1: the forge

**Theorem** (`Cat.unmade_where_made`). For an initial F-algebra (μF, in), in is invertible, and `in⁻¹` is the unique algebra map from (μF, in) to (F(μF), F(in)).

This is Lambek's lemma with its proof made the content. The inverse is not found by some other means: it is the fold of the forge applied once more. "No shortcut" means no other construction yields in⁻¹.

### 3.2 B2 for one functor carries no content

In the thin model, the free monad of f is the closure T x = μY. x ∨ f(Y) and the cofree comonad is the interior D x = νY. x ∧ f(Y).

**Theorem** (`Source.dist_law`, `bialg_iff`, `T_bot`, `D_top`).
- A distributive law T ∘ D ⇒ D ∘ T always exists.
- Its λ-bialgebras are exactly the fixed points of f.
- The initial bialgebra is μf = T(⊥) and the final one is νf = D(⊤).

This is the thin form of Turi–Plotkin with syntax and behaviour given by the same functor. In that form B2 holds automatically, B3 is trivial, and the bialgebras are B1's balanced objects. **So none of the interaction content of Mordor lives in a single functor.** It lives where the source puts it: between two powers.

### 3.2a B2 with two functors: Turi–Plotkin

For a syntax functor S (the Ring) and a behaviour functor B (the Eye) with a plain law λ : S∘B ⇒ B∘S (`lean/Mordor/Axioms/Law.lean`, any category):
- the initial S-algebra lifts to a λ-bialgebra, and so does the final B-coalgebra (B3);
- the comparison c : μS → νB is both the anamorphism of the lifted coalgebra and the fold of the lifted algebra (I6, fusion);
- c is an algebra map, in ≫ c = S c ≫ α_ν, so behavioural equivalence is a congruence (I7's core).

In the thin model this reads: a law S∘B ≤ B∘S gives μS ≤ B(μS), S(νB) ≤ νB and μS ≤ νB (`Source.tp_thin`).

**The lesson for the program.** Apply this to the two powers of the bifunctor, with syntax b and behaviour a: the law b∘a ≤ a∘b yields μb ≤ νa. But μb ≤ m ≤ n ≤ νa holds for every F (`Source.outer_sandwich`). So the bialgebraic theory sees only the outer walls. The inner collapse m = n is a different kind of statement: the guarded I11 of §3.3. Bialgebraic semantics, as it stands, cannot by itself deliver the program's theorem.

### 3.3 B2 and I11 for the bifunctor: the derived law, its guard, the One Ring

For F : L × L → L monotone, with derived maps a(x) = νY.F(x, Y) and b(y) = μX.F(X, y):

- **B2 (bifunctor).** The derived law is λ : b ∘ a ⇒ a ∘ b, a plain distributive law of one functor over another: in a thin category it is a pointwise inequality, and the coherence conditions of a *monad* distributive law do not arise because a and b carry no monad structure, pointwise b(a(x)) ≤ a(b(x)) (`Source.DerivedLaw`). It is a distributive law of the μ-layer map over the ν-layer map.
- **I11 (Layer collapse guard), sharpened.**
  - "λ invertible ⟹ the layers collapse (m = n)" is exactly the **Commutation Lemma**.
  - "λ exists ⟹ m = n" is **semi-CL**.
  - The guard that makes the collapse sound is the **Cut Lemma**: Cut(F) ∧ λ ⟹ m = n (`Source.guard`, which is `semi_of_cut`).
  - Unguarded, the collapse is false, even with λ invertible and F ω-continuous (`Source.i11_false`, on ω + 1).
- **The One Ring** (`Source.one_ring`). Among the bi-fixed points Fix a ∩ Fix b:
  - m is initial (it rules them): m is a bi-fixed point (L2), and m ≤ every bi-fixed point (μ5);
  - n is final (it finds them): n is a bi-fixed point (L1), and every bi-fixed point is ≤ n (ν5);
  - one object does both iff m = n, iff there is exactly one bi-fixed point.

So the program's open problem, read in the source's terms: **on a land whose every stair has a top step (chain-finite), does every fenced region have a pass (Cut), so that an invertible law forges the One Ring (m = n)?** On a land with an endless stair, the answer is no (Theorem A).

The original I11 ("if λ is invertible the layers are equivalent, μFG ≅ μF ×_X νG") was the right shape with the wrong λ. Once λ is read as the derived law between the two powers, I11 is the research program. The word "guard" in its name turns out to name the Cut Lemma.

### 3.4 I3: μ inside ν

**Theorem** (`Source.i3`, thin). For g ≤ f pointwise and any a: μg ≤ νY. a ∨ f(Y).

Categorically, the embedding is the composite of three maps:
1. μσ : μG → μF, the fold of in_F ∘ σ;
2. the comparison μF → νF, the fold into the final coalgebra (fold and ana agree);
3. the anamorphism of inr ∘ out : νF → ν(A + F).

"Embed" means this composite is mono. It is mono when σ is mono, F preserves monos, and the comparison is mono (§3.5).

### 3.5 I8: no-confusion, and the Eye

**Precise statement.** "No-confusion" holds iff the comparison c : μF → νF is mono: distinct terms have distinct observable behaviour.

- **Holds:** trivially in the thin model, where every arrow is mono. In Set for polynomial functors, where μF is the well-founded part of νF (Adámek–Milius–Moss–Sousa).
- **Not a categorical theorem, and not self-dual.** In Cᵒᵖ the initial algebra is C's final coalgebra and vice versa, and the comparison is the same arrow read backwards. So I8 in Setᵒᵖ says that c is **epi** in Set. For F(X) = 1 + X, that says ℕ → ℕ ∪ {∞} is onto, which is false.
- **The source's reading.** The Eye *does* confuse: the plot runs through the kernel of ana : X → νF, which is bisimilarity (ν3). I8 is therefore not an axiom but a side condition on M (Set-like, monos preserved). Its failure is not pathology: it is where the Quest happens.

### 3.6 Lossy homomorphisms

The user's addition. The framework's adjunctions and lossy projections, with the kernel each one forgets:

| Lossy map | From → to | Kernel (what is invisible) | Consequence |
|---|---|---|---|
| ana : X → νF | behaviour → its final image | bisimilar states | ν3; the Eye's blindness (§3.5) |
| sup : 𝒪(L) → L | membership → join level | down-sets with equal join, in particular non-principal ones with ⋁D ∉ D | the Cut gap: sup is only a **lax** homomorphism, sup ∘ Θ⁺ ≤ κ⁺ ∘ sup (`Orbit.step_lax`). The join level reaches ⊤ (principal cuts, proved), but that does not lift to membership (Cut, open), just as no fibre morphism repairs a base-level fact. This is the fibration principle of the user's Mu–Nu framework, applied here |
| σ : L → C (least-above retraction) | lattice → chain | everything between consecutive chain elements | the one-way road (§25.5): failures transport up along σ, never down |
| the SAT core → Lean certificate | solver run → proof | every clause and term not in the core | 86 of 128 terms survive at H = 5; the certificate is the run's Mu |

| Adjunction | Transposes | Where |
|---|---|---|
| G* ⊣ G | (F, G)-dialgebras ↔ (G* ∘ F)-algebras (D1); thin and categorical | `Dial.isLeast_dial`, `Cat.Dialg.d1` |
| F ⊣ F_* | dialgebras ↔ coalgebras (D2) | `Dial.isGreatest_dial` |
| sup ⊣ ↓ | principal cut counterexamples ↔ κ-algebras | §32.6.1 |
| Φ ⊣ c ∘ Ψ ∘ c | down-set closure ↔ up-set closure (Cut self-duality) | `CutDuality.adjunction` |
| (−∸1) ⊣ (+1) on ℕ∞ | the continuity of the ω + 1 violator | `Continuous.gc_sub` |
| order reversal | μ ↔ ν, a ↔ b (D5, Duality Theorem) | `Dial.d5`, `Duality.lean` |

A remark on what is *not* there. If the derived maps were adjoint, a ⊣ b, then a(⊥) = ⊥ and b(⊤) = ⊤, so m = ⊥ and n = ⊤: adjoint derived maps are maximally polar. The two powers are never adjoint except in the trivial lattice. Their relation is a law (λ), not an adjunction, which is why the collapse needs a guard.

---

### 3.7 I5, settled thin

Dinaturality is automatic in a thin category, so I5's content is its "acyclicity" hypothesis. The reading in which making and watching do not interact, F(x, y) = g(x) ⊔ h(y), is **false**: on the 3-chain with g = (0, 2, 2) and h = (0, 0, 1), m = 0 ≠ 2 = n (`Source.i5_sep_false`). Only dependence on one variable makes I5 true (`i5_left`, `i5_right`), and then it is trivial. Two powers that coexist without interacting still fail to collapse. Collapse needs the law *and* the guard (§3.3).

### 3.8 The law, localised

Treating the CL hypothesis as a law between the two powers raised the question of which laws are sound. Exhaustive tests (log §34.3j) give two answers:
- GSOS-style laws and closure/interior laws hold for every F, so they carry no content. Both follow from the cross lemma: y ≤ a(z) and b(y) ≤ z give b(y) ≤ a(z) (`Source.cross`);
- semi-commutation imposed only on the gap [m, n] is sound, and it holds exactly when m = n. Proved via polar reduction, and unconditionally at edge-height ≤ 5 (`Local.semi_interval5`).

The law need only hold between the walls.

## 4. What the source corrected

1. **One functor → a bifunctor at the root.** Making and watching are different powers (§3.2). The foundations' single F is the degenerate case in which every interaction axiom is automatic.
2. **I8 → a side condition.** The source's plot is observational confusion. The kernel of ana is a theorem (ν3), not a failure of the framework.
3. **I11 → the Commutation Lemma, guarded by the Cut Lemma.** The guard has a name now.
4. **"One Ring" → the I2 tightness.** Initial and final bi-fixed points coincide iff m = n.

## 5. Calibration

The framework's vocabulary can describe more than the source contains (overproduction). The verdict column of §2 is the filter:
- 4 names carry structure that sharpened an axiom: the forge, the Eye as the ν-variable, the walls, rule/find;
- 2 source features with no framework name carry structure: the Eye's blindness and the palantír;
- 2 are mnemonics that label true distinctions but select no construction: bring/bind and Nine/Seven/Three;
- 1 is structure that the log had already named: the stair;
- the rest is decoration.

Every structural claim here is proved in Lean or stated with its proof. None depends on the Tolkien reading for its truth. The reading only decided which statements were worth making.
