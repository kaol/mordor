# Mordor — Bialgebraic & Dialgebraic Axioms Framework

An autonomous mathematics research program studying the **Commutation Lemma (CL)** for monotone bifunctions on complete lattices: when do the least and greatest fixed-point operators of a monotone bifunction F(x, y) commute — i.e., when does `lfp_x gfp_y F = gfp_y lfp_x F`?

Mordor is a formal system organized as three layers — **bialgebraic axioms** (algebra + coalgebra on one carrier), **dialgebraic axioms** (algebra and coalgebra fused), and a calculus of **bounds and interaction rules** governing how μ- and ν-axioms mix without collapse. The program combines this formal apparatus with exhaustive machine experiments: every claim in the research log is either proved, or enumerated and refuted to the last instance.

## Current status (v3.8 · The Proved Layer, Read Back to the Source)

**Proven:**
- **The Cut Lemma for every finitely generated cut under DCC** (round 26, §34.3z¹⁰⁵, Lean, standard axioms only): in a bounded lattice with DCC, every cut D = ↓g₁ ∪ … ∪ ↓g_k with ⊤ ∉ D has a witness, for every monotone F and every k (`AsyncGrid.cut_fingen_dcc`). This settles FG∞ for lattices, including the three-generator crossing case left open since §34.3z¹⁸. `cut_two` is the case k = 2.
  - **Idea.** The generator orbits uᵢ(t) = (F gᵢ)ᵗ ⊤ enter D by DCC. Their mixed-time meets W(t) = ⋀ᵢ uᵢ(tᵢ) form a finite grid, and the asynchronous meet step F(m_T, W(t)) ≤ ⋀_{i∈T} uᵢ(tᵢ + 1) holds on it. The grid becomes a finite lattice carrying a witness-free monotone map, which contradicts the finite Cut Lemma (`FinGen.cut_finite`, Sperner parity).
  - **Dual and chain-finite form** (§34.3z¹⁰⁶, `InfCapture`). The order dual handles a finitely generated complement under ACC (`cut_cofingen_acc`). So on every chain-finite lattice, Cut holds whenever D or its complement is finitely generated (`cut_chainfinite_of_finite_side`).
  - **Weaker hypothesis.** The proof needs only *one-sided grid capture*: finitely many rows in D below which every D-valued grid column lies (`cut_of_grid_capture`).
- **Finite Commutation Lemma** — CL holds on every finite chain (§20.5, round 12). Round 22 gives a short proof of a stronger statement: on a finite chain, one-sided **semi-commutation** b∘a ⊑ a∘b already forces μν = νμ (§30.3).
- **Sharpness** — a complete chain satisfies CL iff it is finite (§22.5); the Ladder Construction is also verified symbolically in z3 (§30.5).
- **Theorem A** — every complete lattice containing an infinite chain fails CL; failures can be genuinely two-dimensional (2^ω, §23).
- **L × Mₙ for end-finite L** (§34.3x–y, Lean): CL holds on L × K for every complete lattice L with finite proper principal ideals and filters and every finite K whose middle is an antichain (K = Mₙ, including C₃), e.g. Ω × C₃ and Ω × M₃. These lattices have both infinite principal ideals and infinite principal filters (`Strip.semi_of_prod_three`, `Strips.semi_of_prod_antichain`).
- **Chain-finite with finite principal ideals (or filters)** (round 26, §34.3t, Lean): on every chain-finite complete lattice whose proper principal ideals are all finite, or whose proper principal filters are all finite, the Cut Lemma, semi-CL and CL hold (`IdealFinite.semi_of_chainFinite_ideal` / `_filter`). The proof resets rows to joins of finitely many anchor rows and inducts on the regions that pin the remaining rows, in the Dershowitz–Manna order. Both classes are of unbounded height and width, e.g. Ω (chains of every length side by side), S∞′ and its rank-2 extension.
- **Edge-height ≤ 5** (round 26, §34.3f–h, Lean): the Cut Lemma holds in every bounded poset with no chain of seven elements, so semi-CL and CL hold on every such complete lattice, infinite ones included (D_ω, M_ω × C₂, **E_ω**). The height-3 case is a hand proof. Heights 4 and 5 are drat-trim-verified ground refutations, replayed in Lean by `bv_decide`. Per F, the same holds on any complete lattice whose subalgebra ⟨⊥, ⊤⟩_F has edge-height ≤ 5 (`semi_local5`).
- **CL fails under M0 too** (§34.3i, Lean): F(x, y) = min(x + 1, y ∸ 1) on ω + 1 preserves ω-sups and ω-infs, commutes, and has m ≠ n.
- **Semi-CL is local** (§34.3j, Lean): if semi-CL holds on [m, n], then m = n iff semi-commutation holds on [m, n]; unconditional at edge-height ≤ 5.
- **No-Room** — CL holds on lattices whose middle elements are all atom-and-coatom (edge-height ≤ 2, including infinite M_κ; §16.2, re-proved for all such lattices in §30.5). *Erratum:* earlier status lines said "height ≤ 3"; the argument does not reach edge-height 3 (§30.2(ii)).
- **Dialgebraic layer, thin model** (round 24): D1 holds when G is a right adjoint (μ^{F,G} = μ(G*∘F)), and dually D2. For meet-preserving G, δ₀ is iso ⟺ F(A₀) ∈ Im G. So the Lambek failure zone is the unit of G* ⊣ G, which overturns the §13.3 negative. D5 through an anti-automorphism is the Duality Theorem §22.1 (§32.2–§32.4).
- **The Cut Lemma is self-dual per F** (round 25): the down-set step Φ and the up-set step Ψ satisfy Φ ⊣ c∘Ψ∘c, so R_k ∩ U_j = ∅ ⟺ R_{k+j} ≠ L for any monotone a, b. The down-set and up-set forms of the lemma coincide for each F (§33.3).
- **Finite lattices, decided by SAT** (§30.1; DRAT-certified where marked): E₂ (Theorem B), E₃ (Theorem C), **E₄, E₅, B₄**, C₄×C₄, M₃×M₃, and **every lattice with ≤ 4 join-irreducibles** satisfy CL.

- **Machine-checked in Lean 4 + Mathlib** (round 26, `lean/`): stability, I1, fusion, I2; the Finite Commutation and Semi-Commutation Lemmas on finite chains; principal cuts; No-Room (CL at edge-height ≤ 2, M_κ for every κ); **Sharpness** (complete chains: CL ⟺ finite) and **Theorem A** (an infinite chain ⟹ CL fails), the infinite side included; Cut ⟺ R(F) = L, and on finite lattices "the gap is joins"; the Duality Theorem; the dialgebra theorems of round 24; orbit tightness; the self-duality of round 25; the axioms of the foundations themselves, derived in the thin model and, where Mathlib allows, in any category (`lean/Mordor/Axioms/`, foundations §11). Doing so found a wrong step in the log's L2 proof and a gap in its L1 proof (§34.1). Cut ⟹ semi-CL now holds per F on L itself, with no interval reduction (§34.2).

**Reductions (round 22):**
- **Cut Lemma ⟹ CL.** If every monotone F and every proper down-set D admit x ∈ D, y ∉ D with F(x, y) ≤ x or F(x, y) ≥ y, then semi-commutation (hence CL) holds; proved for principal cuts, machine-checked on 55,320 instances (§30.4). **New (§34.3m–n):** proved for every finitely generated cut of every bounded lattice, hence on **every finite lattice**, so semi-CL and CL hold on every finite lattice. **Machine-checked in Lean** (`FinGenAll.cl_finite`, standard axioms only) via a product Sperner lemma (`Sperner.odd_goods`: for Sperner labellings of the cells, the number of good maximal chains is odd).
- **Escape Lemma** and **Herbrand reduction** for lattices of bounded height (§30.5).
- **The gap is joins** (round 23): the Cut Lemma is equivalent to join-closure of the least down-set containing ⊥ closed under a and b⁻¹ (§31.1). No counterexample on any lattice with ≤ 8 elements, Π₄, B₅, C₃³; no translation-invariant sideways escape on D_ω or E_ω (§31.4–§31.6).
- **The Cut Lemma as a dialgebra L → 𝒪(L)** (round 24): transposed along sup ⊣ ↓, it is the principal-cut proposition μκ = ⊤. The comparison square is lax. Along the orbit it is tight for every F exactly on lattices where L ∖ {⊤} is a tree. That direction is proved; the converse holds on all 73 lattices of size 5–7, and the delay grows off trees (§32.6).
- **GPU census** (round 25, Radeon W6600; second batch §33.7): 2,123,185,877,470 bifunctions enumerated exactly on 17 lattices of ≤ 6 elements, plus 2.6·10⁸ heat-bath samples up to B5 and 7.3·10⁷ multicanonical ones. Zero tripwires and zero CL / semi-CL / Cut violators. Orbit lag is positive on exactly the 6 non-top-closed 6-element lattices, with exact rates for all six (the converse of orbit tightness, verified on every lattice with ≤ 6 elements). The heat-bath sampler matches the exact censuses to 0.3 % relative; on larger lattices the hard core is below 10⁻¹² under the uniform law, so it calibrates rather than searches (§33).

**Standing conjecture:** every chain-finite complete lattice satisfies CL. Formally (`lean/Mordor/Frontier.lean`), it follows from one statement: for every monotone F on a chain-finite complete lattice, R(F) is join-closed (§34.4a). Edge-height ≤ 5 is settled, in Lean (§34.3f–h), and so are all finite lattices (§34.3n, `cl_finite`). Per F, on any complete lattice, a finite (⊓, ⊔, F)-closure of {⊥, ⊤} already forces Cut and semi-CL (§34.3o). **New (§34.3z³⁸, Lean):** a finite *F*-closure suffices, with no ⊓/⊔-closure (`cutCells_of_finite_Fclosure`, via the poset theorem `RelativeCut.cut_cross`). In a counterexample the R(F)-relative cross-closure of {⊥, ⊤} is infinite (`crossClosure_infinite`), so the conjecture follows from Cut on countable chain-finite bounded posets. The ideal orbit always reaches ⊤ (`rk_eventually_top`), so Cut for F holds iff R(F) is closed under κ⁺r = r ⊔ a r ⊔ ⋁{y | b y ≤ r} (`cutMaps_iff_kstep`). R(F) = ⋃ₖ Rₖ, and ⋁R(F) is a finite join from one stage (`stable_support`). **(§34.3z³⁹)** An order automorphism commuting with F that has finitely many fixed points forces Cut for F (`cutCells_of_equivariant`). So translation-periodic counterexamples are impossible, and minimal counterexamples are rigid and term-generated. **(§34.3z⁴¹)** Sequential insertion reduces κ⁺-closure to Base + Insert (`kstep_of_base_insert`), but these are per-F equivalent to Cut (`cutMaps_iff_base_insert`). **(§34.3z⁴²)** Normal form (`cutMaps_of_bottom`): every counterexample can be normalized so that R(F) = {y | F(⊥, y) = ⊥}, a ≡ ⊥ on R and R = R₁. So the universal R-based statements, even the bottom critical pair, are equivalent to the conjecture, and delays are not invariants. **(§34.3z⁴³, Lean)** Chain-dependent CLL is *false* with DCC alone, already at k = 1 (`InfiniteCLL.not_cll_dcc`: a gap order with upward escape). FG∞ needs only max-only labellings. Max-only CLL holds for k = 1, 2 on every DCC poset (`cll_max_one`, `cll_max_two`), which gives two-generated cuts of bounded DCC posets (`cut_two_poset`). The smallest open case is max-only CLL for k = 3. Finite neighbourhoods {z : z ⊓ c ≠ ⊥, z ⊔ c ≠ ⊤} force CL with no chain condition (horizontal sums of finite lattices, e.g. chains of every length side by side), and a box-localization calculus extends this on chain-finite lattices (§34.3p, `Localize.lean`). Pinning and a reset lemma settle finitely many hubs (§34.3r–s). Iterating the reset proves Cut, hence CL, on every chain-finite lattice with finite proper principal ideals or with finite proper principal filters (§34.3t, `IdealFinite.lean`). A box criterion combines all of this with localization. The open frontier is chain-finite lattices with both infinite proper principal ideals and infinite proper principal filters that no box criterion closes. A corner lemma and a down-closed zone rule prove CL on L × K for every complete end-finite L (finite proper principal ideals and filters, e.g. Ω) and every finite lattice K (§34.3z″, `Layers.lean`), e.g. Ω × C₄; this subsumes the strip arguments of §34.3w–y. The proof needs only finitely many second coordinates among the values (`cut_prod_layers`). A case analysis on the corner F(⊥, ⊤), with collapse lemmas that bound one corner family through the anchor (⊥, ⊤) or (⊤, ⊥), proves CL on L₁ × L₂ for any two end-finite L₁, L₂, e.g. **Ω × Ω** (§34.3z‴, `Plane.lean`). Open: Ω × Ω × Ω, which funnels into the plane theorem relative to finitely many layers (Ω × Ω × C₂ first, §34.3z⁗; SAT experiments locate the missing information at generation depth 2 and state it as the finitary conjecture DC2, §34.3z⁶; DC2 is verified exhaustively by a lazy block solver on M_ω² (§34.3z⁷) and on M_ω² × C₂ (§34.3z⁸). Both have edge-height ≤ 5, so this independently confirms `cl_height5` by a height-free method, the one intended for Ω × Ω × C₂), and products with a factor that is not end-finite, and chain-finite lattices with infinite principal ideals and filters in general. (Finite posets were listed as open here until §34.3z³⁷ settled them; see below.) A skeleton theorem (§34.3z¹¹, `Skeleton.lean`) puts the rows of any counterexample on meets of the maximal elements of D and its columns on joins of the minimal elements of the complement. When both sets are finite the cut is closed (`cut_fingen`), so the open case is an infinite labelling. Conjecture FG∞ says finitely many maximal elements of D already suffice. It was first **proved in Lean for k ≤ 2** (`cut_principal_down`; `FGTwo.cut_two`, §34.3z¹⁴): every cut D = ↓p ∪ ↓q of a bounded lattice with DCC has a witness, with no condition on the complement. **It is now proved for every k** (`AsyncGrid.cut_fingen_dcc`, §34.3z¹⁰⁵; see the headline above). More generally (`FGTwo.cut_bouquet`, §34.3z¹⁶), every cut D = ⋃ᵢ ↓pᵢ whose generators, finitely or infinitely many, meet pairwise in one common element has a witness. So does every finite laminar family, one whose generators split recursively so that cross meets lie below the meet of the union (`Laminar.cut_laminar`, §34.3z¹⁷; for three generators: p₁ ⊓ p₃ = p₂ ⊓ p₃ ≤ p₁ ⊓ p₂). The crossing-meets case (three generators of which none meets both others in the common meet) was the open case for rounds §34.3z¹⁸–¹⁰⁴, and §34.3z¹⁰⁵ closes it. For finite families the problem reduces to indecomposable bags (`Crossing.cut_of_tree`, §34.3z¹⁸); every column has a generator row escaping D (`Crossing.column_lemma`); the meet-rows-only theory of a crossing triple is refuted by ground search at edge-height ≤ 6, and at edge-height 7 for strict crossing, all DRAT-verified (§34.3z¹⁹); by `Crossing.rows_to_meets` that theory loses nothing about rows, only the lattice structure among columns. A minimal common contracting column is the join of its row values (`Saturation.min_common_join`). Orbit-defined DCC is made first-order by bounding the orbits of smaller columns by those of a minimal state; the resulting tester (`experiments/fgcut/orbmin.py`, `orbfam.py`) recovers the sandwich and transport inductions with no height bound (§34.3z²¹). For the strict triple, the profile system of orbits from s and g₁(s) is a descent graph whose only unresolved node is the terminal row switch: g₁(x) ≤ p₂ only, h(x) with labels {1, 2} (§34.3z²², `MinSwitch.lean`). A minimal column contracted by the triple-meet row has the history-meet terminal property and a label fixed point K, Λ(y ⊓ g_K(y)) = K with |K| ≤ 2, whose row escapes sideways. That is the same obstruction (§34.3z²⁴, ²⁶, `HistoryFix.lean`). **New (§34.3z²⁹, §34.3z³³, Lean):** the Cut Lemma holds on every finite bounded poset in which the maximal elements of D have all meets (`CLL.cut_of_meets`), or dually the minimal elements of the complement have all joins. The proof is a mod-2 Hopf trace formula for cones (`ConeSperner.exists_full`), formalized with no topology, and needs no joins among columns. So the reduced theory has no finite model for any k, and in a counterexample the row-value closure of ⊤ is infinite. The only remaining obstruction to FG∞ is compactness. **New (§34.3z³⁶–³⁷, Lean):** the Cut Lemma holds on **every finite bounded poset** (`RelativeCut.cut_finite`, via the double-cone lemma `dcl`). The proof is a relative Lefschetz argument mod 2. Words over a face plus ⊤ or ⊥ subdivide the cone of chains of D ⊕ (C ∖ ⊤). Their label count is a chain map by a door lemma, and its trace is 1 by `ConeSperner.trace_chain`. A word labelled exactly by its face violates W1 or W2. **Later (§34.3z⁴³–⁵⁸):**
- *Max-only CLL at k = 3:* every descent-game and escape abstraction fails at non-contracting rows (§34.3z⁴⁵–⁵¹).
- *Edge-height 6:* the H = 6 ground refutation is still SAT at 797 and 1,180 terms (§34.3z⁵⁴).
- *Transport and new reductions in Lean* (`Transport.lean`):
  - duality transport, `cutCells_dual_iff`;
  - straddling finite subalgebras, `cut_of_straddle`;
  - the skeleton-grid witness, `grid_witness`;
  - maximal witness-free cuts, `exists_maximal_WFCut` (§34.3z⁵⁶–⁵⁷).
- *Outside frameworks:* `Axioms/Leibniz.lean` shows the unital Leibniz law collapses under cancellation (§34.3z⁵⁵).
- *The finite trace argument does not extend as it stands:* on the ladder ℕ ∪ {ω} the double-cone map is a locally finite chain map whose diagonal vanishes (§34.3z⁵⁸).

**Later (§34.3z⁵⁹–¹⁰⁶):**
- **The crossing case, locally (§34.3z⁶²–¹⁰⁴, Lean).** About forty rounds of local orbit analysis of three-generator cuts were all formalized in Lean. None closed the case on its own: each mechanism either reduced to the sandwich and equal-time synchronization, or stayed satisfiable in finite z3 profiles.
  - Feedback rays, transfer sets and sink cones.
  - Reciprocal orbits and aggregate fixed points.
  - Supports, cofactors, palettes and endpoint cycles.

  Two local results survive.
  - `two_outside_generator_responses` and `two_outside_anchor_responses`: at a column that every generator row contracts, at least two generator responses and at least two anchor responses lie outside D.
  - `no_equal_time_two`: three generator orbits from a common contracting column cannot all enter D at step 2.
- **The asynchronous meet grid (§34.3z¹⁰⁵).** Mixed-time meet columns supply the missing global step: the finite Cut Lemma on the grid lattice (headline above). The z3 label abstraction of the grid is UNSAT for every profile tested (k = 2, 3 with nᵢ ≤ 4; k = 4 with nᵢ ≤ 2), and each constraint family is necessary (`experiments/asyncgrid/`).
- **Infinite boundaries (§34.3z¹⁰⁶).**
  - Under a counterexample, every finite row family leaves a D-valued grid column uncaptured (`uncaptured_column_exists`). So finite-capture refinement terminates exactly when Cut holds for that F, and any termination measure must use F.
  - Finite Sperner good words exist at every stage (odd count) but need not be compatible under enlargement (`experiments/infcapture/`).

**Later (§34.3z¹⁰⁷–¹²³): the refinement and separator programs.**
- **Grid refinement does not terminate by local means (§34.3z¹⁰⁷–¹¹⁶, Lean).**
  - Pivot monotonicity, fresh-word transport and the first ideal-orbit stage are each refuted or equivalent to Cut
    (`first_stage_iff`).
  - Refinement by dominated rows is inert, and capturing rows have unconstrained orbits (`DominatedRows`).
  - Grid capture holds without a chain condition once entry times are given (`cut_of_grid_capture_upto`). Its ground
    instances do not help the edge-height-6 search: they are almost always satisfied by one orbit point.
- **Axis capture and bounded support (§34.3z¹¹⁷–¹¹⁸, Lean).** An axis-capture graph splits each finite row family into
  an axis escape or an interior mixed pivot with Alternative I (`axis_or_mixed`). At edge-height ≤ H a minimal mixed
  pivot has 2 ≤ |S| ≤ H − 1 and tᵢ + |S| ≤ H (`mixed_minimal_support`). Partial models nevertheless realize
  repeated new maxima, cross cells and boundary completion at constant height 3 (`experiments/sat/axis_*.py`,
  `cross_cells.py`).
- **Finite faithful images (§34.3z¹¹⁹, Lean).**
  - A witness-free structure has no finite faithful poset image (`faithful_image_impossible`). The lattice-congruence
    form is a corollary.
  - Half-filtration: a finite meet-closed family separating every cross pair forces a witness
    (`separating_family_witness`, and its dual).
  - On ω + 1 the coarsest D-saturated congruence has two classes and violates cut-separation, so finite index is not
    the obstruction.
- **Extremal separators (§34.3z¹²⁰–¹²³, Lean).**
  - Maximal separators exist under ACC and are ⊓-irreducible; aggregation has an exact criterion
    (`ExtremalSeparators`).
  - The refinement process is defined, with stopping conditions, persistence, the causal chain, and "a terminal run
    gives Cut" (`SeparatorStages`).
  - The closure-rank drop, the causal fork, and the contained branch at edge-height 6 via `cut_height5` are proved
    (`SeparatorRank`).
  - So are bounded meet and join supports, fresh tokens, fan collapse, and a generic potential-parent stage bound
    (`SeparatorAncestry`).
  - Search (`experiments/separation/`): f(H) = H − 1 is refuted for maximal separators by an exact height-4 instance,
    which needs 4 stages under every choice. Rank-only potentials, scalar or multiset, fail on that instance. The gap
    potential rank y − rank x survived the mutation tests of these rounds; exact search later refuted it for maximal
    separators (§34.3z¹³⁶, below).

**Later (§34.3z¹²⁴–¹⁴⁰): what the separator process can and cannot do, and the orbit-length conjecture.**
- **Proved in Lean.**
  - The crossing-interval order is well-founded (`IntervalRefinement`).
  - Interface traces, patching and pinning, and the infinite-antichain obstruction `atom_family_block`
    (`InterfaceTrace`).
  - Gap-parent and maximum-gap-drop runs force a witness within 2H + 1 stages (`GapPotential.cut_of_gap_parent`,
    `MaxGap.cut_of_max_gap_drop`).
  - The finite state graph, distance and optimal successors of the process (`ShortestRun`).
  - The response run transfers to finite lattices, so a uniform finite response bound would give Cut
    (`ResponseRun.cut_of_resp_bound`).
  - The gap implications hold for **any** sequence of finite meet-closed stages, and for runs with general
    (non-maximal) separators; a terminating general run gives a witness (`GeneralRun`, §34.3z¹³⁶).
- **Refuted by exact finite search** (SAT/CEGAR on fixed lattices, explicit families verified by simulation).
  - Every deterministic rule tested has run length growing with width at edge-height 3, where Cut is a theorem:
    - the response rule, 2k − 1 on near-pencils (§34.3z¹³²);
    - term-closure rules of depth ≤ 3, with or without meets, and the full closure (§34.3z¹³³);
    - lookahead rules (§34.3z¹³⁴);
    - SAT witnesses are *forced* runs, so no selection policy over closure-maximal separators helps.
  - **The maximal-separator conjectures fail at edge-height 3** (§34.3z¹³⁶): the existential minimum is k − 1 on
    near-pencils (k = 3..9). The line-cycle family and a minimal 6-element instance (M₃ with an extra bottom, three
    coatoms in a cycle) have no maximum-gap-descending maximal run. This refutes the finite forms of ∃-max-gap
    descent, ∃-gap-RP and shortest-run descent.
  - No local or bounded-lookahead progress lemma exists. A legal first move can cost a number of further stages that
    grows with width (§34.3z¹³⁸–¹³⁹).
- **Surviving, with exact evidence.** Restrict each bad pair's separator to the response F(x, y) or a maximal
  separator.
  - No instance without a descending run exists on any of the 162 closure systems on 4 points, nor on any decided
    5- or 6-point lattice.
  - The exact worst-case shortest run is **H − 1** on all 179 four-point closure systems and on the height-5
    lattices tested; chains attain H − 1.
  - Along some shortest run the lexicographic potential (−min rank x, max rank y) decreases in all 1,194,594 audited
    instances (§34.3z¹³⁷).

- **The R-orbit has length H (§34.3z¹⁴⁰).** Exact SAT on every finite lattice checked shows that the down-set orbit
  R₀ = ↓⊥, R_{k+1} = ↓(R_k ∪ a(R_k) ∪ b⁻¹(R_k)) reaches L after exactly H stages in the worst case, at edge-height
  H. The lattices checked are all 184 closure systems on 4 points and random lattices up to height 6 and |L| = 40.
  The orbit-height invariant behind this (OH: if ⊤ ∉ R_k, then R_k has an element of height ≥ k) also holds
  exactly. Lean (`OrbitHeight`) proves the chain *tight-stage upper principal cut ⇒ rising escape ⇒ OH ⇒ R_H = L ⇒
  Cut*, and its first cases (`escape`, `orbitHeight_one`). `InterfaceExtraction` shows that the line-cycle
  counterexamples to maximal descent force a lower witness via `atom_family_block`. The step then sharpens to the *tight-stage
  interval cell* (§34.3z¹⁴¹, exact on all lattices checked). It is proved in Lean whenever some top element is
  diagonal (m ≤ F(m, m): `upc_of_le_diag`, which covers 99.92 % of random tight stages), and at the first tight
  stage when a(⊥) ≠ ⊥. The non-diagonal residue, in which every top element entered through b, already occurs on
  the 4-element chain and is the open case. The brief's normalized form of this lemma (§34.3z¹⁴²) turns out to
  be the Cut Lemma itself: a lower cell at a maximal-height element of R(G) is a cell across R, and no such cell
  exists (`BottomMaxCell.R_no_cross_cell`). Proved there: **the Cut Lemma holds for F whenever R(F) has height ≤ 1**
  (`cutMaps_of_R_atomic`, a bouquet with centre ⊥); forced near-cells over atoms and below minimal non-members.

- **Rank-two cuts (§34.3z¹⁴²–¹⁵¹).**
  - **Cut holds whenever R(F) has height ≤ 1** (`BottomMaxCell.cutMaps_of_R_atomic`: an atomic cut is a bouquet
    with centre ⊥).
  - For height 2, Lean proves the incidence structure (blocks meet in ⊥ or one point) and isolated petals
    (`RankTwoIncidence`).
  - In a star of blocks it also proves that the bouquet induction fails only at a *relay* (`RelayDescent`). Every
    relay descends to a rigid terminal form F(⊥, u) = s, F(s, u) = F(b, u) = a ≤ u, u ⊓ F(a, u) = a, and the
    "private seed" alternative is impossible.
  - At edge-height 6, `cut_height5` on intervals gives escape cells below every proper non-member and above every
    nonzero member (`ClippedIntervalCut`).
  - Partial models show that the remaining contradictions need full intervals or the infinite cross-closure. Several
    proposed intermediate statements (normalized BottomMaxCell, "no escape", escape ladders) turned out equivalent
    to Cut itself.

**Open frontier now.** Chain-finite Cut, equivalently join-closure of R(F) (`Frontier.lean`), for cuts where **both**
Max D and Min Dᶜ are infinite; at bounded height, edge-height 6 is the first open case. The sharpest concrete target is now a
choice-free one (§34.3z¹⁴⁰): the **tight-stage upper principal cut**. At a stage where R_k has height exactly k and
⊤ ∉ R_{k+1}, some element m ∈ R_k of height k has a witness cell x ≤ m < y. By `OrbitHeight.cutMaps_of_tightUPC`
it gives Cut at every finite edge-height. The statement is false for an arbitrary m, so a proof must use the
orbit. The existential general-separator conjectures remain as an alternative:
- **GSB(H):** every instance of edge-height H has a response-or-maximal run of at most H − 1 stages;
- **GD(H):** some such run has strictly decreasing maximum gap.

Through `cut_of_terminal_grun` and `cut_of_max_gap_drop_general`, either one at H = 6, in the witness-free setting,
gives Cut at edge-height 6. The finite tests are evidence only: transferring an existential run from finite lattices
is blocked by the stuck test (§34.3z¹³²), and §34.3z¹³⁹ shows that a proof must plan the run globally. Also still
open:
- the poset form of FG∞ at k = 3 (max-only CLL);
- Ω × Ω × Ω;
- products with a factor that is not end-finite.

## Repository layout

| Path | Contents |
|---|---|
| `docs/00-foundations.md` | The formal system: ambient setting, bialgebraic & dialgebraic axioms, bounds, interaction rules, metatheorems, with status tags; the CL program and the Cut Lemma interface (§0–§10, v3.7) |
| `docs/00-foundations-double.md` | Draft: the axioms raised to double categories (horizontal monads, vertical comonads, dialgebras as universal squares, tabulator bounds, equipment interaction rules); its model E(L) restates the bridge as representability of μΘ (§34.3z⁶¹, `Axioms/Double.lean`) |
| `docs/01-early-notes.md` | Early revision notes and first exploration findings (v1.1–v1.2) |
| `docs/rounds/` | The research log, one file per exploration round (rounds 2–26, versions v1.3 → v3.8) |
| `docs/02-the-source.md` | The framework's Tolkien vocabulary read back to its source; the sharpened axioms (I11 = CL guarded by the Cut Lemma) |
| `docs/README.md` | Index to the research log with one-line summaries |
| `experiments/` | The machine-experiment stack: exact realizability CSP solver, E₃ census pipeline, validation harness |
| `gpu/` | GPU census of the projection F ↦ (a, b): exact enumeration and heat-bath MCMC with tripwires (PyTorch, ROCm/CUDA/CPU); see `gpu/README.md` |
| `experiments/sat/` | Round 22: direct SAT encoding (CaDiCaL via PySAT), DRAT certification, semi-commutation and Cut Lemma sweeps, z3 theories |
| `lean/` | Round 26: Lean 4 / Mathlib proofs of the log's proved core (Mathlib is a lake dependency, not committed) |
| `data/gpu-2026-10/` | Round 25: results.jsonl and batch.log of the first GPU run |
| `experiments/finite_support/`, `experiments/asyncgrid/`, `experiments/infcapture/` | Round 26, §34.3z⁹⁷–¹¹⁵: z3 orbit and support profiles of the crossing case, the asynchronous-grid label abstraction (`reduced_grid.py`), good-word compatibility, grid refinement, dominated and capturing rows |
| `experiments/separation/` | Round 26, §34.3z¹²⁰–¹³⁹: the extremal-separator process on finite lattices (bitset search, replayable records), rank, ancestry and potential audits; response, term and lookahead rules with exact SAT maxima; exact CEGAR for existential minima and descent-free instances (`exist_cegar.py`, `nodesc_sweep.py`); the line-cycle family; restricted, local and lookahead progress audits |
| `experiments/amalgamation/` | Round 26, §34.3z¹⁴⁰: exact R-orbit stages (SAT for a = gfp, b = lfp), slow joins, the orbit length, the orbit-height invariant, rising escape and the tight-stage upper principal cut |
| `experiments/intervals/` | Round 26, §34.3z¹²⁴–¹²⁶: anchor envelopes, safe selection, Veinott and antichain-pin experiments |
| `experiments/dialgebra/` | Round 24: thin-model dialgebra censuses (transposition, failure zone, D5), the Cut Lemma transposition, orbit-laxity z3 searches |
| `data/` | Machine-experiment results (JSON) |

## The machine method, in one paragraph

CL fails on a lattice L exactly when some interval of L carries a **commuting polar pair** (a, b) — monotone, bound-fixing, a∘b = b∘a — is **realizable** as the derived pair of a monotone bifunction (a(x) = gfp_y F(x, y), b(y) = lfp_x F(x, y)). Realizability is an exact finite constraint problem on F: pin cells F(x, a(x)) = a(x), F(b(y), y) = b(y), the strong exclusions (E2⁺: y ≰ a(x) ⟹ F(x, y) ∉ ↑y; E3⁺: b(y) ≰ x ⟹ F(x, y) ∉ ↓x), and monotonicity in both coordinates. The solver (unary domains → AC-3 on cover arcs → MRV DFS) is exact — validated against the exhaustive chain-4 ground truth, 223 = 223. Censuses kill commuting pairs in bulk with sound relaxations only (T1 block unary tables, 40-cell interface sub-CSPs); every survivor is refuted by the exact solver. See `experiments/README.md`. Since round 22 the same criterion is also solved directly as one SAT instance per interval, with the pair (a, b) as variables (`experiments/sat/`).

## Reproducing the censuses

The census pipeline is a single self-contained TypeScript program (`experiments/e3-two-crossing-census.ts`); each two-crossing class is one parameter line. Each class census runs in about a minute in a sandboxed TypeScript runner. Anchors and tripwires for revalidation are listed in `experiments/README.md`.

## Reading the log

Start with `docs/README.md`. Each round file is self-contained prose: what was asked, what the machine found, what was proved, what remains open, and an honest-scope section stating exactly what the round does *not* cover. Errata are recorded in place and withdrawn explicitly — audits are themselves censuses.