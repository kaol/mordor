# Brief, run 20: outside briefer (adjoint-math-research v1.0)

**Repository:** /home/user/mordor at **65453b9**. It was read-only: nothing in the checkout was written, built or
changed. The only git command was `git log --oneline -1`.

Checked at source:
- `lean/Mordor/StairB1.lean`, all of it: `tbFibre`, `exists_first_low`, `landEq_of_above`, `certAtom_of_N1`,
  `fixed_of_uniformFibre`, `certAtom_of_N1_thin`, `certAtom_of_N1_exit`.
- `lean/Mordor/Normalize.lean`: `CertAtom`, `mem_one_iff`, `w0_of_T`, `goodTop_iff_certAtom`.
- `LateParent.lean`, section `Landing`: `land_index_pos`, `land_not_le`, `land_bot_lt`, `exit_atom`, `land_unique`,
  `cert_of_exitFixed`, `trap_of_tb`, `domCoLand`, `tb_of_tight`, `exitFixed_of_dom`, `upTrap_stay`, `upTrap_land`,
  `fixedBelow_of_exitDom`, `goodAtom_of_greatestZ`.
- The log `docs/rounds/26-v3.7.md`, §34.3z²⁹¹–²⁹⁴.
- `experiments/amalgamation/brief293/brief.md`, in full.
- `orbit_probe.py` (world encoding, Stair / Row1 / LastEither / Desc1 / Meet2 flags and the replay), `stair_probe.py`,
  `bank.py`, `brief291/world.py`.

**Work directory:** everything this brief produced is in
`/tmp/claude-0/-home-user/3b6fdd2c-c95c-5c07-b47c-6ae28c687a4c/scratchpad/amr_run20/brief/`:
- the Lean file `PairTrap.lean`, with `lean_axioms_out.txt`;
- the testers and free analyses (`*.py`) and their outputs (`*_out.txt`);
- run directories `run1/`–`run4/`;
- refuting models in `cex/` and `run*/`.

**Mission (negation of the failure signature).** Do not predict which row certifies. Pick a row whose landing every
colour atom must already lie under, and let one staircase invariant close the case. Where no such row exists, make
the certificate set the object, not a walk to it.

---

## 0. Summary

1. **CertAtom holds at N = 1 in every branch, in W0.** A1 is closed. The proof is complete on paper (§4.2) and was
   compiled in the briefer's scratch copy against the repository's Lean files: `PairTrap.lean`, standard axioms only,
   no `sorry`.
   - New tool **`pairStair`**: a staircase for two rows x, y with a common lower row q as the *value* row.
   - **`certAtom_of_N1_all`**, and **`certAtom_N1 : F ⊥ (F ⊥ ⊤) = ⊥ → CertAtom F H`**.
   - Proof of A1 in four lines. If row d does not exit, put m = λ(d) ∈ Z and q₀ = m ⊓ d. Every boundary value of row
     q₀ on the (d, m)-staircase that lies below m equals m, because every colour φ(B) lies below φ(⊤) = d. By downward
     induction m ≤ λ(m). That contradicts `land_not_le`.
   - No connector can arise. §294 picked the wrong pair; ConnectorClose is not needed for A1 (ladder audit, §2).
2. **TopRow (new rung, every N, Lean in `PairTrap.lean`): `certAtom_of_topRow`, `certAtom_of_boundedAtoms`.**
   - TopRow: if some element x has a landing row and lies above every atom of Z that is a value of row ⊥, CertAtom
     holds.
   - BoundedAtoms: in particular, CertAtom holds whenever 𝒜 (the atoms of Z in φ(L)) has an upper bound in Z.
   - This covers all 96 stored N = 1 models and 56 of the 95 stored W0 models at N ≥ 2 (samples).
   - It is the N = 1 argument with d replaced by any landing row above the colours: a reduction of every N to "some
     row above 𝒜 lands".
3. **That reduction's universal forms are refuted.** TopLand asks whether the least admissible row above 𝒜 (after
   renormalizing the rows outside Z) lands.
   - Refuted on 16–17 stored W0 models.
   - Refuted by exact search in branch a as well (run 3; smallest |L| 14, H 5, N 2).
   - ClosureLand, the ⊥-seeded accumulating version, is refuted on 7 stored models (Orbit3, N 3).
   - "Some closed set exists" is the target in other words.
   - So beyond N = 1 the open case is now sharp: N ≥ 2, 𝒜 unbounded in Z (|𝒜| ≥ 2), every joint row stuck. It holds
     39 of the 191 stored W0 models, 20 of them with |𝒜| = 2.
4. **The Stair and W0² worlds at A1 are not covered by the theorem.** The proof uses Tb at m ⊓ d at meets of
   desc(d) and desc(m), which is neither a W0² nor a Stair column. Runs 2 and 4 test StairTb and TwoRowTb at
   exact N = 1 with room (§6).
5. Runs 2 and 4: StairTb (0/8) and TwoRowTb (0/17) hold at exact N = 1 with room (H 13–14, M 6–7), mutants failing. They are provisional at A1. In W0² the A1 theorem therefore has a proof yet to be found that avoids three-row columns (P3's open step).
6. Frontier corrections: 15 (§16).

## 1. Frontier (restated; checked at source)

- L finite (`NoChain α (H+1)`), F monotone in both arguments, φ = F(⊥, ·), a(x) = gfp F(x, ·).
- "High" means height ≥ 3, "low" means height ≤ 2. Descent u_j(x) = (F x)^j ⊤. λ(x) is the first low element of the
  descent, at index i(x), and r_x = u_{i(x)−1}(x).
- **W0 ∧ n1**: a(⊥) = ⊥, R_2 tight, ⊤ ∉ R_2, R_1 not tight. Then Z = R_1 = φ⁻¹(⊥) (`mem_one_iff`); Z is a down-set
  of heights ≤ 2 (ZT). At every row x of Z:
  - Ta: no high y has y ≤ F(x,y) (⟺ x lands, `ta_iff_lands`);
  - Tb: no high y has F(x,y) ≤ x (`tb_of_tight`).
- `land_not_le`: λ(x) ≰ x for x ∈ Z.
- `exitFixed_of_dom`: for **any** row x (not only x ∈ Z) whose descent reaches a height-2 p with φ(p) = c an atom of
  Z and c ≤ x, c is μ-fixed. Checked in source: its hypotheses do not ask x ∈ Z.
- `w0_of_T`: W0 depends only on row ⊥ and the rows of Z. So the rows outside Z may be redefined (any monotone
  extension) without changing W0, Z, the descents of Z-rows, or CertAtom's conclusion. This is the nrmHom principle.
- **Open target CertAtom** (`CertAtom`, Normalize.lean): some atom q of Z has λ(q) ∉ Z and φ(λ(q)) = q.
- d = last nonzero t_j of the ⊥-descent t_j = φ^j(⊤); N is its index, and t_1 = φ(⊤). Every φ-value lies below t_1.
- **𝒜** := {atoms c of Z : c = φ(w) for some w}. It contains every colour atom at a staircase boundary, every exit
  atom c(x) = φ(λ(x)), and φ(r_x) when λ(x) is an atom.

## 2. Ladder audit

### 2.1 §34.3z²⁹⁴, step by step

| step (§294) | re-derived | verdict |
|---|---|---|
| 0. `certAtom_of_N1_exit`: at N = 1 a row-d exit is dominated, φ(λ(d)) ≤ φ(⊤) = d | source: `fixedBelow_of_exitDom` with hdom from `(F ⊥).mono le_top` | ✓ Lean |
| 1. no exit ⇒ m = λ(d) ∈ Z, m ≰ d, φ(r_d) = q₀ = m ⊓ d an atom, m ∈ M2 | φ(r_d) ≤ F(d, r_d) ⊓ φ(⊤) = m ⊓ d. It is nonzero by ZT. d ≤ m would force m = d (both low, h(d) = 2), against `land_not_le` | ✓ |
| 2. F(q₀, r_d) = m | q₀ = φ(r_d) ≤ F(q₀, r_d) ≤ F(d, r_d) = m; ≠ q₀ by Tb; h(m) = 2 | ✓ |
| 3. F(m, r_d) high | ≥ m, ≰ m by Tb at m | ✓, unused below |
| 4. NoFix ⇒ a connector on the (q₀, d)- or (q₀, m)-staircase | correct: with neither, `landEq_of_above`'s argument gives λ(q₀) = λ(d) = m = λ(m) | ✓ as a reduction, **misplaced as a rung** |

**Finding.** Step 4 reduced A1 to a located statement (ConnectorClose for two named pairs) that is *stronger than
needed*. The pair that closes A1 is **(d, m) itself, with value row q₀ = m ⊓ d**. Its boundary points are meets of
desc(d) and desc(m), and there every colour lies below d. So the only atom a boundary value below m could take is
q₀, and Tb at q₀ excludes it (§4.2). "Every proof must handle connectors" (brief293 §11) is false at N = 1.

### 2.2 Other rungs re-derived

- `certAtom_of_N1_exit`: "⟸" is Lean. The "⟹" via `upTrap_land` is now moot: row d always exits at N = 1
  (§4.3 AboveD).
- **StairTb, TwoRowTb at A1 are not implied by the new theorem.** The proof uses Tb at q₀ at u ⊓ v with
  u ∈ desc(d), v ∈ desc(m). W0² and Stair keep Tb at q only at u ⊓ v with u ∈ desc(q). So the rungs
  "CertAtom ⟸ TwoRowTb ⟸ StairTb" keep their placement. Their content at A1 is now *beyond* the target, not *at*
  it. Runs 2 and 4 probe them (§6).
- `fixed_of_uniformFibre` / `certAtom_of_N1_thin` are special cases of `certAtom_of_N1_all`. They are subsumed, not
  wrong.
- Placement of the new rungs, each re-derived from its Lean proof:
  - CertAtom ⟸ BoundedAtoms ⟸ (N = 1);
  - CertAtom ⟸ TopRow;
  - BoundedAtoms ⟸ GreatestZ (Z has a greatest element).

  GreatestZ ⟹ GoodAtom1 was `goodAtom_of_greatestZ`; the new rung gives the stronger conclusion CertAtom from a
  weaker hypothesis.
- **Disguised-target check.**
  - BoundedAtoms is strictly stronger than CertAtom: 39 stored W0 models fail it and have a fixed atom.
  - "Some S ⊆ Z ∪ {⊥} is closed" (§5) is ⟺ CertAtom. Take S = {⊥, q*} for a fixed q*. It is a **restatement**;
    do not carry it as a rung.

## 3. Reuse (real names)

- From `LateParent.lean`: `land_index_pos`, `land_not_le`, `tb_of_tight`, `exitFixed_of_dom`, `domCoLand`,
  `trap_of_tb`, `ta_iff_lands`, `mem_succ_of_cell`, `iter_antitone_of_le`, `eq_of_le_of_height_ge`,
  `height_strictMono`, `height_bot_eq_zero`, `Rk_mono`.
- From `Normalize.lean`: `CertAtom`, `mem_one_iff`, `w0_of_T`.
- From `StairB1.lean`: `exists_first_low`, `certAtom_of_N1_exit`. The proof of `landEq_of_above` is the template
  for `pairStair`.

---

## 4. LEAD: the pair staircase; CertAtom at N = 1 (A1 included)

### 4.1 `pairStair` (Lean, `PairTrap.lean`; paper below)

Rows x, y and a value row q with q ≤ x and q ≤ y. Write v_j = u_j(x) and w_k = u_k(y). Both rows land, at indices
i and i′. Put p = λ(x) and suppose h(p) = 2 and h(⊤) ≥ 3.

Grid: G(j,k) = v_j ⊓ w_k, antitone in both arguments. For l < i, κ(l) is the least k with G(l,k) low; it exists
(k = i′) and is ≥ 1 (G(l,0) = v_l is high). κ is non-increasing. The boundary point is B_l = G(l, κ(l)−1), which is
high.

1. e_l := F(q, B_l) ≤ F(x, v_l) ⊓ F(y, w_{κ(l)−1}) = G(l+1, κ(l)). This uses q ≤ x and q ≤ y.
2. **Absorption hypothesis** (habs): every high B with F(q, B) ≤ p has F(q, B) = p.
3. Downward induction on l from i−1. Base: e_{i−1} ≤ G(i, κ) ≤ v_i = p, so e_{i−1} = p. Step: from e_{l+1} = p,
   p ≤ G(l+2, κ(l+1)) ≤ G(l+1, κ(l+1)), which is low, so it equals p. Then
   e_l ≤ G(l+1, κ(l)) ≤ G(l+1, κ(l+1)) = p, so e_l = p.
4. Conclusion: p = e_0 ≤ G(1, κ(0)) ≤ w_{κ(0)} = w_{i′} = λ(y), since κ(0) = i′. **So λ(x) ≤ λ(y).** ∎

Rows x and y need not lie in Z. Only the value row's Tb enters, through habs.

### 4.2 Theorem (Lean: `certAtom_of_N1_all`, `certAtom_N1`): W0 ∧ N = 1 ⇒ CertAtom

Here d = φ(⊤) ∈ Z.
1. If row d exits, its exit atom is dominated, φ(λ(d)) ≤ φ(⊤) = d, and is μ-fixed (`certAtom_of_N1_exit`).
2. Otherwise m := λ(d) ∈ Z, and m ≰ d (`land_not_le`). Put q₀ := m ⊓ d, which is in Z (≤ d).
   - ⊥ < φ(r_d) ≤ q₀, so q₀ ≠ ⊥.
   - h(q₀) = 2 is impossible: it would give q₀ = d = m.
   - So q₀ is an atom, and h(m) = 2.
3. habs for (q, x, y, p) = (q₀, d, m, m). Let B be high with F(q₀,B) ≤ m.
   - φ(B) ≤ F(q₀, B) ≤ m and φ(B) ≤ φ(⊤) = d, so φ(B) ≤ q₀.
   - φ(B) ≠ ⊥ (ZT), so φ(B) = q₀ ≤ F(q₀, B).
   - F(q₀,B) ≠ q₀ (Tb at q₀).
   - So q₀ < F(q₀,B) ≤ m, and F(q₀,B) = m.
4. `pairStair` gives m ≤ λ(m). λ(m) is low, so λ(m) = m ≤ m, against `land_not_le` at m. ∎

Branch b/g (d an atom) runs the same way: q₀ = d when d < m. So this also re-proves `certAtom_of_N1` and A1-thin.

**Hypotheses used:**
- ZT;
- Ta at d and m (landing);
- `land_not_le` at d and m (Tb at d and m at their landing predecessors);
- **Tb at q₀ at the boundary points of the (d, m)-staircase**: three-row columns u ⊓ v, u ∈ desc(d), v ∈ desc(m);
- in the exit case, Tb at the exit atom as `domCoLand` uses it (two-row meets, `trap_of_tb`).

### 4.3 Corollaries (paper; from the Lean statements)

- **AboveD.** At N = 1 every row x ∈ Z with x ≥ d exits, with a dominated exit atom. This is TopRow (§5.1) at x.
  Free check: holds on all 116 such rows of the 96 stored N = 1 models (`pairtrap_out.txt`).
- **PairTrap (any N).** If x ∈ Z lands at y = λ(x) ∈ M2, then some boundary point B of the (x, y)-staircase has
  F(x ⊓ y, B) = φ(B) an atom of 𝒜 with φ(B) ≤ y and φ(B) ≰ x. This is the contrapositive of 4.1 with q = x ⊓ y,
  taking the largest l with e_l ≠ y. Free check: holds on all 326 such rows of the 191 stored W0 models.

### 4.4 Programme fields

| field | content |
|---|---|
| candidate | the theorem of 4.2: **complete**, Lean-checked in the briefer's scratch copy, to be re-checked in the repository |
| payoff | it closes N = 1, so CertAtom ⟹ GoodAtom1 (`goodAtom1_of_cert1` via Cert1) and GoodTop at N = 1 |
| placement | CertAtom ⟸ BoundedAtoms ⟸ (N = 1); subsumes `certAtom_of_N1`, `certAtom_of_N1_thin`, `fixed_of_uniformFibre` at N = 1 |
| testability | a theorem; search checks only the encoding. Bank replay: 0 failures on the 96 stored N = 1 W0 models |
| hypothesis world | W0 ∧ N = 1. Relaxation for the footprint: Row1 at E1 (refuted relative, has A1 NoFix models) |
| anatomy | none (theorem). In relaxed worlds a NoFix model must violate one used hypothesis. Footprint replay: of the 93 stored relaxed-world N = 1 NoFix models (Row1/LastEither/Desc1/W0♭ dumps on file), 54 violate exactly **Tb at q₀ = m ⊓ d at a (d, m)-boundary point**, 34 violate `land_not_le` at d or m (W0♭-type worlds), 5 have a dominated exit of d without a fixed atom (exit-case Tb dropped). Of run 1's 8 new Row1 E1 models, 7 violate the (d, m)-boundary Tb and 1 the exit-case Tb. None escapes every used hypothesis (`pairtrap_out.txt`, `run1/footprint_replay_out.txt`) |
| mode | ladder audit (§294's rung misplaced), then signature inversion: no predicted certificate row; the invariant e_l = m propagates along the whole boundary |
| limit | needs a landing row above every colour atom. At N ≥ 2 the colours lie below t_1 ∉ Z (§5) |
| decisive open step | none at N = 1. For the transfer to N ≥ 2: JointStuck (§5.3) |

## 5. P2: TopRow, BoundedAtoms, and why the reduction to N = 1 stops

### 5.1 `certAtom_of_topRow` (Lean)

In W0, let x be any element whose row lands at p (first low element of its descent). Suppose every atom of Z that is
a value of row ⊥ lies below x. Then CertAtom holds.

- *p ∉ Z.* c = φ(p) < p is an atom of Z (as in `exit_atom`, using a(⊥) = ⊥), and c ≤ x. So c is μ-fixed
  (`exitFixed_of_dom`; x need not be in Z).
- *p ∈ Z, p ≤ x.* F(p, r_x) ≤ F(x, r_x) = p, against Tb at p.
- *p ∈ Z, p ≰ x.* q = x ⊓ p < p, and every Z-atom of φ(L) below p lies below q. So habs holds:
  - a colour atom below p is q, and Tb lifts it to p;
  - a height-2 colour below p is p itself.

  `pairStair` gives λ(p) = p, which is impossible.

**`certAtom_of_boundedAtoms`:** if some x ∈ Z lies above 𝒜, take its row (it lands by Ta). N = 1 is x = d.

### 5.2 TopLand: the universal transfer, refuted

By `w0_of_T`, the rows outside Z are free. The least admissible row at X = ⋁𝒜 is G_X = ⋁_{z∈Z, z≤X} F(z, ·). The
transfer "make the row above the colours land" therefore reads TopLand_X: the G_X-iteration from ⊤ gets low.

A sharper virtual-row form is paper only. The proof of 5.1 goes through verbatim for g_S = ⋁_{z∈S} F(z,·) with
S = {⊥} ∪ 𝒜 ∪ {height-2 z ∈ Z above two atoms of 𝒜}. That form is TopLand_S ⟹ CertAtom. `topland_census.py`
reports 0 proof failures on the stored models: the predicted φ(p) is μ-fixed in every case where g_S lands.

| statement | free (stored W0, samples) | exact search (run 3) |
|---|---|---|
| TopLand_X | fails 17/191 (all atom, N ≥ 2; smallest \|L\| 15, H 5, N 2) | — |
| TopLand_t1 (X = t_1) | fails 34/191 (a 4, atom 30) | fails in branch a, N ≥ 2: 51/63 lattices (mutant) |
| TopLand_S | fails 16/191 | **fails in branch a, N ≥ 2: 48/63 lattices** (smallest \|L\| 14, H 5, width 5, N 2); branch atom 59/63 |
| ClosureLand (S_0 = {⊥}; add what the landing lacks) | STUCK on 7/191 (s278–s280 Orbit3, N 3; smallest \|L\| 30, H 8) | — |
| restriction to ↓t_j (F ⊓ t_j) | leaves W0 on 58 stored models (Tb breaks) | — |

All refuting models are saved: `cex/*.json` (copies of the stored sources, with coordinates) and
`run3/cand_*.json`, `run3/m*.json`.

### 5.3 Programme fields

| field | content |
|---|---|
| candidate | **normal form (proved, paper plus Lean for the actual-row case): CertAtom ⟺ CertAtom on the stuck world** W0 ∧ (𝒜 unbounded in Z) ∧ (g_S stuck for S = {⊥} ∪ 𝒜 ∪ {height-2 z ∈ Z above two atoms of 𝒜}). Off it, BoundedAtoms or TopRow-S gives a fixed atom. The programme then asks for **JointStuck**: in the stuck world, the high joint fixed point Y = ⋁_{z∈S} F(z, Y) (each F(z,Y) < Y by Ta) yields a proper sub-family S′ ⊂ S whose g_{S′} lands and is closed (§5.2 sense), or a Tb violation |
| payoff (conditional) | JointStuck ⟹ CertAtom: a closed S′ gives a fixed atom (TopRow-S, 5.1/5.2), and a Tb violation contradicts W0 |
| placement | the normal form sits at CertAtom. JointStuck sits at CertAtom restricted to the stuck world. **Restatement risk**: "some closed S′ exists" is CertAtom itself (S′ = {⊥, q*}). JointStuck counts only if S′ is produced *from Y* (a construction), not asserted |
| testability | the stuck world has models (run 3: 48 lattices in branch a, 59 in branch atom), so its *anatomy* is testable. JointStuck as a construction is `needs direct proof`. Note: every z ∈ S has F(z, Y) ≤ g_S(Y) = Y, so every colour row (the fixed atom included, which lies in 𝒜) descends from Y and staircases started at Y apply to all of S. The "shadow" "some fixed q* has F(q*, Y) ≤ Y" is therefore trivially true; it was checked free anyway (123/123 stuck models, `stuck_shadow_out.txt`) and carries no information |
| anatomy of a CertAtom counterexample (now forced) | N ≥ 2; \|𝒜\| ≥ 2; ⋁𝒜 ∉ Z; for every S between {⊥} ∪ 𝒜 and Z, g_S stuck at a high Y = ⋁_{z∈S} F(z, Y) with every F(z, Y) < Y (Ta). The smallest such W0 lattice (with a fixed atom) is \|L\| 14, H 5 |
| mode | signature inversion (the set of colour rows as one object) |
| limit | gives no ranking. Every "∃ closed S" form is a restatement |
| decisive open step | **JointStuck**: from Y, choose S′ by a rule stated in terms of Y and the colours below the corners of the staircases started at Y (generalized `pairStair` with u_0 = Y ≤ v_0 = ⊤ gives λ ≤ Y ⊓ w_{κ(0)}), and prove the rule's S′ closed |

## 6. P3: are StairTb / TwoRowTb right at A1? (sharpness of the pushed rungs where the target is now a theorem)

| field | content |
|---|---|
| candidate | StairTb and TwoRowTb restricted to N = 1 (branch a is A1) |
| payoff | if either fails at A1, the pushed rung is refuted. Then the frontier's lead world is too large, and three-row Tb instances (§4.2) are necessary |
| placement | CertAtom(N = 1) ⟸ TwoRowTb(N = 1) ⟸ StairTb(N = 1), with the left end now proved |
| testability | finitely refutable (`orbit_probe.py nofix 0 Stair E1` / `Meet2 E1`) |
| hypothesis world | Stair or W0² at exact N = 1. NoFix models exist in the mutants LastEither E1 and Row1 E1 (runs 1, 2) |
| anatomy | a pair (q₀, x) staircase with a connector, closed in W0 only through a three-row Tb instance at m ⊓ d. Room: H ≥ 8 (Row1 relatives fail from H 8), width, \|𝒜\| = 2 |
| mode | ladder audit |
| limit | says nothing at N ≥ 2 |
| result | **provisional at A1, both**: Stair E1 0/8 (mutant 7/8, 2 of them A1) and Meet2 E1 0/17 (mutant 17/17, 12 A1), H 13–14, M 6–7. So W0² and Stair carry the A1 theorem empirically, without the three-row columns the proof uses. The decisive open step is a proof of A1 from W0² columns only: either a two-row replacement of the (d, m)-boundary Tb instance, or a proof that W0² ∧ A1 ⟹ that instance |

## 7. P4: two colour atoms (the smallest open case)

| field | content |
|---|---|
| candidate (conjectural) | CertAtom when \|𝒜\| = 2, i.e. 𝒜 = {a, b} with a ∨ b ∉ Z |
| what is already forced (paper, from 4.1 and 5.1) | NoFix gives b ≤ λ(a) and a ≤ λ(b): each atom's landing carries the other colour (as its exit atom, a PairTrap connector, or an atom landing). If λ(a) ∈ Z then a ≰ λ(a), else λ(a) ≥ a ∨ b ∈ Z; an exit landing above both atoms is a ∨ b ∉ Z. The virtual row F(a,·) ∨ F(b,·) is stuck at a high Y = F(a,Y) ∨ F(b,Y) with both values < Y (TopRow with S = {⊥, a, b}, which is closed whenever it lands) |
| payoff | closes 20 of the 39 stored open models' class |
| testability | needs direct proof (vacuous in W0). Relaxation: Stair ∧ NoFix ∧ \|𝒜\| = 2 |
| decisive open step | contradict "λ(a) ≥ b, λ(b) ≥ a, F(a,Y) ∨ F(b,Y) = Y" with Tb at a and b at the meets Y ⊓ u, u on the other atom's descent: the pair staircase started at Y (generalized `pairStair` with u_0 = Y ≤ v_0 = ⊤ gives λ ≤ Y ⊓ w_{κ(0)}) |

## 8. Probe scripts (work dir; `PYTHONPATH=/home/user/mordor/experiments/amalgamation:/home/user/mordor/experiments/separation`)

Testers:
- `topland_probe.py` (new exact SAT encoding, same row scheme as `stair_probe.py`). World: full W0 through (T).
  - Flags: branch (Ba / Bb) and N (exact E2–E6, or Nge2), read through the ⊥-descent iteration.
  - Encoding of 𝒜 and S: A(q) ⇒ Z(q) ∧ ∃w f(⊥, w, q); s(z) ⇒ one of {⊥, A(z), pair of A-atoms below z}.
  - SAT means some high Y has Y ≤ ⋁_{z∈S} F(z, Y): every e ≱ Y misses some F(z, Y) with s(z). One-directional
    encodings are sound because a subset of S gives a smaller join.
  - Mutant flag `T1` (S = Z ∩ ↓t_1).
  - Every SAT model is replayed from the definitions (world.W, closure_census.first_low); a mismatch asserts.
- `orbit_probe.py` (repository, unchanged): `nofix 0 E1` (W0), `Row1 E1`, `Stair E1`, `LastEither E1`, `Meet2 E1`.
  Branch read off the `model:` lines.

Free analyses (from the definitions, no SAT):
- `pairtrap.py`: PairTrap, AboveD, N1Cert, and the footprint of the relaxed N = 1 NoFix models.
- `absorb_census.py`, `topland_census.py`, `closure_census.py`, `restrict_census.py`.
- `save_cex.py`, which writes `cex/`.

## 9. Report lines

```
CertAtom at N = 1 (LEAD, theorem) | orbit_probe nofix 0 E1 (exact; W0) | SAT = W0 model at N = 1 with no mu-fixed atom
  run 1: tall 13 4 1 8, tall 14 4 2 20 (maxn 40), tall 10 6 1 8 (maxn 45), tall 10 7 1 5 (maxn 50)
  room reached: H 13/14, M 6/7, |L| 33-49, width 6-13 | anatomy: none (Lean proof)
  candidate SAT 0/8 | mutant Row1 E1 (refuted relative, bank s292_row1_h8) SAT 8/8 (branch a 7, atom 1)
  footprint replay of the 8 mutant models: 7 violate Tb at q0 = m ^ d at a (d,m)-boundary point, 1 the exit-case Tb
  bank replay (free): 96/96 stored N = 1 W0 models have a fixed atom; AboveD 116/116 rows
      -> theorem (Lean, scratch); search agrees (second encoding of the statement's meaning)
TopLand_S, branch a, N >= 2 (P2 transfer) | topland_probe Ba Nge2 (exact) | SAT = W0 model whose joint colour row is stuck
  run 3: closure 5 11 4 30 (30), tall 8 4 1 12 (12), tall 10 4 2 20 maxn 40 (17), tall 12 4 1 8 maxn 40 (4)
  candidate SAT 48/63 (H 5-12, N 2-9) | mutant T1 51/63 | branch-atom twin 59/63 | calibration on 15 stored lattices 15/15
      -> REFUTED (smallest |L| 14, H 5, width 5, N 2, branch a; run3/cand_closure_5_11_4_30.json)
StairTb at N = 1 (P3) | orbit_probe nofix 0 Stair E1 (exact; the worker's encoding) | SAT = Stair model, N = 1, no mu-fixed atom
  run 2: tall 13 4 1 8, tall 14 4 2 20 (maxn 40), tall 10 6 1 8 (maxn 45), tall 10 7 1 5 (maxn 50): 8 lattices,
     H 10/13/14, M 6/7, |L| 33-49
  candidate SAT 0/8 | mutant LastEither E1 (refuted relative, bank s292_lasteither_h10) SAT 7/8 (branch a 2, atom 5)
  branch a (A1): mutant models 2 (H 13) | candidate failures 0 -> provisional; branch atom: theorem
  footprint replay of the 7 mutant models: all 7 violate Tb at q0 = m ^ d at a (d,m)-boundary point
TwoRowTb at N = 1 (P3) | orbit_probe nofix 0 Meet2 E1 (exact; the worker's encoding) | SAT = W0^2 model, N = 1, no mu-fixed atom
  run 4: run 1's four corpora + tall 12 4 1 8, tall 11 5 1 8 (maxn 45): 17 lattices, H 10-14, M 4-7, |L| 27-49
  candidate SAT 0/17 | mutant Row1 E1 SAT 17/17 (run 1: 8, run 4: 9; branch a 12, atom 5)
  branch a (A1): mutant models 12 (H 10-14, M 4-7) | candidate failures 0 -> provisional, one step above brief293's
     H <= 12 and M 4 at exact N = 1; branch atom: theorem
  footprint replay of run 4's 9 mutant models: all 9 violate Tb at q0 = m ^ d at a (d,m)-boundary point
```

## 10. Runs (budget 5 exact runs, ≤ 1500 s each, ≤ 2 in parallel; 4 used)

| run | job (cwd `runK/`, script `runK.sh`) | wall |
|---|---|---|
| 1 | LEAD: `orbit_probe.py nofix 0 E1` (W0) and mutant `nofix 0 Row1 E1` on tall 13 4 1 8 / tall 14 4 2 20 (maxn 40), tall 10 6 1 8 (maxn 45), tall 10 7 1 5 (maxn 50) | 125 s |
| 2 | P3: `nofix 0 Stair E1` and mutant `nofix 0 LastEither E1`, same four corpora | 1010 s |
| 3 | P2: `topland_probe.py`, candidate Ba Nge2, mutants T1 Ba Nge2 and Bb Nge2, calibration on `cex/TopLand_S.json`; closure 5 11 4 30, tall 8 4 1 12, tall 10 4 2 20, tall 12 4 1 8 (maxn 40) | 31 s |
| 4 | P3: `nofix 0 Meet2 E1` on run 1's four corpora + tall 12 4 1 8, tall 11 5 1 8 (maxn 45); mutant Row1 E1 on the last two | 883 s |

Runs 1 and 2 ran in parallel, then 2 and 3, then 2 and 4 (never more than two jobs). One run (the fifth) is unused and
returned. Free analyses (bank replays, censuses, footprint replays) are outside the budget: `pairtrap_out.txt`,
`absorb_census_out.txt`, `topland_census_out.txt`, `topland_split_out.txt`, `closure_census_out.txt`,
`restrict_census_out.txt`, `bounded_census_out.txt`, `save_cex_out.txt`, `run1/footprint_replay_out.txt`,
`footprint_runs24_out.txt`.

## 11. Pushes owed

- **Formalization in the repository.** Copy `PairTrap.lean` into `lean/Mordor/` (it imports `Mordor.StairB1`), build,
  and run `#print axioms` on the five theorems. In the briefer's copy they compiled with
  `[propext, Classical.choice, Quot.sound]`.
- **Second encoding of `topland_probe.py`'s refutation.** Replay `run3/cand_closure_5_11_4_30.json` with an
  independent checker; the briefer's replay is `closure_census.first_low` on `world.W`.
- **P3.** A second encoding of runs 2/4. Stair E1 on more lattices: only 2 A1 mutant models so far, all at H 13. Then exact N = 1 at |L| > 50.
- **P2/P4.** JointStuck needs a relaxation run: Stair ∧ NoFix ∧ 𝒜 unbounded (worker's tester plus a 𝒜 clause).

## 12. Already failed: do not repeat

All of frontier §4, plus this brief's refutations:
- **AbsorbExists** (some x ∈ Z has 𝒜 ∩ ↓λ(x) ⊆ ↓x): 14 stored W0 models; smallest |L| 9, H 4, N 2 (`cex/AbsorbExists.json`).
- **TopLand_X / TopLand_t1 / TopLand_S**: §5.2, stored plus run 3.
- **ClosureLand** (⊥-seeded accumulation): 7 stored W0 models; smallest |L| 30, H 8, N 3. It is ⊥-anchored, as the
  failure signature predicts.
- **Restriction transfer** F ⊓ t_j on ↓t_j: Tb fails (58 stored models).
- **"Some closed S exists"** / "some atom's seeded closure closes": restatements of CertAtom.
- ConnectorClose for the pairs (q₀, d), (q₀, m) as a route to A1: superseded (A1 is closed without it).

## 13. Hard constraints and design rules (updated)

- The **colour bound** is the whole of N = 1: φ(Hi) ⊆ ↓t_1, and t_1 ∈ Z exactly when N = 1.
- A proof at N ≥ 2 must handle a stuck joint row. Every landing row x (any x ∈ L) gains an atom of 𝒜 below λ(x) not
  below x (TopRow, contrapositive).
- Tb at the height-2 rows is used only through `land_not_le` (consistent with §7 on file).
- Tb at atom rows is used at **three-row pair columns** (meets of the descents of two rows above the atom). W0² and
  Stair lack these.

## 14. Formalization order (no `sorry`, no new axioms)

1. `pairStair`.
2. `certAtom_of_topRow`.
3. `certAtom_of_boundedAtoms`, `certAtom_of_N1_all`, `certAtom_N1`.

All of them are in `PairTrap.lean`. Optional:
- a virtual-row `pairStair` (replace `F x` by any monotone g with F q ≤ g; the proof is unchanged);
- a `domCoLand` analogue, then TopLand_S ⟹ CertAtom in Lean.

## 15. Expected report

One verdict each:
- **LEAD**: `proves` (N = 1 / A1).
- **P2**: `conditional lemma` (TopRow) plus `refuted` (TopLand), with ladder update CertAtom ⟸ BoundedAtoms.
- **P3**: `provisional` (StairTb and TwoRowTb at A1; owed: a second encoding and more A1 mutant models under Stair).
- **P4**: `needs direct proof`.

## 16. Frontier corrections

1. **§2 ladder, open-target bullet and StairTb bullet** ("Open at N = 1: A1 = h(d) = 2 with ≥ 2 atoms below d"):
   **closed.** CertAtom holds at N = 1 in every branch (`certAtom_N1`, `certAtom_of_N1_all`; briefer's scratch
   `PairTrap.lean`, standard axioms; the worker adds it to `lean/Mordor/`). §3 already said "Open: CertAtom off
   N = 1", which contradicted §2; the two are now consistent.
2. **§2 "A1 anatomy (§294) … So A1 is ConnectorClose for these two pairs"**: a misplaced rung, located and stronger
   than needed. The pair (d, λ(d)) with value row λ(d) ⊓ d closes A1 with no connector (§2.1, §4.2). Remove it as an
   open step.
3. **§2 "at N = 1: CertAtom ⟺ row d exits"**: now unconditional. At N = 1 every row of Z above d exits, with a
   dominated exit atom (AboveD, from `certAtom_of_topRow`).
4. **§2 ladder, add:**
   - `pairStair` [P];
   - CertAtom ⟸ TopRow [P `certAtom_of_topRow`];
   - CertAtom ⟸ BoundedAtoms [P `certAtom_of_boundedAtoms`]: 𝒜 has an upper bound in Z. BoundedAtoms ⟸ N = 1, and
     BoundedAtoms ⟸ GreatestZ;
   - PairTrap [paper corollary of `pairStair`].

   Mark `certAtom_of_N1`, `certAtom_of_N1_thin` and `fixed_of_uniformFibre` (at N = 1) as subsumed.
5. **§2 StairTb / TwoRowTb**: the N = 1 theorem does **not** reach them. Its proof uses Tb at m ⊓ d at meets of
   desc(d) and desc(m), which are not W0² or Stair columns. Their A1 status is per runs 2 and 4 (§10):
   provisional, 0/8 (Stair) and 0/17 (Meet2) at exact N = 1, H 13–14, M 6–7, with mutants failing (LastEither 7/8, Row1 17/17).
6. **§2 decisive step ConnectorClose**: obsolete at N = 1. At N ≥ 2 replace it by JointStuck (§5.3). Any
   counterexample has N ≥ 2, |𝒜| ≥ 2, 𝒜 unbounded in Z, and every joint colour row stuck at a high joint fixed point.
7. **brief293 hard constraint "every proof must handle connectors"** (carried in §2/§7): false at N = 1. Replace it
   by "a proof at N ≥ 2 must handle a stuck joint colour row".
8. **§4 refuted routes, add:**
   - AbsorbExists: 14 stored W0; |L| 9, H 4, N 2;
   - TopLand_X: 17 stored; |L| 15, H 5, N 2;
   - TopLand_t1: 34 stored, and branch a by run 3;
   - TopLand_S: 16 stored, and branch a by run 3; |L| 14, H 5, width 5, N 2;
   - ClosureLand: 7 stored; |L| 30, H 8, N 3;
   - Restriction transfer F ⊓ t_j: 58 stored.

   Files are in `cex/` and `run3/` of this brief.
9. **§6 room vector, add:** |𝒜| (atoms of Z in φ(L)) and "𝒜 bounded in Z" as anatomy coordinates. All 39 stored W0
   models with 𝒜 unbounded have N ≥ 2; 20 have |𝒜| = 2; 1 is in branch a. brief293's "number of atoms in φ(Hi)"
   should be read as |𝒜|.
10. **§7 design rules, add:**
    - Tb at atom rows is used at **three-row pair columns** (meets of the descents of two rows of Z above the atom).
    - The colour bound φ(L) ⊆ ↓t_1 is the whole content of N = 1.
    - Rows outside Z are free (`w0_of_T`), and `exitFixed_of_dom` holds for rows outside Z, so a "virtual" landing
      row above the colours suffices.
11. **§8 set-aside, the anchor**: add ClosureLand, a ⊥-seeded accumulating closure, refuted on Orbit3 models. Even
    accumulation does not rescue a ⊥-anchored walk.
12. **§1 definitions, add 𝒜** := {atoms c ∈ Z : c = φ(w) for some w} and t_1 = φ(⊤). State that `exitFixed_of_dom`
    takes an arbitrary row x.
13. **§3 buckets**:
    - Established (scratch Lean, to be audited and copied): `pairStair`, `certAtom_of_N1_all`,
      `certAtom_of_topRow`, `certAtom_N1`, `certAtom_of_boundedAtoms`.
    - Paper: PairTrap, AboveD, TopRow-S (the virtual-row form).
    - Unverified (one encoding): run 3's refutation of TopLand_S in branch a (`topland_probe.py`; the models replay
      from the definitions).
14. **§9 vacuity map**:
    - W0 ∧ N = 1 ∧ NoFix has no model (theorem; run 1: 0/8 at H 13–14, M 6–7).
    - W0 ∧ ¬TopLand_S, the hypothesis world of JointStuck, has models in both branches at N ≥ 2 (run 3).
    - Every CertAtom counterexample lies in that world.
15. **§10 speeds**:
    - `orbit_probe.py nofix 0 E1` and `Row1 E1` at |L| 33–49 finish in seconds per lattice (run 1, all 16 jobs in
      about 110 s).
    - `Stair E1` takes minutes per lattice at H 13–14 (run 2).
    - `topland_probe.py` takes under 1 s per lattice at |L| ≤ 40.

