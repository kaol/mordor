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
   RUN24_STATUS.
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
