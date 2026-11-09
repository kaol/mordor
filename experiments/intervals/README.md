# Intervals and envelopes (round 26, §34.3z¹²⁴)

- `envelope_falsify.py`: z3 on every lattice with ≤ 5 elements and every cut. (A1/A2) cellwise witness preservation of
  the anchor envelope E(x, y) = ⋁_{h ≤ x} ⋀_{c ≥ y} F(h, c) (brief anchors / arbitrary finite anchors);
  (B) invariance of a crossing interval under F given witness-free inner cross cells. Output
  `out_envelope_falsify.txt`: (A1), (A2) fail first on C4, (B) first on B2.
- `selection_falsify.py SEED N`: the safe-selection lemma of §34.3z¹²⁵ (nonempty trace windows ⇒ a monotone
  witness-free selection with values in the open interval (w, v)); random instances on closure-system lattices and
  the C4 / B2 regressions. Output `out_selection_falsify.txt`; minimal counterexamples (|L| = 6)
  `selection_counterexample_s2.json`, `_s5.json`.
- `veinott_audit.py SEED N`: weak Veinott monotonicity (Kukushkin 2009) of the windows, selectability, general pins
  (Lean `general_pin`, `general_pin_dual`) and iterated pinning. Output `out_veinott_audit.txt`.
  `pinfree_blocked_counterexample.json`: the |L| = 10 instance that the narrow internal-pin pattern misses and the
  general pin catches.
- `antichain_pins.py NMAX`: the M_n crossing interval in which all n rows are blocked and every n − 1 are selectable
  (unbounded pin arity; Lean `atom_family_block` for the infinite version). Output `out_antichain_pins.txt`.
