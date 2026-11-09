# Intervals and envelopes (round 26, §34.3z¹²⁴)

- `envelope_falsify.py`: z3 on every lattice with ≤ 5 elements and every cut. (A1/A2) cellwise witness preservation of
  the anchor envelope E(x, y) = ⋁_{h ≤ x} ⋀_{c ≥ y} F(h, c) (brief anchors / arbitrary finite anchors);
  (B) invariance of a crossing interval under F given witness-free inner cross cells. Output
  `out_envelope_falsify.txt`: (A1), (A2) fail first on C4, (B) first on B2.
- `selection_falsify.py SEED N`: the safe-selection lemma of §34.3z¹²⁵ (nonempty trace windows ⇒ a monotone
  witness-free selection with values in the open interval (w, v)); random instances on closure-system lattices and
  the C4 / B2 regressions. Output `out_selection_falsify.txt`; minimal counterexamples (|L| = 6)
  `selection_counterexample_s2.json`, `_s5.json`.
