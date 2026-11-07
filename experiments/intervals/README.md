# Intervals and envelopes (round 26, §34.3z¹²⁴)

- `envelope_falsify.py`: z3 on every lattice with ≤ 5 elements and every cut. (A1/A2) cellwise witness preservation of
  the anchor envelope E(x, y) = ⋁_{h ≤ x} ⋀_{c ≥ y} F(h, c) (brief anchors / arbitrary finite anchors);
  (B) invariance of a crossing interval under F given witness-free inner cross cells. Output
  `out_envelope_falsify.txt`: (A1), (A2) fail first on C4, (B) first on B2.
