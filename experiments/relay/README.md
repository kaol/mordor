# Relay partial models (round 26, §34.3z¹⁴⁶)

`relay_probe.py (terminal | seed) [forest] [nearcell] [global | interval | two | updown | join] (sweep P NMAX |
closure K M SEED COUNT)`: SAT over F, D, s, a, b, u on a fixed lattice with the relay of Lean `RelayDescent.IsRelay`, a
chosen end case of `relay_meet_update`, and witness-freeness only on the chosen columns. Output
`out_relay_probe.txt`; smallest terminal models `terminal_local_min7.json` (columns ≤ u) and
`terminal_forest_join_min13.json` (D a star forest, columns ≤ u ⊔ F(a, u)).

§34.3z¹⁴⁷: options `orbit=K` (u is the K-th value of the F(⊥, ·)-orbit of ⊤, witness-free along it) and `rows=R`
(witness-freeness along the first R values of the ⊤-orbits of F(s, ·), F(a, ·), F(b, ·)). Output
`out_relay_orbit.txt`; models `orbit_terminal_min27.json`, `orbit1_rows_min25.json`.
