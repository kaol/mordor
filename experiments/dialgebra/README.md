# Round 24: the dialgebraic layer in the thin model

Scripts for `docs/rounds/24-v3.5.md` (§32). They import `gpu/lattices.py`, `gpu/engine.py` and `gpu/reference.py` through a relative path.
They need numpy and torch (CPU is fine), and z3 for `orbit_lax.py`. Run from this directory with `python3 <script>.py`.

| script | section | what it checks |
|---|---|---|
| `lambek_zone.py` | §32.2–32.3 | Lambek census of every (f, g) pair on C3, C4, M3, N5, B2; transposition μ^{f,g} = μ(g*∘f); failure-zone predictor δ₀ iso ⟺ f(A₀) ∈ Im g |
| `duality.py` | §32.3–32.4 | dual predictor δ₁ iso ⟺ g(A₁) ∈ Im f (f join-preserving); D5 via an anti-automorphism on every pair |
| `naive_ab.py` | §32.5 | negative: dialgebras of (a, b) / (b, a) do not encode m = n |
| `cut_transpose.py` | §32.6.1–2 | principal cuts ⟺ κ-prefixed points; μκ = ⊤; the lax square on arbitrary down-sets |
| `orbit_lax.py` | §32.6.3 | z3: F with ⋁R_k ≠ r_k (orbit not tight), top-closedness, delay-d simulation; witnesses re-checked by `gpu/reference.py` |
