# Finite separators (round 26, §34.3z¹²⁰)

- `finite_landmarks.py [samples] [seed]`: the extremal-separator refinement (T₀ = {⊥, ⊤}; every bad cross pair gets a
  maximal upper separator; meet-closure) on random closure-system lattices with random monotone F and down-set D;
  stage counts and |T| by height. `climb SEED SECONDS`: hill-climbing on (F, D) maximizing the stage count.
  `width3 SEED POINTS RESTARTS`: the same on height-3 linear spaces of growing width. Output `out_finite_landmarks.txt`.
  Finite lattices always end (separated or stuck), so these runs only measure stage counts; they cannot exhibit a
  witness-free structure.
