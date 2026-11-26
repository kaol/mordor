# Candidate predicates for bankx.py --file (Python, from the definitions in bank.M). FAIL = statement false on the model.
def _fixed(m): return [q for q in m.atoms if m.fixed(q)]
def _good(m): return [q for q in m.atoms if m.good(q)]
def _bm2(m, q): return any(m.le[q][x] for x in m.M2)
offg = lambda m: m.branch != 'g'
TESTS = {
  'OneFix (exactly one mu-fixed atom)': (lambda m: True, lambda m: len(_fixed(m)) == 1),
  'OddFix (odd number of mu-fixed atoms)': (lambda m: True, lambda m: len(_fixed(m)) % 2 == 1),
  'M:OneGood (at most one good atom; refuted s282)': (lambda m: True, lambda m: len(_good(m)) <= 1),
  'FixMax (off g: every mu-fixed atom lies below M2)': (offg, lambda m: all(_bm2(m, q) for q in _fixed(m))),
  'M:GoodNonMax (off g: every good atom lies below M2)': (offg, lambda m: all(_bm2(m, q) for q in _good(m))),
  'GoodToFix (every good atom is mu-fixed or exits to a mu-fixed atom)': (lambda m: True, lambda m: all(m.fixed(q) or (m.exits(q) and m.fixed(m.c(q))) for q in _good(m))),
  'M:GoodFix (every good atom is mu-fixed; refuted s282)': (lambda m: True, lambda m: all(m.fixed(q) for q in _good(m))),
  'TopExit (off g: some m in M2 exits with c(m) <= m)': (offg, lambda m: any(m.exits(x) and m.le[m.c(x)][x] for x in m.M2)),
  'M:MaxIdx2 (off g: some max-landing-index m in M2 certifies; refuted s282)': (offg, lambda m: (lambda I: any(m.exits(x) and m.le[m.c(x)][x] for x in m.M2 if I[x] == max(I.values())))({x: m.lidx(x) for x in m.M2})),
  'LandIdxMono (x <= y in Z: i(x) <= i(y), equal index => lam(x) <= lam(y))': (lambda m: True, lambda m: all(m.lidx(x) < m.lidx(y) or (m.lidx(x) == m.lidx(y) and m.le[m.lam(x)][m.lam(y)]) for x in m.Z for y in m.Z if m.le[x][y])),
  'PredStep (exit landing p of x in Z, predecessor s: F(bot,s) in {c_p, p})': (lambda m: True, lambda m: all(m.F[m.bot][m.desc(x)[m.lidx(x)-1]] in (m.c(x), m.lam(x)) for x in m.Z if m.exits(x))),
}
