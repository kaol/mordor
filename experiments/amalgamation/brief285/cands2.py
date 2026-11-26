def _fixed(m): return [q for q in m.atoms if m.fixed(q)]
def _bm2(m, q): return any(m.le[q][x] for x in m.M2)
TESTS = {
  'FixMax on branch g (sharpness side)': (lambda m: m.branch == 'g', lambda m: all(_bm2(m, q) for q in _fixed(m))),
  'AtMost1Fix (at most one mu-fixed atom)': (lambda m: True, lambda m: len(_fixed(m)) <= 1),
  'FixIff (fixed(q) <=> q <= F(bot, lam q)) for atoms of Z': (lambda m: True, lambda m: all(m.fixed(q) == m.le[q][m.F[m.bot][m.lam(q)]] for q in m.atoms)),
  'NonFixGoodUpper (good non-fixed atom q: F(q, lam q) = lam q)': (lambda m: True, lambda m: all(m.F[q][m.lam(q)] == m.lam(q) for q in m.atoms if m.good(q) and not m.fixed(q))),
  'BotBelowFix (fixed q, landing index i: t_(i+1) in {bot, q}; = q iff q = d)': (lambda m: True, lambda m: all((m.tb[m.lidx(q)+1] if m.lidx(q)+1 < len(m.tb) else m.bot) in (m.bot, q) for q in _fixed(m))),
}
