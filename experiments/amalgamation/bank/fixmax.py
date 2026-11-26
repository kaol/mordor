def hyp(m): return m.branch != 'g'
def holds(m): return all(any(m.le[q][x] for x in m.M2) for q in m.atoms if m.fixed(q))
