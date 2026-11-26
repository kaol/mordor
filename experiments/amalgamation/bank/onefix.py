def holds(m): return sum(1 for q in m.atoms if m.fixed(q)) == 1
