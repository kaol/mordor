# LfpMin itself on the bank (hypothesis NoFix): expected 'outside hypothesis' on every W0 + n1 model (contradiction mode).
def hyp(m): return not any(m.fixed(q) for q in m.atoms)
def holds(m): return False
