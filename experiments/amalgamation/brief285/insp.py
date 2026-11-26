import sys, json
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation'); sys.path.insert(0, '/home/user/mordor/experiments/separation')
import bank
from rstages import a_of
sys.path.insert(0, '.'); import bankx
for fn in sys.argv[1:]:
    mf = json.load(open(fn)); m = bank.M(mf['sets'], mf['F'])
    print(fn, bankx.diag(m), 'w0', m.w0)
    for q in m.atoms:
        print('  atom', q, 'good', m.good(q), 'fixed', m.fixed(q), 'lam', m.lam(q), 'c', m.c(q), 'a', a_of(m.L, m.F, q), 'below M2', [x for x in m.M2 if m.le[q][x]], 'F(q,lam)', m.F[q][m.lam(q)])
