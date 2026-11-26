"""Free replay of the LEAD (in W0b: NoFix ==> GoodTop) and of its mutant (NoFix ==> OwnZCell) over every banked model
and every model JSON given on the command line.  W0b = a(bot)=bot, ZT, n1, h(top)>=3, Ta at every row of Z, Tb at
every atom row of Z (Tb at height-2 rows dropped).  FAIL = the model lies in W0b, has no mu-fixed atom, and the
conclusion is false."""
import sys, os, json, glob
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'amalg'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'separation'))
import bank
from rstages import a_of
def w0b(m):
    h = m.h; F = m.F; le = m.le; n = m.n
    if a_of(m.L, F, m.bot) != m.bot or h[m.top] < 3: return False
    if not all(h[z] <= 2 for z in m.Z) or not m.M2: return False
    for x in m.Z:
        if x == m.bot: continue
        for y in range(n):
            if h[y] < 3: continue
            if le[y][F[x][y]]: return False
            if h[x] == 1 and le[F[x][y]][x]: return False
    return True
files = [os.path.join(bank.BANK, e['file']) for e in json.load(open(os.path.join(bank.BANK, 'index.json')))] + sys.argv[1:]
T = {'lead': [0, 0, 0], 'mutZ': [0, 0, 0]}
for fn in files:
    ms = json.load(open(fn)); ms = ms if isinstance(ms, list) else [ms]
    for k, mf in enumerate(ms):
        m = bank.M(mf['sets'], mf['F'])
        if m.d is None or not w0b(m): continue
        nofix = not any(m.fixed(q) for q in m.atoms)
        if not nofix:
            for t in T: T[t][0] += 1
            continue
        gt = any(m.lam(x) == x for x in m.M2)
        oz = any(z in m.Z and m.h[z] == 2 and m.le[q][m.F[q][z]] for q in m.atoms for z in m.desc(q))
        for t, ok in (('lead', gt), ('mutZ', oz)):
            T[t][1 if ok else 2] += 1
            if not ok: print(f'  {t} FAIL on {os.path.basename(fn)}#{k} (n={m.n}, H={m.L.height}, branch {m.branch})')
print('replay | world W0b | [hypothesis NoFix false (pass), NoFix and conclusion holds, FAIL]')
for t in T: print(' ', t, T[t])
