import sys, json, os
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation'); sys.path.insert(0, '/home/user/mordor/experiments/separation')
import bank
from rstages import a_of
from collections import Counter
idx = json.load(open(os.path.join(bank.BANK, 'index.json'))); C = Counter()
for e in idx:
    for k, mf in enumerate(bank.models(e)):
        m = bank.M(mf['sets'], mf['F'])
        if not m.w0: continue
        h = m.h; le = m.le; F = m.F; bot = m.bot
        for x in m.Z:
            if x == bot: continue
            ds = m.desc(x); i = m.lidx(x); p = ds[i]; s = ds[i-1]
            ex = m.exits(x); 
            if ex:
                cp = F[bot][p]; u1 = F[bot][s]
                kind = 'c' if u1 == cp else ('p' if u1 == p else 'other')
                C[(f'h{h[x]}', 'exit', 'F(bot,s)=' + kind, 'cert' if le[cp][x] else 'nocert')] += 1
            else:
                u = F[bot][s]; asc = [bot]
                while True:
                    v = F[asc[-1]][s]
                    if v == asc[-1] or v in asc: break
                    asc.append(v)
                    if v not in m.Z: break
                C[(f'h{h[x]}', 'in', 'escape from ' + ('below x' if le[asc[-2]][x] else 'not below x'))] += 1
for k, v in sorted(C.items()): print(k, v)
