"""Free bank replay: mu-cycles on Z in every W0+n1 banked model; for each cycle, its elements, heights, and which steps
are exits (lambda not in Z).  Also: exit columns p (landings outside Z), their exit atom c = F(bot, p), the rows landing
there, and whether some row >= c lands there (= c fixed)."""
import sys, os, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'amalg'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'separation'))
import bank
idx = json.load(open(os.path.join(bank.BANK, 'index.json')))
for e in idx:
    for k, mf in enumerate(bank.models(e)):
        m = bank.M(mf['sets'], mf['F'])
        if not m.w0: continue
        cyc = set()
        for x in m.Z:
            seen = []
            y = x
            while y not in seen: seen.append(y); y = m.mu(y)
            c = tuple(seen[seen.index(y):]); r = c.index(min(c)); cyc.add(c[r:] + c[:r])
        cs = [[(x, m.h[x], 'X' if m.exits(x) else '-') for x in c] for c in sorted(cyc)]
        cols = {}
        for x in m.Z:
            if m.exits(x): cols.setdefault(m.lam(x), []).append(x)
        colinfo = [(p, m.F[m.bot][p], rows, any(m.le[m.F[m.bot][p]][x] for x in rows)) for p, rows in cols.items()]
        print(f"{e['file']}#{k} br={m.branch} cycles={cs} exitcols={colinfo}")
