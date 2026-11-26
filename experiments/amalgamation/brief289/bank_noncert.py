"""Free bank replay: for every exiting row x of Z whose exit atom c = F(bot, lambda(x)) is NOT below x (a non-certifying
exit), print x, h(x), p = lambda(x), c, whether p >= x, lambda(c), mu-orbit of c and whether it reaches a fixed atom."""
import sys, os, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'amalg'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'separation'))
import bank
idx = json.load(open(os.path.join(bank.BANK, 'index.json')))
tot = 0; reach = 0
for e in idx:
    for k, mf in enumerate(bank.models(e)):
        m = bank.M(mf['sets'], mf['F'])
        if not m.w0: continue
        for x in m.Z:
            if not m.exits(x): continue
            c = m.c(x); p = m.lam(x)
            if m.le[c][x]: continue
            orb = [c]
            while m.mu(orb[-1]) not in orb: orb.append(m.mu(orb[-1]))
            fx = m.fixed(orb[-1]); tot += 1; reach += fx
            print(f"{e['file']}#{k} br={m.branch} x={x}(h{m.h[x]}) p={p} p>=x:{m.le[x][p]} c={c} lam(c)={m.lam(c)} c-exits:{m.exits(c)} orbit(c)={orb} ends-fixed:{fx}")
print('non-certifying exits', tot, 'whose exit atom orbit reaches a fixed atom', reach)
