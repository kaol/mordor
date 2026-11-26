"""Free bank replay over EVERY banked model (W0+n1 and relaxed worlds). For each model prints world flags and a
set of statements computed from the definitions (bank.M API). No search."""
import sys, os, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'amalg'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'separation'))
import bank
from rstages import a_of
idx = json.load(open(os.path.join(bank.BANK, 'index.json')))
def stats(m):
    L=m.L; h=m.h; F=m.F; bot=m.bot
    fixed=[q for q in m.atoms if m.fixed(q)]
    stall=[q for q in m.atoms if m.le[q][a_of(L,F,q)] and a_of(L,F,q)!=q]
    good=[q for q in m.atoms if m.good(q)]
    nexits=sum(1 for x in m.Z if m.exits(x))
    return dict(fixed=fixed, stall=stall, good=good, exitrows=nexits, Z=len(m.Z))
for e in idx:
    for k, mf in enumerate(bank.models(e)):
        m = bank.M(mf['sets'], mf['F'])
        if m.d is None: print(e['file'], 'no d'); continue
        print(f"{e['file']}#{k} w0={m.w0} n={m.n} H={m.L.height} br={m.branch} {stats(m)}")
