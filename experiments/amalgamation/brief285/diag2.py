import sys, json, os
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation'); sys.path.insert(0, '/home/user/mordor/experiments/separation')
import bank
from rstages import a_of
idx = json.load(open(os.path.join(bank.BANK, 'index.json')))
for e in idx:
    for k, mf in enumerate(bank.models(e)):
        m = bank.M(mf['sets'], mf['F'])
        if not m.w0: continue
        h = m.h; le = m.le; F = m.F; bot = m.bot
        A = lambda y: a_of(m.L, F, y)
        fx = [q for q in m.atoms if m.fixed(q)]
        print(f"{e['file']}#{k} br={m.branch} N={m.N} d={m.d} tb={m.tb} fixed={fx} good={[q for q in m.atoms if m.good(q)]}")
        for x in m.Z:
            if x == bot: continue
            print(f"   x={x}(h{h[x]}) desc={m.desc(x)} lam={m.lam(x)} a={A(x)}(h{h[A(x)]}) mu={m.mu(x)} atoms<={[q for q in m.atoms if le[q][x]]}")
        P = sorted({m.lam(x) for x in m.Z if m.exits(x)})
        for p in P:
            col = [bot]; 
            while True:
                u = F[col[-1]][p]
                if u in col: break
                col.append(u)
            print(f"   exit landing p={p}: c_p={F[bot][p]} column ascent {col} rows landing here {[x for x in m.Z if m.lam(x)==p]}")
