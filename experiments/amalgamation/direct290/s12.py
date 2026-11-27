import sys, json, collections, glob; sys.path.insert(0, '.'); import bank
def chk(m):
    le = m.le
    S1 = any(m.lam(q) in m.M2 and le[q][m.lam(q)] for q in m.atoms)
    bad2 = [(q, m.lam(q)) for q in m.atoms if m.lam(q) in m.M2 and le[q][m.lam(q)] and m.lam(m.lam(q)) != m.lam(q)]
    ex = [x for x in m.Z if m.exits(x)]
    return S1, bad2, ex
C = collections.Counter()
for f in sys.argv[1:]:
    for d in json.load(open(f)):
        m = bank.M(d['sets'], d['F']); S1, bad2, ex = chk(m)
        C[('S1', S1)] += 1; C[('S2', not bad2)] += 1
        if ex: print('exit model', f, m.n, 'exits', ex, 'lam', [m.lam(x) for x in ex], 'branch', m.branch)
print('W0flat NoFix samples:', dict(C))
C = collections.Counter()
for e in json.load(open('bank/index.json')):
    for d in bank.models(e):
        m = bank.M(d['sets'], d['F'])
        if not m.w0: continue
        S1, bad2, ex = chk(m); C[('S1', S1)] += 1; C[('S2', not bad2)] += 1
print('W0 bank:', dict(C))
