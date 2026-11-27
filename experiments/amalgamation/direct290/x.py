import sys, json, collections; sys.path.insert(0, '.'); import bank
def X(m):   # atom q <= m in M2 with lam(q) = m  =>  lam(m) = m or m exits
    return all(m.lam(mm) == mm or m.exits(mm) for q in m.atoms for mm in [m.lam(q)] if mm in m.M2 and m.le[q][mm])
def S1(m): return any(m.lam(q) in m.M2 and m.le[q][m.lam(q)] for q in m.atoms)
def noexit(m): return not any(m.exits(x) for x in m.Z)
C = collections.Counter()
for f in sys.argv[1:]:
    for d in json.load(open(f)):
        m = bank.M(d['sets'], d['F']); C[('X', X(m))] += 1; C[('S1|noexit', S1(m) if noexit(m) else 'n/a')] += 1
print('W0flat NoFix samples', dict(C)); C = collections.Counter()
for e in json.load(open('bank/index.json')):
    for d in bank.models(e):
        m = bank.M(d['sets'], d['F'])
        if m.w0: C[('X', X(m))] += 1
print('W0 bank', dict(C))
