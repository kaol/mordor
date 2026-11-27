import sys, json, glob, os, collections; sys.path.insert(0, '.'); import bank
seen = set(); models = []
for f in glob.glob('**/*.json', recursive=True):
    try: D = json.load(open(f))
    except Exception: continue
    for d in (D if isinstance(D, list) else [D]):
        if not isinstance(d, dict) or 'sets' not in d or 'F' not in d: continue
        key = json.dumps([d['sets'], d['F']])
        if key in seen: continue
        seen.add(key)
        try: m = bank.M(d['sets'], d['F'])
        except Exception: continue
        if m.w0: models.append((f, m))
print('distinct W0 models', len(models))
C = collections.Counter()
for f, m in models:
    L = m.L; F = m.F; h = m.h; le = m.le
    A = sorted({F[m.bot][w] for w in range(m.n) if h[F[m.bot][w]] == 1 and F[m.bot][F[m.bot][w]] == m.bot})
    bounded = any(all(le[a][z] for a in A) for z in m.Z)
    if bounded: continue
    S = [m.bot] + A
    g = lambda y: [y2 for y2 in [m.bot] for _ in [0]][0]
    def g(y):
        v = m.bot
        for z in S: v = L.join[v][F[z][y]]
        return v
    y = m.top; s = []
    while y not in s: s.append(y); y = g(y)
    Y = s[-1]
    fixed = [q for q in m.atoms if m.fixed(q)]
    phY = F[m.bot][Y]
    C[('|A|', len(A))] += 1
    C[('Y high', h[Y] > 2)] += 1
    C[('phi(Y) fixed', phY in fixed)] += 1
    C[('phi(Y) in A', phY in A)] += 1
    C[('fixed below Y', all(le[q][Y] for q in fixed))] += 1
    C[('fixed in A', all(q in A for q in fixed))] += 1
    C[('#fixed', len(fixed))] += 1
    C[('Ytb: some c in A with F(c,Y)<=c', any(le[F[c][Y]][c] for c in A))] += 1
    C[('F(c,Y) high for all c', all(h[F[c][Y]] > 2 for c in A))] += 1
for k in sorted(C, key=str): print(k, C[k])
