"""Independent brute-force check of a periodic model on the index window [-N, N] (outputs may leave the window)."""
import sys, pickle, itertools
m = pickle.load(open(sys.argv[1], 'rb')); N = int(sys.argv[2]) if len(sys.argv) > 2 else 8
K, T, sK, sT, W, H = m['K'], m['T'], m['sideK'], m['sideT'], m['W'], m['H']
BOT, TOP = 0, len(K) - 1
def cl(d): return max(-W - 1, min(W + 1, d))
def side(e): return sK[e[1]] if e[0] == 'K' else sT[e[2]]
def le(a, b):
    if a == b: return True
    if side(a) == 'C' and side(b) == 'D': return False
    if a[0] == 'K' and b[0] == 'K':
        if a[1] == BOT or b[1] == TOP: return True
        if a[1] == TOP or b[1] == BOT: return False
        return m['KK'][(a[1], b[1])]
    if a[0] == 'K':
        return True if a[1] == BOT else (False if a[1] == TOP else m['KI'][(a[1], b[2])])
    if b[0] == 'K':
        return True if b[1] == TOP else (False if b[1] == BOT else m['IK'][(a[2], b[1])])
    if a[2] == b[2]: return False
    return m['II'][(a[2], b[2], cl(b[1] - a[1]))]
def F(x, y):
    kx = ('K', x[1]) if x[0] == 'K' else ('T', x[2]); ky = ('K', y[1]) if y[0] == 'K' else ('T', y[2])
    c = cl(y[1] - x[1]) if (x[0] == 'I' and y[0] == 'I') else None
    o = m['F'][(kx, ky, c)]
    if o[0] == 'K': return o
    a = x[1] if o[0] == 'x' else y[1]
    return ('I', a + o[1], o[2])
EL = [('K', k) for k in K] + [('I', i, t) for i in range(-N, N + 1) for t in T]
bad = {}
def fail(k, *w): bad.setdefault(k, w)
for a in EL:
    for b in EL:
        if a != b and le(a, b) and le(b, a): fail('antisym', a, b)
        if le(a, b) and side(a) == 'C' and side(b) == 'D': fail('downset', a, b)
        if le(a, b):
            for c in EL:
                if le(b, c) and not le(a, c): fail('trans', a, b, c)
# height: longest chain in window
import functools
order = sorted(EL, key=lambda e: 0)
@functools.lru_cache(None)
def longest(e): return 1 + max([longest(f) for f in EL if f != e and le(e, f)], default=0)
h = max(longest(e) for e in EL)
if h > H + 2: fail('height', h)
Dl = [e for e in EL if side(e) == 'D']; Cl = [e for e in EL if side(e) == 'C']
for x in Dl:
    for y in Cl:
        z = F(x, y)
        if le(z, x): fail('W1', x, y, z)
        if le(y, z): fail('W2', x, y, z)
        for x2 in Dl:
            if le(x, x2) and not le(z, F(x2, y)): fail('monoX', x, x2, y)
        for y2 in Cl:
            if le(y, y2) and not le(z, F(x, y2)): fail('monoY', x, y, y2)
print(sys.argv[1], 'window', N, 'longest chain', h, 'failures:', bad if bad else 'none')
