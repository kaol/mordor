import sys; sys.path.insert(0, '.'); from world import *
ms = dedup(load_all(sys.argv[1:]))
print('distinct stored models:', len(ms))
cnt = {}
for name, w in ms:
    k = ('W0' if w.w0() else 'W0flat-only') if w.w0flat() else 'other'
    k2 = k + (' NoFix' if k != 'other' and w.nofix() else '') + (' NoExit' if k != 'other' and w.noexit() else '')
    cnt[k2] = cnt.get(k2, 0) + 1
print(cnt)
bad = [(n, w.witnesses()) for n, w in ms if w.w0flat() and w.nofix() and not w.witnesses()]
print('W0flat & NoFix without witness (GoodTop counterexamples):', bad)
