import sys, time
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
from monotone_good_words import *
for nP, nU in [tuple(map(int, a.split("x"))) for a in sys.argv[1:]] or [(2, 2), (3, 2), (2, 3)]:
    t0 = time.time(); out = cegar_all(nP, nU)
    print(f"|P*|={nP} |U*|={nU}, all {len(all_exhaustions(nP, nU))} exhaustions: {out[0]} (iterations {out[1]}, {time.time()-t0:.0f}s)", flush=True)
    if len(out) > 2:
        for c in sorted(out[2], key=lambda c: (len(c[0]), len(c[1]), sorted(c[0]), sorted(c[1]))):
            if out[2][c] or out[3][c]: print('   ', sorted(c[0]), sorted(c[1]), 'SP', sorted(out[2][c]), 'SU', sorted(out[3][c]), flush=True)
