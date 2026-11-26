"""Room coordinates (|L|, H, width = largest antichain, N, branch, |M2|) of stored model JSON files (read-only)."""
import sys, os, json
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'amalg'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'separation'))
import bank
for fn in sys.argv[1:]:
    mf = json.load(open(fn)); mf = mf[0] if isinstance(mf, list) else mf
    m = bank.M(mf['sets'], mf['F'])
    print(f"{fn}: |L|={m.n} H={m.L.height} width={bank.width(m.L)} N={m.N} branch={m.branch} |M2|={len(m.M2)} relax={mf.get('relaxation')} mode={mf.get('mode')}")
