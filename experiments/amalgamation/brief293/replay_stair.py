"""Bank/stored-model replay (free, from the definitions) of StairTb and TwoRowTb: every stored model of the repository
(bank/, holding/, brief*/ , direct*/ ...) that lies in the Stair world (resp. W0^2) must have a mu-fixed atom.
FOR ALL stored models m: m in world => some atom of Z is mu-fixed.  Prints failures (= refutations)."""
import sys, collections
sys.path.insert(0, '.'); sys.argv = sys.argv[:1] + ['nofix']
from corners import w0sq
import importlib.util
spec = importlib.util.spec_from_file_location('sp', 'stair_probe.py')
src = open('stair_probe.py').read(); ns = {}
exec(src[src.index('def stair_world'):src.index('def encode')], {'__builtins__': __builtins__}, ns)
stair_world = ns['stair_world']
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import load_all, dedup
C = collections.Counter()
for name, w in dedup(load_all()):
    try:
        if not w.base(): continue
        st = stair_world(w); sq = w0sq(w)
    except Exception: continue
    nf = w.nofix(); d, N = w.dN(); br = 'a' if w.h[d] == 2 else 'atom'
    C[('Stair', st, 'W0sq', sq, 'nofix', nf, br, 'N1' if N == 1 else 'N>=2')] += 1
    if (st or sq) and nf: print('FAILURE', name, 'stair', st, 'w0sq', sq)
for k, v in sorted(C.items(), key=str): print(v, k)
