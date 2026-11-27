"""Free check: stored models in W0^2 but not W0 -- is their descent-maximal form F# in W0 (repairable) or not
(irreparable: the only slice where TwoRowTb says more than CertAtom)?  Also prints where each came from."""
import sys, collections
sys.path.insert(0, '.'); from corners import w0sq; from dmaxviol import sharp
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation/brief291'); from world import W, load_all, dedup
C = collections.Counter()
for name, w in dedup(load_all()):
    if not w.base(): continue
    if any(w.lam(x) is None for x in w.Z): continue
    if not w0sq(w) or (w.w0flat() and w.w0()): continue
    G, _ = sharp(w); v = W(w.sets, G); rep = v.mono and v.w0flat() and v.w0()
    d, N = w.dN()
    print(name, 'n', w.n, 'H', w.h[w.top], 'N', N, 'branch', 'a' if w.h[d] == 2 else 'atom', 'nofix', w.nofix(), 'F# in W0:', rep)
    C[rep] += 1
print(dict(C))
