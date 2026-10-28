"""Run crossground.py, then deletion-minimize its F-term set (subterm-closed, deepest first) with fixed-term solves, and
print the surviving terms as words, e.g. p1·p1·m123·T = F(p1, F(p1, F(m123, T))).   python3 crossmin.py K H maxterms shape"""
import sys, subprocess, pickle, itertools, os
sys.argv = [sys.argv[0]] + sys.argv[1:]
K, H, CAP, SHAPE = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
CG = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'crossground.py')
src = open(CG).read()
# 1) run search, capture terms
ns = {'__file__': CG, '__name__': 'x'}
exec(compile(src, 'cg', 'exec'), ns)
G0 = ns['G']; rep = ns['rep']; subsets = ns['subsets']
nm = {}
for A in subsets: nm.setdefault(rep[A], 'm' + ''.join(str(i + 1) for i in sorted(A)) if len(A) > 1 else 'p' + str(min(A) + 1))
nm[0] = '0'; nm[1] = 'T'
def tree(i):
    t = G0.terms[i]
    if t is None: return nm[i]
    return (nm[t[0]], tree(t[1]))
Fterms = [tree(i) for i in range(len(G0.terms)) if G0.terms[i] is not None]
# 2) fixed-term solver
def unsat(T):
    src2 = src.replace("G.add_term((rep[frozenset(range(K))], 1), 1)\nt0", "t0")
    ns2 = {'__file__': ns['__file__'], '__name__': 'y'}
    head = src2.split("t0 = time.time(); rnd = 0")[0]
    exec(compile(head, 'cg2', 'exec'), ns2)
    G = ns2['G']; rep2 = ns2['rep']; inv = {}
    for A in subsets: inv.setdefault('m' + ''.join(str(i + 1) for i in sorted(A)) if len(A) > 1 else 'p' + str(min(A) + 1), rep2[A])
    inv['0'] = 0; inv['T'] = 1
    idx = {}
    def add(t):
        if isinstance(t, str): return inv[t]
        if t in idx: return idx[t]
        y = add(t[1]); i = G.add_term((inv[t[0]], y), 1); idx[t] = i; return i
    for t in sorted(T, key=lambda t: str(t).count('(')): add(t)
    return G.solve() is None
def depth(t): return 0 if isinstance(t, str) else 1 + depth(t[1])
def has(u, t): return u == t or (not isinstance(u, str) and has(u[1], t))
T = set(Fterms); assert unsat(T)
for t in sorted(T, key=lambda t: -depth(t)):
    if t not in T: continue
    T2 = {u for u in T if not has(u, t)}
    if unsat(T2): T = T2
def show(t): return t if isinstance(t, str) else f"{t[0]}·{show(t[1])}"
print(f"K={K} H={H} {SHAPE}: {len(Fterms)} -> {len(T)} F-terms")
for t in sorted(T, key=lambda t: (depth(t), show(t))): print(' ', show(t))
