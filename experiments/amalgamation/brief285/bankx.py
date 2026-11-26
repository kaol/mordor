"""Briefer run 15: bank replay driver (no search). Imports bank.M / bank.models from the repo read-only and evaluates
named predicates on every banked model of W0 + n1 (off g where the hypothesis says so). FAIL = statement false on the model.
  python3 bankx.py NAME [NAME ...]   |  python3 bankx.py diag   (prints the top-layer anatomy of every off-g model)"""
import sys, json, os
sys.path.insert(0, '/home/user/mordor/experiments/amalgamation'); sys.path.insert(0, '/home/user/mordor/experiments/separation')
import bank
from rstages import a_of
def A(m, y): return a_of(m.L, m.F, y)
def below_M2(m, q): return any(m.le[q][x] for x in m.M2)
def offg(m): return m.branch != 'g'
def ownp(m, q):   # height-2 p on row q's descent with q <= F(q,p)
    return [p for p in m.desc(q) if m.h[p] == 2 and m.le[q][m.F[q][p]]]
T = {}
# sanity of paper lemma (F1): every good atom q exits; every Z-row above q lands at lam(q) and exits to c(q)
T['GoodExitUp'] = (lambda m: True, lambda m: all(m.exits(q) and all(m.lam(x) == m.lam(q) and m.c(x) == m.c(q) for x in m.Z if m.le[q][x]) for q in m.atoms if m.good(q)))
# non-fixed good atom q: F(q, lam q) = lam q = a(q)
T['NonFixGoodA'] = (lambda m: True, lambda m: all(m.F[q][m.lam(q)] == m.lam(q) == A(m, q) for q in m.atoms if m.good(q) and not m.fixed(q)))
# ladder audit: off g, every good atom lies below M2  (then NMGood <=> GoodAtom1 off g)
T['GoodNonMax'] = (offg, lambda m: all(below_M2(m, q) for q in m.atoms if m.good(q)))
# off g, every mu-fixed atom lies below M2 (then TopCert <=> CertAtom off g)
T['FixNonMax'] = (offg, lambda m: all(below_M2(m, q) for q in m.atoms if m.fixed(q)))
# on g: is d mu-fixed? is d maximal?
T['gDfix'] = (lambda m: m.branch == 'g', lambda m: m.fixed(m.d))
def diag(m):
    h = m.h; le = m.le; out = [f'branch {m.branch} N={m.N} |L|={m.n} H={m.L.height} d={m.d}(h{h[m.d]}) atoms={m.atoms} M2={m.M2}']
    for x in m.M2 + m.atoms:
        below = [q for q in m.atoms if le[q][x]]
        out.append(f'   row {x}(h{h[x]}) atoms<= {below} lam={m.lam(x)}(h{h[m.lam(x)]}) idx={m.lidx(x)} exits={m.exits(x)} c={m.c(x)} '
                   f'{"CERT" if m.exits(x) and le[m.c(x)][x] else ""} good={m.good(x) if h[x]==1 else "-"} fixed={m.fixed(x) if h[x]==1 else "-"} own={ownp(m,x) if h[x]==1 else "-"}')
    return '\n'.join(out)
if __name__ == '__main__':
    idx = json.load(open(os.path.join(bank.BANK, 'index.json')))
    if sys.argv[1] == 'diag':
        for e in idx:
            for k, mf in enumerate(bank.models(e)):
                m = bank.M(mf['sets'], mf['F'])
                if m.w0 and (len(sys.argv) < 3 or sys.argv[2] in e['file']): print(e['file'], k, diag(m))
        sys.exit()
    names = sys.argv[1:]
    if names[0] == '--file':
        ns = {}; exec(open(names[1]).read(), ns); T.update(ns['TESTS']); names = list(ns['TESTS'])
    for name in names:
        hyp, st = T[name]; tally = {'pass': 0, 'FAIL': 0, 'outside hypothesis': 0, 'not W0+n1': 0}
        print(f'bank replay {name} | every banked model of W0 + n1 | FAIL = statement false on that model')
        for e in idx:
            for k, mf in enumerate(bank.models(e)):
                m = bank.M(mf['sets'], mf['F'])
                if not m.w0: tally['not W0+n1'] += 1; continue
                if not hyp(m): tally['outside hypothesis'] += 1; continue
                ok = st(m); tally['pass' if ok else 'FAIL'] += 1
                if not ok: print(f"  FAIL on {e['file']}#{k} (|L| = {m.n}, H = {m.L.height}, branch {m.branch}, N = {m.N})")
        print(f'  {name}: {tally}')
