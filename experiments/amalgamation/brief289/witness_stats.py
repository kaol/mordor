"""Free: for every stored model (run*/ JSON) lying in W0b with no mu-fixed atom, list the GoodTop witnesses (m in M2 with
lambda(m) = m) and whether each stalls (a(m) = m), is a diagonal post-fixed point (m <= F(m, m)), equals lambda(bot)."""
import sys, os, json, glob, hashlib
sys.path.insert(0, 'amalg'); sys.path.insert(0, 'separation')
import bank
from rstages import a_of
exec(open('replay_lead.py').read().split("files = ")[0])
seen = set(); tot = st = lb = 0
for fn in sorted(glob.glob('run*/*.json')):
    mf = json.load(open(fn)); mf = mf[0] if isinstance(mf, list) else mf
    key = hashlib.md5(json.dumps([mf['sets'], mf['F']]).encode()).hexdigest()
    m = bank.M(mf['sets'], mf['F'])
    if m.d is None or not w0b(m) or any(m.fixed(q) for q in m.atoms): continue
    dup = key in seen; seen.add(key)
    wit = [x for x in m.M2 if m.lam(x) == x]
    s_ = [a_of(m.L, m.F, x) == x for x in wit]; l_ = [x == m.lam(m.bot) for x in wit]
    if not dup: tot += 1; st += any(s_); lb += any(l_)
    print(fn, '(duplicate)' if dup else '', 'branch', m.branch, 'witnesses', wit, 'stall', s_, 'diag', [m.le[x][m.F[x][x]] for x in wit], '=lambda(bot)', l_)
print(f'distinct W0b NoFix models {tot}; witness stalls in {st}; witness = lambda(bot) in {lb}')
