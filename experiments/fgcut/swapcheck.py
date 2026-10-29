"""Swap obstruction to completion transfer.  P: ⊥ < d < p (D = {⊥, d, p}); columns b1, b2 incomparable, with
b1, b2 < s1, s2 < ⊤ (bowtie), so b1 ⊔ b2 is missing and the MacNeille completion adds w = b1 ⊔ b2 (s1 ⊓ s2).
F(x, b1) = b2, F(x, b2) = b1 for x ∈ D, F(x, s_i) = s_{3-i}, F(x, ⊤) = s1 — monotone, and no witness at any column
cell of the swap.  Check both extensions at the new element w."""
import itertools
E = ['bot', 'd', 'p', 'b1', 'b2', 'w', 's1', 's2', 'top']
cov = [('bot','d'),('d','p'),('p','b1'),('p','b2'),('b1','w'),('b2','w'),('w','s1'),('w','s2'),('s1','top'),('s2','top')]
le = {(x, y): x == y for x in E for y in E}
for a, b in cov: le[(a, b)] = True
for k in E:
    for i in E:
        for j in E:
            if le[(i, k)] and le[(k, j)]: le[(i, j)] = True
P = [e for e in E if e != 'w']; D = ['bot', 'd', 'p']; C = ['b1', 'b2', 's1', 's2', 'top']
val = {'b1': 'b2', 'b2': 'b1', 's1': 's2', 's2': 's1', 'top': 'top'}   # ⊤ exempt: any finite closed system has a witness somewhere (CLL)
F = {(x, y): val[y] for x in D for y in C}
def join(S):
    ub = [u for u in E if all(le[(s, u)] for s in S)]; return next(u for u in ub if all(le[(u, v)] for v in ub))
def meet(S):
    lb = [u for u in E if all(le[(u, s)] for s in S)]; return next(u for u in lb if all(le[(v, u)] for v in lb))
mono = all(le[(F[(x, y)], F[(x2, y2)])] for (x, y) in F for (x2, y2) in F if le[(x, x2)] and le[(y, y2)])
print('F monotone on D x C:', mono)
print('original column witnesses below top:', [(x, y) for (x, y) in F if y != 'top' and le[(y, F[(x, y)])]])
for x in D:
    lo = join([F[(a, b)] for a in D for b in C if le[(a, x)] and le[(b, 'w')]])
    hi = meet([F[(a, b)] for a in D for b in C if le[(x, a)] and le[(b, 'w')] is False and le[('w', b)]])
    print(f"x={x}: lower ext F^(x,w) = {lo}  W2 {'FAILS' if le[('w', lo)] else 'ok'};  upper ext F~(x,w) = {hi}  W2 {'FAILS' if le[('w', hi)] else 'ok'}")
