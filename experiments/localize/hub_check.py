"""Check the hypotheses of `Pin.cut_hub` on S∞′ (log §34.3r). Local hypotheses are checked exactly on truncations
S∞′_N; the finiteness hypotheses hI (proper principal ideals) and hJ (filters of elements outside ⊥, d, e, c) are
checked by stability: |↓g| and |↑g| for a fixed g do not change with N (so they are finite in the limit), while
|↑⊥|, |↑d|, |↑e|, |↑c| grow."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from boxes import sinf

def check(N):
    L = sinf(N, True); E, le, n = L.E, L.le, L.n
    I = E.index; bot, top, d, e, c = I('bot'), I('top'), I('d'), I('e'), I('c')
    B = {bot, d, e, c}
    ok = {}
    ok['hcov'] = all(z in (bot, e) or le[d][z] for z in range(n))
    ok['hed'] = not le[e][d]
    ok['hdc'] = le[d][c]; ok['hec'] = le[e][c]
    ok['he_down'] = all(z in (bot, e) for z in range(n) if le[z][e])
    ok['hc_down'] = all(le[z][d] or z in (e, c) for z in range(n) if le[z][c])
    ok['he_up'] = all(z == e or le[c][z] for z in range(n) if le[e][z])
    coat = [w for w in range(n) if le[c][w] and w not in (c, top)]
    ok['hc_up'] = all(z in (w, top) for w in coat for z in range(n) if le[w][z])
    ok['hw_down'] = all(le[z][c] or z == w or all(le[b][d] for b in B if le[b][z])
                        for w in coat for z in range(n) if le[z][w])
    down = {E[g]: sum(le[z][g] for z in range(n)) for g in range(n) if g != top}
    up = {E[g]: sum(le[g][z] for z in range(n)) for g in range(n) if g != bot}
    return ok, down, up

if __name__ == '__main__':
    res = {N: check(N) for N in range(3, 9)}
    print('local hypotheses:', {k: all(res[N][0][k] for N in res) for k in res[3][0]})
    common = set(res[3][1]) & set(res[8][1])
    print('hI stable (|↓g| independent of N):', all(res[3][1][g] == res[8][1][g] for g in common))
    cu = set(res[3][2]) & set(res[8][2])
    grow = sorted((str(g) for g in cu if res[3][2][g] != res[8][2][g]))
    print('elements whose |↑g| grows with N:', grow, '(hJ allows exactly d, e, c besides ⊥)')
