"""Ω × K, K finite: hubs, co-hubs and infinite intervals (log §34.3w).

`TwoSided.two_sided` needs finitely many hubs (infinite principal filter) and co-hubs (infinite principal ideal), and
`cut_two_sided_capture` leaves only infinite intervals [w, v], ⊥ < w ≤ v < ⊤, that the cut crosses. On truncations
Ω_N × K, an element or interval counts as "infinite" when its size grows from N to N + 1.
Expected: hubs {(⊥, k)}, co-hubs {(⊤, k)}, infinite intervals exactly the strips [(⊥, k), (⊤, k')] with
⊥ < k ≤ k' < ⊤ in K.
"""
import sys
sys.path.insert(0, '../localize')
from boxes import Lat, omega
from products_check import product, chain

def m3(): return Lat(['0', 'a', 'b', 'c', '1'], [('0', x) for x in 'abc'] + [(x, '1') for x in 'abc'])

def stats(L):
    b = [i for i in range(L.n) if all(L.le[i][j] for j in range(L.n))][0]
    t = [i for i in range(L.n) if all(L.le[j][i] for j in range(L.n))][0]
    up = {L.E[g]: sum(L.le[g]) for g in range(L.n)}
    dn = {L.E[g]: sum(L.le[z][g] for z in range(L.n)) for g in range(L.n)}
    iv = {(L.E[w], L.E[v]): sum(1 for z in range(L.n) if L.le[w][z] and L.le[z][v])
          for w in range(L.n) for v in range(L.n) if w != b and v != t and L.le[w][v]}
    return up, dn, iv

def check(name, K, N=3):
    A, B = stats(product(omega(N), K)), stats(product(omega(N + 1), K))
    grow = lambda a, b: sorted((k for k in a if b[k] > a[k]), key=str)
    print(name)
    print('  hubs   :', grow(A[0], B[0]))
    print('  co-hubs:', grow(A[1], B[1]))
    print('  infinite intervals (⊥ < w ≤ v < ⊤):', grow(A[2], B[2]))

if __name__ == '__main__':
    check('Omega x C3', chain(3)); check('Omega x C4', chain(4)); check('Omega x M3', m3())
