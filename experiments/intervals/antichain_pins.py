"""Unbounded pin arity in an M_n crossing interval (log §34.3z¹²⁶; brief Part B, §10).

Lattice L_n: ⊥ < a_1..a_n < v < ⊤ and ⊥ < y < ⊤ (y ≰ v); height 3. D = {⊥, a_1..a_n}; I = [⊥, v] (crossing).
Cells: (⊥, y) and (a_i, y) for the rows in R ⊆ {a_1..a_n}. Windows (range reduction to the open interval, safety):
W(a_i, y) = {a_j : j ≠ i}, W(⊥, y) = {a_1..a_n}. Monotone selection: z(⊥, y) ≤ z(a_i, y).
The original values G ≡ v on these cells are monotone and witness-free (y ≰ v).
For each n: is the full family R = all atoms selectable? Is every family missing one atom selectable?
(So the minimal obstruction has n + 1 cells: no certificate of bounded arity exists, and for M_ω none at all.)
  python3 antichain_pins.py NMAX
"""
import sys
from z3 import *

def selectable(n, rows):
    # elements: 0 = ⊥, 1..n = atoms, n+1 = v, n+2 = y, n+3 = ⊤
    le = lambda a, b: a == b or a == 0 or b == n + 3 or (1 <= a <= n and b == n + 1)
    meet = lambda a, b: a if le(a, b) else (b if le(b, a) else 0)
    s = Solver(); z0 = Int('z0'); Z = {i: Int(f'z{i}') for i in rows}
    s.add(Or([z0 == j for j in range(1, n + 1)]))
    for i in rows:
        s.add(Or([Z[i] == j for j in range(1, n + 1) if j != i]))
        s.add(Or([And(z0 == a, Z[i] == b) for a in range(1, n + 1) for b in range(1, n + 1) if le(a, b)]))
    return s.check() == sat

if __name__ == '__main__':
    for n in range(2, int(sys.argv[1]) + 1):
        full = selectable(n, list(range(1, n + 1)))
        drops = [selectable(n, [i for i in range(1, n + 1) if i != k]) for k in range(1, n + 1)]
        print(f"n = {n}: all {n} rows selectable: {full}; every family of {n - 1} rows selectable: {all(drops)}")
