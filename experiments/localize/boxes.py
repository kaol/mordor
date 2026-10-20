"""Size-uniformity test of the box criterion (log §34.3p): on truncations L_N of infinite chain-finite families,
classify every box [s, t] and interior corner c. A (box, corner) pair is *growing* if |V| increases with N; it is
*stuck* (for the D-free criterion) if it is growing, has no interior spine point, and fails ⋁V < t or ⋀V > s.
Per stuck pair we also record which side fails, since the D-dependent calculus only needs ⋁V < t when c ∉ D and
⋀V > s when c ∈ D."""
import itertools, sys

class Lat:
    def __init__(self, els, rel):
        self.E = list(els); idx = {e: i for i, e in enumerate(self.E)}; n = len(self.E)
        le = [[i == j for j in range(n)] for i in range(n)]
        for a, b in rel: le[idx[a]][idx[b]] = True
        for k in range(n):
            for i in range(n):
                if le[i][k]:
                    for j in range(n):
                        if le[k][j]: le[i][j] = True
        self.le, self.idx, self.n = le, idx, n
        self.join = [[None] * n for _ in range(n)]; self.meet = [[None] * n for _ in range(n)]
        for i in range(n):
            for j in range(n):
                ub = [k for k in range(n) if le[i][k] and le[j][k]]
                lj = [k for k in ub if all(le[k][m] for m in ub)]
                lb = [k for k in range(n) if le[k][i] and le[k][j]]
                gm = [k for k in lb if all(le[m][k] for m in lb)]
                assert len(lj) == 1 and len(gm) == 1, ('not a lattice', self.E[i], self.E[j])
                self.join[i][j], self.meet[i][j] = lj[0], gm[0]
    def sup(self, S, default):
        r = default
        for z in S: r = self.join[r][z]
        return r
    def inf(self, S, default):
        r = default
        for z in S: r = self.meet[r][z]
        return r

def classify(L):
    le, n = L.le, L.n
    out = {}
    for s in range(n):
        for t in range(n):
            if s == t or not le[s][t]: continue
            box = [z for z in range(n) if le[s][z] and le[z][t]]
            spine = any(p not in (s, t) and all(le[z][p] or le[p][z] for z in box) for p in box)
            for c in box:
                if c in (s, t): continue
                V = [z for z in box if L.meet[z][c] != s and L.join[z][c] != t]
                out[(L.E[s], L.E[t], L.E[c])] = (len(V), spine, L.sup(V, s) != t, L.inf(V, t) != s)
    return out

def omega(N):
    E = ['bot', 'top'] + [(n, i) for n in range(1, N + 1) for i in range(1, n + 1)]
    R = [('bot', e) for e in E if e != 'bot'] + [(e, 'top') for e in E if e != 'top']
    R += [((n, i), (n, i + 1)) for n in range(1, N + 1) for i in range(1, n)]
    return Lat(E, R)

def hinf(N):
    E = ['bot', 'top', 'h', 'k'] + [(n, i) for n in range(1, N + 1) for i in range(1, n + 1)]
    R = [('bot', e) for e in E if e != 'bot'] + [(e, 'top') for e in E if e != 'top']
    R += [((n, i), (n, i + 1)) for n in range(1, N + 1) for i in range(1, n)]
    R += [((n, n), 'h') for n in range(1, N + 1)] + [((1, 1), 'k')]
    return Lat(E, R)

def sinf(N, second_atom=False):
    E = ['bot', 'top', 'd', 'c'] + (['e'] if second_atom else []) + [('z', i, j) for i in range(1, N + 1)
         for j in range(1, i + 1)] + [('w', i) for i in range(1, N + 1)]
    R = [('bot', e) for e in E if e != 'bot'] + [(e, 'top') for e in E if e != 'top'] + [('d', 'c')]
    if second_atom: R += [('e', 'c')]
    for i in range(1, N + 1):
        R += [('d', ('z', i, 1))] + [(('z', i, j), ('z', i, j + 1)) for j in range(1, i)]
        R += [(('z', i, i), ('w', i)), ('c', ('w', i))]
    return Lat(E, R)

def zigzag(N):
    """columns C_n (n = 1..N) of length n; consecutive columns share a link element above their tops' predecessors"""
    E = ['bot', 'top'] + [(n, i) for n in range(1, N + 1) for i in range(1, n + 1)] + [('l', n) for n in range(1, N)]
    R = [('bot', e) for e in E if e != 'bot'] + [(e, 'top') for e in E if e != 'top']
    R += [((n, i), (n, i + 1)) for n in range(1, N + 1) for i in range(1, n)]
    R += [((n, n), ('l', n)) for n in range(1, N)] + [((n + 1, n + 1), ('l', n)) for n in range(1, N)]
    return Lat(E, R)

FAM = {'Omega': omega, 'Hinf': hinf, 'Sinf': sinf, "Sinf'": lambda N: sinf(N, True), 'zigzag': zigzag}
if __name__ == '__main__':
    Ns = [4, 6, 8]
    for name, f in FAM.items():
        res = {N: classify(f(N)) for N in Ns}
        common = set.intersection(*(set(r) for r in res.values()))
        growing = [k for k in common if res[Ns[0]][k][0] < res[Ns[1]][k][0] < res[Ns[2]][k][0]]
        stuck = [k for k in growing if not res[Ns[-1]][k][1] and not (res[Ns[-1]][k][2] and res[Ns[-1]][k][3])]
        print(f"{name}: {len(common)} stable (box, corner) pairs; growing |V|: {len(growing)}; stuck (D-free): {len(stuck)}")
        for k in sorted(stuck, key=str)[:8]:
            v = res[Ns[-1]][k]
            print('   ', k, '|V| =', [res[N][k][0] for N in Ns], ' join<t' if v[2] else ' join=t', ' meet>s' if v[3] else ' meet=s')
