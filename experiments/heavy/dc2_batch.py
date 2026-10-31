"""DC2 on M_ω^dim × C_n at larger pools (log §34.3z⁵³, §34.3z⁵⁸), for machines with more memory and time.

For each instance (k, m) it builds the encoding of experiments/products/depth_support_gen.py unchanged and either
  dump   writes the clause set as DIMACS (streamed to disk, so memory is the encoder's, not the solver's), for an
         external proof-producing solver (kissat / cadical) and drat-trim: see run_dc2.sh;
  solve  solves in process with CaDiCaL (pysat), as the log's runs did.
One JSON line per instance is appended to dc2_results.jsonl (instance, points, variables, clauses, result, seconds).
UNSAT certifies "no depth-2 model with these pool sizes"; DC2 needs every (k, m) up to the bounds of §34.3z⁵⁸
(|L₁| ≤ 30 for n = 3), so each result is a finite instance, not a proof of DC2.

  python3 dc2_batch.py dump  4,2 2,4 4,3 3,4 4,4 [--n 3] [--dim 2] [--out cnf/]
  python3 dc2_batch.py solve 4,2 [--solver cd195]"""
import sys, os, time, json, argparse
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'products'))
import depth_support_gen as g


class Dumped(Exception):
    pass


def recorder(path):
    class Rec:
        """Stands in for the pysat solver: streams clauses to `path`.body, writes the DIMACS file on solve()."""
        def __init__(self):
            self.body = open(path + '.body', 'w'); self.nc = 0; self.nv = 0
        def add_clause(self, c):
            self.body.write(' '.join(map(str, c)) + ' 0\n'); self.nc += 1
            m = max((abs(x) for x in c), default=0)
            if m > self.nv: self.nv = m
        def solve(self, *a, **k):
            self.body.close()
            with open(path, 'w') as out, open(path + '.body') as body:
                out.write(f"p cnf {self.nv} {self.nc}\n")
                for line in body: out.write(line)
            os.remove(path + '.body')
            raise Dumped((self.nv, self.nc))
    return Rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('mode', choices=['dump', 'solve'])
    ap.add_argument('pools', nargs='+')
    ap.add_argument('--n', type=int, default=3)
    ap.add_argument('--dim', type=int, default=2)
    ap.add_argument('--out', default='cnf')
    ap.add_argument('--solver', default='cd153', choices=['cd153', 'cd195'])
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    for spec in a.pools:
        pools = [int(x) for x in spec.split(',')]
        tag = f"dc2_dim{a.dim}_n{a.n}_" + '_'.join(map(str, pools))
        t0 = time.time(); rec = {'instance': tag, 'pools': pools, 'n': a.n, 'dim': a.dim, 'mode': a.mode}
        if a.mode == 'dump':
            path = os.path.join(a.out, tag + '.cnf')
            orig = g.Cadical153; g.Cadical153 = recorder(path)
            try:
                g.run(pools, a.n, tag, dim=a.dim, quiet=True)
            except Dumped as e:
                rec.update(variables=e.args[0][0], clauses=e.args[0][1], result='dumped', cnf=path)
            finally:
                g.Cadical153 = orig
        else:
            if a.solver == 'cd195':
                from pysat.solvers import Cadical195; g.Cadical153 = Cadical195
            r, _, var, P = g.run(pools, a.n, tag, dim=a.dim)
            rec.update(points=len(P), variables=len(var), result='SAT' if r else 'UNSAT', solver=a.solver)
        rec['seconds'] = round(time.time() - t0, 1)
        print(json.dumps(rec), flush=True)
        with open('dc2_results.jsonl', 'a') as fh: fh.write(json.dumps(rec) + '\n')


if __name__ == '__main__':
    main()
