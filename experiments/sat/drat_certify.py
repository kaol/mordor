"""Independent check of an UNSAT clause set: solve it with Glucose 4 (PySAT, DRAT proof logging) and verify the proof
with drat-trim, optionally writing the verified core.   python3 drat_certify.py in.cnf path/to/drat-trim [core.cnf]"""
import sys, subprocess, time
from pysat.formula import CNF
from pysat.solvers import Glucose4
cnf, trim = sys.argv[1], sys.argv[2]; core = sys.argv[3] if len(sys.argv) > 3 else None
F = CNF(from_file=cnf); t0 = time.time()
with Glucose4(bootstrap_with=F.clauses, with_proof=True) as s:
    sat = s.solve(); proof = s.get_proof() if not sat else None
print(f"{cnf}: {len(F.clauses)} clauses, {F.nv} variables, Glucose4 {'SAT' if sat else 'UNSAT'} in {time.time() - t0:.1f}s", flush=True)
if sat: sys.exit(1)
drat = cnf.rsplit('.', 1)[0] + '.drat'
with open(drat, 'w') as fh: fh.write('\n'.join(proof) + '\n')
args = [trim, cnf, drat] + (['-c', core] if core else [])
out = subprocess.run(args, capture_output=True, text=True).stdout
print('\n'.join(l for l in out.splitlines() if 'VERIFIED' in l or 'core' in l.lower() or 'ERROR' in l or 'lemmas' in l))
sys.exit(0 if 's VERIFIED' in out else 2)
