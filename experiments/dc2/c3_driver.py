"""Resumable driver for the full DC2 check on M_ω² × C_n (all level-0 patterns up to coordinate swap).
usage: c3_driver.py n worker_index n_workers results_file"""
import sys, os, json, time
import dc2_lazy as d, dc2_eager as e, plane_full as P
import c3
from thick_patterns import width

n, wi, nw, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
d.PREC_L2 = False; d.BLOCK_MAXL1 = 1
done = {}
if os.path.exists(out):
    for line in open(out):
        r = json.loads(line); done[(r['tag'], r['k'])] = r
def log(r):
    with open(out, 'a') as f: f.write(json.dumps(r) + '\n')

pats = list(c3.all_patterns(n)); reps, seen = [], set()
for p in pats:
    t = c3.tag(p, n)
    if t in seen: continue
    seen.add(t); seen.add(c3.tag(c3.swap_pat(p), n)); reps.append(p)
claimdir = os.path.join(os.path.dirname(os.path.abspath(out)), f'c3_claims_n{n}')
os.makedirs(claimdir, exist_ok=True)
def claim(t):
    f = os.path.join(claimdir, t)
    try:
        fd = os.open(f, os.O_CREAT | os.O_EXCL | os.O_WRONLY); os.write(fd, str(os.getpid()).encode()); os.close(fd); return True
    except FileExistsError:
        try: pid = int(open(f).read().strip() or 0)
        except Exception: pid = 0
        alive = pid > 0 and os.path.exists(f'/proc/{pid}')
        if alive: return False
        os.remove(f)
        return claim(t)
def complete(t):
    for fn in os.listdir(os.path.dirname(os.path.abspath(out))):
        if fn.startswith('c3_results'):
            for line in open(os.path.join(os.path.dirname(os.path.abspath(out)), fn)):
                r = json.loads(line); done.setdefault((r['tag'], r['k']), r)
    c = done.get((t, 'closure'))
    return c is not None and (c.get('w') is None or all((t, k) in done for k in range(2 * c['w'] + 1)))
for p in reps:
    t = c3.tag(p, n)
    if complete(t) or not claim(t): continue
    if (t, 'closure') in done and done[(t, 'closure')].get('w') is None: continue
    if (t, 'closure') in done:
        cells = [tuple(map(tuple, c)) for c in done[(t, 'closure')]['cells']]
        cells = [(tuple(c[0]), tuple(c[1])) for c in done[(t, 'closure')]['cells']]
        w = done[(t, 'closure')]['w']
    else:
        w, cells = c3.low_width_closure(p, n)
        log({'tag': t, 'k': 'closure', 'w': w, 'cells': cells})
        if w is None: print(t, 'NO low-width closure', flush=True); continue
    d.DPAT = p; d.ZERO0 = None; d.SEL0 = False
    shapes = c3.find_shapes(p, cells, n)
    d.DPAT = p; d.CLOSED0 = lambda x, y, cs=set(cells): (x, y) in cs
    for k in range(0, 2 * w + 1):
        if (t, k) in done: continue
        closed1 = set(c for i in range(k) for c in c3.inst(shapes, ('a', i)))
        d.CLOSED1 = lambda x, y, c1=closed1: (x, y) in c1
        t0 = time.time()
        d.SKIP_BLOCKS = True
        rm = d.run(k, 1, n, verbose=False)
        d.SKIP_BLOCKS = False
        if not rm:
            log({'tag': t, 'k': k, 'res': 'UNSAT', 'how': 'master', 's': round(time.time() - t0)}); continue
        m = 2 * width(sorted(closed1, key=str)) if k else 0
        r = d.run(k, m, n, verbose=False)
        log({'tag': t, 'k': k, 'm': m, 'res': 'SAT' if r else 'UNSAT', 'how': 'lazy', 's': round(time.time() - t0)})
        print(t, k, m, 'SAT' if r else 'UNSAT', round(time.time() - t0), flush=True)
print('worker done', flush=True)
