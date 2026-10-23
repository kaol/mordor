"""Distributed atom-freeness case-split tree (c3_tree2.py + c3_leafjob.py as one claim-based work queue, §34.3z¹¹).

Queue directory DIR holds
  n_<id>.json   node {tag, zero, carry}          n_<id>.res   {'leaf': w} or {'branch': cell}
  j_<id>_<k>.json  leaf × k job                  j_<id>_<k>.res  {'res': 'UNSAT'|'SAT', ...}
  *.claim       host:pid of the worker on it (stale claims of dead local pids are removed by `worker` on start)
A node is split exhaustively on a level-0 cell c (c atom-free | c closed and carrying an L1 atom), so the leaves cover
every counterexample; a leaf is closed when all its jobs (k = 0 if carry = ∅, else 1 .. 2·width(carry)) are UNSAT.
usage: c3_dtree.py init DIR TAG [TREE_OUT [LEAVES_JSONL LEAFRES...]]   (optional seeding from earlier runs)
       c3_dtree.py worker DIR          c3_dtree.py status DIR
       c3_dtree.py node DIR ID         c3_dtree.py job DIR ID K   (internal: one item, run as a subprocess)

Outcome on 111100110000 (the one NO-CLOSURE pattern of the first M_ω² × C₃ run): infeasible.  31 random root-to-leaf
probes reach leaves at depth 12–27 with carry width 1–8; Knuth's estimator gives ≈1.4·10⁷ leaves.  Superseded by a
direct width-5 closure (closure_111100110000_w5.json, run with run_one.sh); kept as the record of the attempt."""
import sys, os, json, hashlib, random, socket, subprocess, time

cv = lambda cs: frozenset((tuple(c[0]), tuple(c[1])) for c in cs)
js = lambda cs: sorted(([list(c[0]), list(c[1])] for c in cs), key=str)
def nid(Z, C): return hashlib.sha1(json.dumps([js(Z), js(C)]).encode()).hexdigest()[:16]
def rd(p): return json.load(open(p))
def wr(p, o):
    t = f"{p}.tmp{os.getpid()}"; json.dump(o, open(t, 'w')); os.replace(t, p)
def mk(p, o):  # create once (children may be created concurrently by a re-run parent)
    if not os.path.exists(p): wr(p, o)
def node_file(D, tag, Z, C):
    i = nid(Z, C); mk(f"{D}/n_{i}.json", {'tag': tag, 'zero': js(Z), 'carry': js(C)}); return i

def setup_pat(tag, n=3):
    import c3
    return next(p for p in c3.all_patterns(n) if c3.tag(p, n) == tag)

def do_node(D, i):
    import dc2_lazy as d, dc2_eager as e, plane_full as P
    from thick_patterns import width
    B, T = d.B, d.T
    N = rd(f"{D}/n_{i}.json"); tag = N['tag']; Z, C = cv(N['zero']), cv(N['carry']); n = 3
    pat = setup_pat(tag, n); Dset = {p for p, v in pat.items() if v}
    cells = [(x, y) for x in pat for y in pat if x in Dset and y not in Dset]
    d.DPAT = pat; d.CLOSED1 = P.fibre; d.SEL0 = False
    d.ZERO0 = (lambda x, y: (x, y) in Z) if Z else None
    d.CLOSED0 = lambda x, y: (x, y) in C or (x, y) in Z
    d.CARRY0 = (lambda x, y: (x, y) in C) if C else None
    w = width(sorted(C, key=str)) if C else 0
    sizes = [(0, 0)] if not C else [(k, 2) for k in range(1, min(2, 2 * w) + 1)]
    t0 = time.time()
    for k, m in sizes:
        if e.run(k, m, n, verbose=False):
            M, V, pairs, dom = d.LAST_MODEL
            busy = []
            for c in cells:
                if c in Z or c in C: continue
                vals = [a for j in range(2) for a in dom(*c) if V('v', *c, j, a) in M]
                busy.append((any(a not in (B, T) for a in vals), c))
            if not busy:
                wr(f"{D}/n_{i}.res", {'stuck': True, 'k': k, 's': round(time.time() - t0)}); return
            busy.sort(key=lambda t: (not t[0], width(sorted(C | {t[1]}, key=str))))
            c = busy[0][1]
            a = node_file(D, tag, Z | {c}, C); b = node_file(D, tag, Z, C | {c})
            wr(f"{D}/n_{i}.res", {'branch': js([c])[0], 'children': [a, b], 's': round(time.time() - t0)}); return
    for k in ([0] if not C else range(1, 2 * w + 1)): mk(f"{D}/j_{i}_{k}.json", {'node': i, 'k': k})
    wr(f"{D}/n_{i}.res", {'leaf': w, 's': round(time.time() - t0)})

def do_job(D, i, k):
    import c3, dc2_lazy as d
    from thick_patterns import width
    N = rd(f"{D}/n_{i}.json"); tag = N['tag']; Z, C = cv(N['zero']), cv(N['carry']); n = 3
    pat = setup_pat(tag, n)
    d.PREC_L2 = False; d.BLOCK_MAXL1 = 1; d.SEL0 = False
    def setup():
        d.DPAT = pat
        d.ZERO0 = (lambda x, y: (x, y) in Z) if Z else None
        d.CARRY0 = (lambda x, y: (x, y) in C) if C else None
    setup()
    shapes = c3.find_shapes(pat, sorted(C | Z, key=str), n) if C and k > 0 else []
    setup(); d.CLOSED0 = lambda x, y: (x, y) in C or (x, y) in Z
    closed1 = set(c for j in range(k) for c in c3.inst(shapes, ('a', j)))
    d.CLOSED1 = lambda x, y: (x, y) in closed1
    t0 = time.time()
    d.SKIP_BLOCKS = True; rm = d.run(k, 1, n, verbose=False); d.SKIP_BLOCKS = False
    if not rm: rec = {'res': 'UNSAT', 'how': 'master', 's': round(time.time() - t0)}
    else:
        m = 2 * width(sorted(closed1, key=str)) if k else 0
        r = d.run(k, m, n, verbose=False)
        rec = {'res': 'SAT' if r else 'UNSAT', 'how': 'lazy', 'm': m, 's': round(time.time() - t0)}
    rec['host'] = socket.gethostname(); wr(f"{D}/j_{i}_{k}.res", rec)

def alive(pid):
    try: os.kill(pid, 0); return True
    except OSError: return False

def worker(D):
    host = socket.gethostname(); me = f"{host}:{os.getpid()}"
    for f in os.listdir(D):  # stale local claims
        if f.endswith('.claim'):
            try: h, p = open(f"{D}/{f}").read().split(':')
            except Exception: continue
            if h == host and not alive(int(p)): os.remove(f"{D}/{f}")
    while True:
        fs = set(os.listdir(D))
        todo = lambda s: [f[:-5] for f in fs if f.startswith(s) and f.endswith('.json')
                          and f[:-5] + '.res' not in fs and f[:-5] + '.claim' not in fs]
        nodes, jobs = todo('n_'), todo('j_')
        if nodes: random.shuffle(nodes); cand = nodes
        elif jobs: random.shuffle(jobs); cand = sorted(jobs, key=lambda j: int(j.split('_')[2]))
        elif any(f.endswith('.claim') for f in fs): time.sleep(20); continue
        else: return
        for it in cand[:5]:
            try: fd = os.open(f"{D}/{it}.claim", os.O_CREAT | os.O_EXCL | os.O_WRONLY)
            except FileExistsError: continue
            os.write(fd, me.encode()); os.close(fd)
            args = ['node', D, it[2:]] if it.startswith('n_') else ['job', D] + it[2:].split('_')
            r = subprocess.run([sys.executable, '-u', os.path.abspath(__file__)] + args)
            if r.returncode: print('FAILED', it, r.returncode, flush=True)
            os.remove(f"{D}/{it}.claim")
            break

def status(D):
    fs = set(os.listdir(D)); root = nid(frozenset(), frozenset())
    st = {'nodes': 0, 'leaves': 0, 'open_nodes': 0, 'jobs_done': 0, 'jobs_open': 0, 'SAT': [], 'stuck': [], 'maxw': 0,
          'max_s': 0}
    stack = [root]
    while stack:
        i = stack.pop(); st['nodes'] += 1
        if f"n_{i}.res" not in fs: st['open_nodes'] += 1; continue
        r = rd(f"{D}/n_{i}.res")
        if 'stuck' in r: st['stuck'].append(i); continue
        if 'branch' in r: stack += r['children']; continue
        st['leaves'] += 1; st['maxw'] = max(st['maxw'], r['leaf'])
        C = rd(f"{D}/n_{i}.json")['carry']
        for k in ([0] if not C else range(1, 2 * r['leaf'] + 1)):
            if f"j_{i}_{k}.res" not in fs: st['jobs_open'] += 1; continue
            jr = rd(f"{D}/j_{i}_{k}.res"); st['jobs_done'] += 1; st['max_s'] = max(st['max_s'], jr['s'])
            if jr['res'] != 'UNSAT': st['SAT'].append((i, k))
    closed = not (st['open_nodes'] or st['jobs_open'] or st['SAT'] or st['stuck'])
    print(json.dumps(st)); print('CLOSED: every counterexample is refuted' if closed else 'not closed')

def init(D, tag, tree_out=None, leaves=None, leafres=()):
    os.makedirs(D, exist_ok=True); node_file(D, tag, frozenset(), frozenset())
    if not tree_out: return
    # Seed leaf results from a c3_tree2.py run (internal nodes are recomputed; same code/solver gives the same splits).
    for l in open(tree_out):
        if not l.startswith('{'): continue
        L = json.loads(l); Z, C = cv(L['zero']), cv(L['carry']); i = node_file(D, tag, Z, C)
        mk(f"{D}/n_{i}.res", {'leaf': L['w'], 's': 0, 'seeded': True})
        for k in ([0] if not C else range(1, 2 * L['w'] + 1)): mk(f"{D}/j_{i}_{k}.json", {'node': i, 'k': k})
    if leaves:
        idx = [json.loads(l) for l in open(leaves) if l.startswith('{')]
        for f in leafres:
            for l in open(f):
                r = json.loads(l); L = idx[r['leaf']]; i = nid(cv(L['zero']), cv(L['carry']))
                if os.path.exists(f"{D}/j_{i}_{r['k']}.json"):
                    mk(f"{D}/j_{i}_{r['k']}.res", {k: v for k, v in r.items() if k not in ('tag', 'leaf', 'k')} | {'seeded': True})

if __name__ == '__main__':
    cmd, D = sys.argv[1], sys.argv[2].rstrip('/')
    if cmd == 'init':
        a = sys.argv[4:]; init(D, sys.argv[3], a[0] if a else None, a[1] if len(a) > 1 else None, a[2:])
    elif cmd == 'worker': worker(D)
    elif cmd == 'status': status(D)
    elif cmd == 'node': do_node(D, sys.argv[3])
    elif cmd == 'job': do_job(D, sys.argv[3], int(sys.argv[4]))
