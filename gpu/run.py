"""run.py: CLI and batch for the Mordor GPU census.

  python3 run.py census C4                     # exact census of one lattice (spec syntax: lattices.parse)
  python3 run.py census all5 --fibres          # every lattice with 5 elements, with exact fibre sizes of (a, b)
  python3 run.py mcmc B4 --chains 65536 --sweeps 4000 --burn 1000 --thin 10
  python3 run.py batch --list                  # the prepared jobs, with sizes
  python3 run.py batch                         # all jobs, cheapest first; resumable (Ctrl-C safe)
  python3 run.py batch 3 7                     # only jobs 3 and 7

Each finished run appends one JSON line to results.jsonl (--out); checkpoints live in checkpoints/. Send back
results.jsonl and batch.log. Env: DEVICE (cuda|cpu|...), MORDOR_MEM, MORDOR_GROUP (see engine.py),
MORDOR_MAX_F (default 1e11: 'auto' jobs run a census only when the Knuth estimate of its size is below this)."""
import sys, os, json, time, argparse
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import lattices
import engine

# (mode, spec, params, why)
BATCH = [
    ('census', 'all<=5', {'fibres': True}, "anchors: C3/C4 reproduce the log (175/24,696 bifunctions, 223 pairs on C4); every lattice ≤ 5"),
    ('census', 'C5', {'fibres': True}, "16,818,516 bifunctions; the first chain with band-satisfying polar configurations"),
    ('census', 'N5', {'fibres': True}, "pentagon, 31,022,611 bifunctions: exact law of commutation / defects / R(F) stages"),
    ('census', 'M3', {'fibres': True}, "diamond, 129,157,925 bifunctions"),
    ('mcmc', 'N5', {'chains': 32768, 'sweeps': 3000, 'burn': 1000, 'thin': 20}, "sampler validation against the N5 census"),
    ('auto', 'all6', {'chains': 32768, 'sweeps': 4000, 'burn': 1000, 'thin': 10},
     "every 6-element lattice (15): census where the Knuth estimate is ≤ MORDOR_MAX_F (C6: 5.5e10), else mcmc (M4: 1.3e14)"),
    ('mcmc', 'B3', {'chains': 65536, 'sweeps': 4000, 'burn': 1000, 'thin': 10}, "uniform law on B3"),
    ('mcmc', 'E2', {'chains': 65536, 'sweeps': 4000, 'burn': 1000, 'thin': 10}, "Theorem B lattice, uniform law"),
    ('mcmc', 'D4', {'chains': 65536, 'sweeps': 4000, 'burn': 1000, 'thin': 10}, "height-3 column lattice"),
    ('mcmc', 'E3', {'chains': 65536, 'sweeps': 6000, 'burn': 2000, 'thin': 10}, "Theorem C lattice"),
    ('mcmc', 'B4', {'chains': 32768, 'sweeps': 6000, 'burn': 2000, 'thin': 10}, "Boolean 2^4"),
    ('mcmc', 'E4', {'chains': 32768, 'sweeps': 6000, 'burn': 2000, 'thin': 10}, "the round-21 'cutting edge' (SAT-settled in round 22)"),
    ('mcmc', 'Pi4', {'chains': 32768, 'sweeps': 6000, 'burn': 2000, 'thin': 10}, "partition lattice, non-modular"),
    ('mcmc', 'C4xC4', {'chains': 32768, 'sweeps': 6000, 'burn': 2000, 'thin': 10}, "distributive grid"),
    ('mcmc', 'B5', {'chains': 8192, 'sweeps': 8000, 'burn': 3000, 'thin': 20}, "32 elements: beyond the SAT sweeps of round 23"),
]


def done(out):
    res = {}
    if os.path.exists(out):
        for line in open(out):
            try:
                r = json.loads(line); res[(r['mode'], r['lattice'], r.get('chains'), r.get('sweeps'))] = r
            except Exception: pass
    return res


MAX_F = float(os.environ.get('MORDOR_MAX_F', '1e11') or 1e11)


def key(mode, L, p): return (mode, L.name, None, None) if mode == 'census' else (mode, L.name, p.get('chains'), p.get('sweeps'))


def is_done(res, mode, L, p):
    if mode == 'auto': return key('census', L, p) in res or key('mcmc', L, p) in res
    return key(mode, L, p) in res


def summary(r):
    c = r['count']; v = r['viols']; t = r['trips']
    pct = lambda bit: 100.0 * sum(n for k, n in r['joint'].items() if k[engine.JOINT_BITS.index(bit)] == '1') / max(c, 1)
    s = (f"{r['lattice']}: {c:,} F; commuting {pct('comm'):.2f}%, m≠n {100 - pct('meqn'):.2f}%, polar {pct('polar'):.2f}%; "
         f"violators cl={v['cl']} semi={v['semi']} cut={v['cut']}; orbit-lax {sum(r['laxfirst'][1:]):,}; "
         f"tripwires {sum(t.values())}; t={r['t']}s")
    if 'fibres' in r: s += f"; realizable pairs {r['fibres']['image']:,}"
    if 'mixing' in r and r['mixing']: s += "; mixing |z|max=" + str(max(abs(m['z']) for m in r['mixing'].values()))
    return s


def run_one(mode, L, p, out, dev, log):
    os.makedirs(os.path.join(HERE, 'checkpoints'), exist_ok=True)
    if mode == 'auto':
        sz = engine.census_size(L, dev)
        mode = 'census' if sz is not None and sz[0] <= MAX_F else 'mcmc'
        log(f"  {L.name}: census size ≈ {sz[0]:.3g} ± {sz[1]:.2g}" if sz else f"  {L.name}: census refused (too large)")
        log(f"  → {mode} (MORDOR_MAX_F = {MAX_F:.3g})")
    tag = L.name + ('' if mode == 'census' else f"_c{p['chains']}_s{p['sweeps']}_seed{p.get('seed', 1)}")
    ck = os.path.join(HERE, 'checkpoints', f"{mode}_{tag}{'_fib' if p.get('fibres') else ''}.pkl")
    if mode == 'census':
        r = engine.census(L, dev, ck=ck, fibres=p.get('fibres', False), log=log)
    else:
        r = engine.mcmc(L, dev, p['chains'], p['sweeps'], p['burn'], p['thin'], p.get('seed', 1), ck=ck, log=log)
    with open(out, 'a') as fh: fh.write(json.dumps(r) + '\n')
    log("  " + summary(r))
    if sum(r['viols'].values()) or sum(r['trips'].values()):
        log("  !!! nonzero violator/tripwire counts: witnesses are in the JSON line. Please send results.jsonl.")
    return r


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('mode', choices=['census', 'mcmc', 'batch'])
    ap.add_argument('rest', nargs='*', help="lattice spec (census/mcmc) or job numbers (batch)")
    ap.add_argument('--list', action='store_true'); ap.add_argument('--fibres', action='store_true')
    ap.add_argument('--chains', type=int, default=32768); ap.add_argument('--sweeps', type=int, default=4000)
    ap.add_argument('--burn', type=int, default=1000); ap.add_argument('--thin', type=int, default=10)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--out', default=os.path.join(HERE, 'results.jsonl'))
    ap.add_argument('--device', default=os.environ.get('DEVICE'))
    a = ap.parse_args()
    dev = engine.pick_device(a.device)
    logf = open(os.path.join(HERE, 'batch.log'), 'a')
    def log(s):
        print(s, flush=True); logf.write(s + '\n'); logf.flush()
    if a.mode == 'batch':
        sel = [int(x) for x in a.rest]; res = done(a.out)
        for i, (mode, spec, p, why) in enumerate(BATCH, 1):
            Ls = lattices.parse(spec); Ls = Ls if isinstance(Ls, list) else [Ls]
            fin = sum(is_done(res, mode, L, p) for L in Ls)
            size = ""
            if mode == 'census' and len(Ls) == 1 and Ls[0].n <= 5:
                c = Ls[0].count_bifunctions(max_states=200_000)
                size = f", {c:,} bifunctions" if c else ""
            print(f"[{i}] {mode} {spec} ({len(Ls)} lattice{'s' if len(Ls) > 1 else ''}{size}; {fin}/{len(Ls)} done): {why}")
        if a.list: return
        for i, (mode, spec, p, why) in enumerate(BATCH, 1):
            if sel and i not in sel: continue
            Ls = lattices.parse(spec); Ls = Ls if isinstance(Ls, list) else [Ls]
            for L in Ls:
                if is_done(done(a.out), mode, L, p): continue
                log(f"\n=== job {i}: {mode} {L.name} ({time.strftime('%H:%M:%S')}) ===")
                run_one(mode, L, p, a.out, dev, log)
        return
    Ls = lattices.parse(a.rest[0]); Ls = Ls if isinstance(Ls, list) else [Ls]
    p = dict(fibres=a.fibres, chains=a.chains, sweeps=a.sweeps, burn=a.burn, thin=a.thin, seed=a.seed)
    if a.mode == 'census': p = dict(fibres=a.fibres)
    for L in Ls: run_one(a.mode, L, p, a.out, dev, log)


if __name__ == '__main__':
    main()
