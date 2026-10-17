"""analyze.py: markdown tables from a results.jsonl of run.py (round 25, §33).

  python3 analyze.py ../data/gpu-2026-10/results.jsonl

Rates are percentages of all F (census: exact; mcmc: estimates under the uniform law). Duplicate runs of the same
lattice (all<=5 lists C5, N5, M3 again under L5_*) are shown once, keyed by the lid (the lattice's order matrix hash)."""
import sys, json, os
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)


def rates(r):
    bits, J, c = r['joint_bits'], r['joint'], r['count']
    P = lambda pred: sum(v for k, v in J.items() if pred({b: k[i] == '1' for i, b in enumerate(bits)}))
    lf = r.get('laxfirst')
    return dict(
        comm=P(lambda d: d['comm']), meqn=P(lambda d: d['meqn']), polar=P(lambda d: d['polar']),
        resid=P(lambda d: not d['meqn'] and not d['polar']),                  # m ≠ n but not polar
        clgap=P(lambda d: d['meqn'] and not d['comm']),                        # m = n without commutation
        semi=P(lambda d: d['semi_ba_le_ab']), dsemi=P(lambda d: d['semi_ab_le_ba']),
        pol_dsemi=P(lambda d: d['polar'] and d['semi_ab_le_ba']),
        lax=None if lf is None else sum(lf[1:]), count=c)


def main(path):
    R, seen = [], set()
    for line in open(path):
        r = json.loads(line); k = (r['mode'], r['lid'])
        if k in seen: continue
        seen.add(k); R.append(r)
    pct = lambda x, c: f"{100 * x / c:.4f}" if c else "-"
    print("| lattice | n | mode | F | comm | m = n | polar | m ≠ n, not polar | m = n, not comm | ψ ≤ φ | φ ≤ ψ | polar ∧ φ ≤ ψ | orbit-lax | trips | viol |")
    print("|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for r in R:
        q = rates(r); c = q['count']
        lax = "n/a (schema 1)" if q['lax'] is None else f"{q['lax']:,} ({pct(q['lax'], c)})"
        print(f"| {r['lattice']} | {r['n']} | {r['mode']} | {c:,} | {pct(q['comm'], c)} | {pct(q['meqn'], c)} | "
              f"{pct(q['polar'], c)} | {pct(q['resid'], c)} | {pct(q['clgap'], c)} | {pct(q['semi'], c)} | "
              f"{pct(q['dsemi'], c)} | {pct(q['pol_dsemi'], c)} | {lax} | {sum(r['trips'].values())} | "
              f"{sum(r['viols'].values())} |")
    tot = sum(r['count'] for r in R if r['mode'] == 'census')
    print(f"\nexact census total (distinct lattices): {tot:,} F; MCMC samples: "
          f"{sum(r['count'] for r in R if r['mode'] == 'mcmc'):,}")


if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'results.jsonl'))
