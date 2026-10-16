"""Tests for the Mordor GPU census. Run on the target device:  DEVICE=cuda python3 -m pytest -q tests
(default: whatever engine.pick_device chooses). Anchors come from the research log (docs/rounds)."""
import os, sys, collections
import numpy as np, pytest, torch
HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__))); sys.path.insert(0, HERE)
import lattices, engine, reference

DEV = engine.pick_device(os.environ.get('DEVICE'))
quiet = lambda s: None


def ones(r, bit):
    return sum(c for k, c in r['joint'].items() if k[engine.JOINT_BITS.index(bit)] == '1')


@pytest.mark.parametrize('spec,total', [('C3', 175), ('C4', 24696), ('B2', 28224), ('C5', 16818516), ('N5', 31022611)])
def test_counts_dp(spec, total):
    assert lattices.parse(spec).n_bifunctions == total                       # MacMahon (§16.4), §13.2


def test_census_anchors_chain4():
    r = engine.census(lattices.chain(4), DEV, fibres=True, log=quiet)
    assert r['count'] == 24696                                               # §16.4
    assert ones(r, 'comm') == 12450 and r['count'] - ones(r, 'meqn') == 7280  # §15.1, §22.1
    assert ones(r, 'polar') == 6440                                          # §18.1
    assert r['fibres']['image'] == 223                                       # §24.1: derived pairs on chain-4
    assert sum(r['trips'].values()) == 0 and sum(r['viols'].values()) == 0


def test_census_anchors_chain3_B2():
    r = engine.census(lattices.chain(3), DEV, fibres=True, log=quiet)
    assert (r['count'], ones(r, 'comm'), r['count'] - ones(r, 'meqn'), r['fibres']['image']) == (175, 137, 20, 27)
    r = engine.census(lattices.B(2), DEV, log=quiet)
    assert r['count'] == 28224 and ones(r, 'comm') == 15984                  # §13.2


@pytest.mark.parametrize('spec', ['C4', 'B2', 'M3', 'N5', 'E2', 'D3', 'B3', 'C3xC3'])
def test_observe_matches_reference(spec):
    engine.Plan(lattices.parse(spec), DEV, census=False)                     # Plan.selftest compares with reference


def test_census_equals_reference_loop_B2():
    """Every F on B2 through the reference implementation; the census joint histogram must agree exactly."""
    L = lattices.B(2); P = engine.Plan(L, DEV)
    Rw = torch.zeros(1, 0, dtype=torch.int32, device=DEV)
    for k in range(L.n): Rw = engine.census_level(P, Rw, k)
    F = engine.leaves_to_F(P, Rw).cpu().numpy()
    assert len(F) == 28224 and len({f.tobytes() for f in F}) == 28224
    assert engine.monotone(P, torch.as_tensor(F, device=DEV)).all()
    want = collections.Counter()
    for f in F:
        o = reference.observe_one(L, f)
        want[''.join('1' if o[k] else '0' for k in engine.JOINT_BITS)] += 1
    assert engine.census(L, DEV, log=quiet)['joint'] == dict(want)


def test_census_checkpoint_resume(tmp_path, monkeypatch):
    ck = str(tmp_path / 'ck.pkl')
    monkeypatch.setattr(engine, 'GROUP', 7)
    L = lattices.chain(4)
    full = engine.census(L, DEV, log=quiet)
    a = engine.census(L, DEV, ck=ck, log=quiet)
    b = engine.census(L, DEV, ck=ck, log=quiet)                              # everything resumed from the checkpoint
    for r in (full, a, b): r.pop('t'); r.pop('device')
    assert full == a == b and full['count'] == 24696


def test_mcmc_uniform_on_C4():
    """Heat bath ≈ uniform: joint-key frequencies vs the exact census (chi-square, loose: samples are autocorrelated)."""
    L = lattices.chain(4)
    exact = engine.census(L, DEV, log=quiet)
    r = engine.mcmc(L, DEV, chains=4096, sweeps=400, burn=100, thin=10, seed=7, log=quiet)
    N = r['count']; chi2 = 0.0
    for k, c in exact['joint'].items():
        e = N * c / exact['count']; chi2 += (r['joint'].get(k, 0) - e) ** 2 / e
    dof = len(exact['joint']) - 1
    assert chi2 < dof + 10 * (2 * dof) ** 0.5 + 50, (chi2, dof)
    assert all(abs(m['z']) < 8 for m in r['mixing'].values()), r['mixing']


def test_mcmc_checkpoint_resume(tmp_path):
    L = lattices.B(2); ck = str(tmp_path / 'm.pkl')
    a = engine.mcmc(L, DEV, chains=256, sweeps=60, burn=10, thin=5, seed=3, log=quiet)
    engine.mcmc(L, DEV, chains=256, sweeps=60, burn=10, thin=5, seed=3, ck=ck, log=quiet)
    b = engine.mcmc(L, DEV, chains=256, sweeps=60, burn=10, thin=5, seed=3, ck=ck, log=quiet)   # resumed at the end
    for r in (a, b): r.pop('t'); r.pop('device')
    assert a == b


@pytest.mark.parametrize('spec,mem', [('C4', 8 << 10), ('B2', 4 << 10)])
def test_census_small_memory_budget(monkeypatch, spec, mem):
    """With a small MORDOR_MEM every split path (parent batches, child-count splits, leaf chunks) runs; result unchanged."""
    ref = engine.census(lattices.parse(spec), DEV, log=quiet)
    monkeypatch.setattr(engine, 'MEM', mem)
    small = engine.census(lattices.parse(spec), DEV, log=quiet)
    for r in (ref, small): r.pop('t'); r.pop('device')
    assert ref == small
