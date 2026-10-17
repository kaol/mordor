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


def test_plan_census_only():
    engine.Plan(lattices.N5(), DEV, census=True, mcmc=False)                 # self-test builds what it needs


def test_orbit_lax_top_closed_and_witnesses():
    """§32.6: ⋁R_k = r_k for every F on a top-closed lattice (tree ⊕ ⊤); on B2 ⊕ ⊤ (L5_3) strict orbits exist, and every
    orbit_lax witness is confirmed by the reference."""
    for spec in ('C4', 'B2'):
        assert sum(engine.census(lattices.parse(spec), DEV, log=quiet)['laxfirst'][1:]) == 0
    L = next(L for L in lattices.all_lattices(5) if L.name == 'L5_3')
    r = engine.mcmc(L, DEV, chains=2048, sweeps=120, burn=20, thin=10, seed=5, log=quiet)
    W = r['witnesses'].get('orbit_lax', [])
    assert sum(r['laxfirst'][1:]) > 0 and W
    for f in W:
        o = reference.observe_one(L, np.array(f).reshape(L.n, L.n))
        assert o['laxfirst'] >= 0 and not o['trip_lax']


def _all_F(L):
    P = engine.Plan(L, DEV); Rw = torch.zeros(1, 0, dtype=torch.int32, device=DEV)
    for k in range(L.n): Rw = engine.census_level(P, Rw, k)
    return P, engine.leaves_to_F(P, Rw)


def _joint_keys(f, sel):
    keys = sum(f[k][sel].long() << i for i, k in enumerate(engine.JOINT_BITS))
    return collections.Counter(''.join('1' if k >> i & 1 else '0' for i in range(len(engine.JOINT_BITS))) for k in keys.tolist())


@pytest.mark.parametrize('spec,box', [('B2', 'corners'), ('B2', 'rowgap'), ('C4', 'corners')])
def test_box_heat_bath_exact(spec, box):
    """§33.5(1): the heat bath inside a box is uniform on the monotone F of the box (vs exhaustive enumeration)."""
    L = lattices.parse(spec); P, F = _all_F(L)
    lo, hi = engine.box_preset(L, box)
    lo, hi = torch.as_tensor(lo, device=DEV), torch.as_tensor(hi, device=DEV)
    inb = (P.leq[lo[None], F] & P.leq[F, hi[None]]).flatten(1).all(1)
    f = engine.observe(P, F); exact = _joint_keys(f, inb); tot = int(inb.sum())
    r = engine.mcmc(L, DEV, chains=2048, sweeps=300, burn=50, thin=10, seed=4, log=quiet, box=box)
    N = r['count']; chi2 = sum((r['joint'].get(k, 0) - N * c / tot) ** 2 / (N * c / tot) for k, c in exact.items())
    assert set(r['joint']) <= set(exact), "sampler produced a joint key absent from the box"
    dof = max(1, len(exact) - 1)
    assert chi2 < dof + 10 * (2 * dof) ** 0.5 + 50, (chi2, dof)


def test_tmmc_logg_synthetic():
    """Level masses from exact proposal counts of a symmetric kernel: C[s, t] = g(s) Q(s→t) with g Q symmetric."""
    rng = np.random.default_rng(0); g = np.array([1e-6, 3e-3, 0.2, 0.797]); m = len(g)
    K = rng.random((m, m)); K = K + K.T                                          # symmetric flux g(s) Q(s, t)
    C = K * 1e9                                                                   # counts ∝ flux
    assert np.allclose(np.exp(engine.tmmc_logg(C)), C.sum(1) / C.sum(), rtol=1e-9)  # symmetric C ⇒ g ∝ visits
    Q = K / g[:, None]; Q /= Q.sum(1).max(); np.fill_diagonal(Q, 0); np.fill_diagonal(Q, 1 - Q.sum(1))
    C = g[:, None] * Q * 1e12
    assert np.allclose(np.exp(engine.tmmc_logg(C)), g, rtol=1e-6)


def test_mucan_matches_census_C4():
    """§33.5(1): multicanonical/TMMC level masses and per-level conditional laws vs the exact C4 census."""
    L = lattices.chain(4); P, F = _all_F(L); f = engine.observe(P, F)
    nlev, Sf = engine.SCORES['rstages'][0](P), engine.SCORES['rstages'][1]; S = Sf(P, f)
    exact = (torch.bincount(S, minlength=nlev).double() / len(S)).tolist()
    r = engine.mucan(L, DEV, 'rstages', chains=2048, sweeps=300, adapt=200, burn=50, thin=5, seed=1, log=quiet)
    for e, p in zip(exact, r['p_uniform']):
        assert (p is None and e == 0) or abs(p - e) < 0.02, (exact, r['p_uniform'])
    for lev in r['levels']:
        sel = S == lev['level']; ex = _joint_keys(f, sel); tot = int(sel.sum()); N = lev['count']
        assert set(lev['joint']) <= set(ex)
        chi2 = sum((lev['joint'].get(k, 0) - N * c / tot) ** 2 / (N * c / tot) for k, c in ex.items())
        assert chi2 < len(ex) + 10 * (2 * len(ex)) ** 0.5 + 50, (lev['level'], chi2)
        for x in lev['examples']:
            assert int(Sf(P, engine.observe(P, torch.as_tensor([x], device=DEV)))[0]) == lev['level']


def test_mucan_checkpoint_resume(tmp_path):
    L = lattices.B(2); ck = str(tmp_path / 'u.pkl')
    kw = dict(chains=256, sweeps=40, adapt=40, burn=10, thin=5, seed=3, log=quiet)
    a = engine.mucan(L, DEV, 'defects', **kw)
    engine.mucan(L, DEV, 'defects', ck=ck, **kw)
    b = engine.mucan(L, DEV, 'defects', ck=ck, **kw)                             # resumed at the end
    for r in (a, b): r.pop('t'); r.pop('device')
    assert a == b


def test_parse_all_lattice_names():
    assert lattices.parse('L6_12').leq.tolist() == lattices.all_lattices(6)[12].leq.tolist()
