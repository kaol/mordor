# Mordor GPU census

Measures the projection F ↦ (a, b) of the Mordor research log on finite lattices, on a GPU through PyTorch (ROCm/HIP on
AMD, CUDA, or the CPU). Two modes:
- **census**: every monotone bifunction F, exact.
- **mcmc**: many heat-bath chains sampling F uniformly, for lattices too large for a census.

Per F it records:
- commutation and both one-sided semi-commutations,
- polarity, whether μν = νμ, the common fixed points,
- the defects of a∘b vs b∘a,
- the stages of the Cut Lemma closure R(F), and of its transposed ideal orbit r_k, with the first stage where ⋁R_k < r_k
  (orbit laxity, round 24 §32.6),
- optionally the exact fibre sizes over each pair (a, b).

Theorems of the log are checked on every F (tripwires). Conjectures (CL, semi-CL, Cut Lemma) are counted; any
violator is saved in full. Design and correctness argument: `DESIGN.md`.

## Setup: Radeon Pro W6600 (Linux, ROCm)

```bash
python3 -m venv ~/mordor && . ~/mordor/bin/activate
pip install numpy pytest
# PyTorch with ROCm: pick the newest ROCm index listed at https://pytorch.org/get-started/locally/
pip install torch --index-url https://download.pytorch.org/whl/rocm6.4
export HSA_OVERRIDE_GFX_VERSION=10.3.0      # W6600 is gfx1032; ROCm wheels ship gfx1030 kernels
python3 -c "import torch; print(torch.cuda.is_available(), torch.cuda.get_device_name(0))"
```

The W6600 is RDNA 2 (gfx1032), which the ROCm wheels do not list. The override makes it run the gfx1030 kernels,
which is the usual working setup for Navi 23 cards. If you see "invalid device function", the override is not set
in that shell. `DEVICE=cpu` runs everything on the CPU, if needed.

The card has 8 GB, and the desktop (X11) needs some of it. `MORDOR_MEM` (MiB, default 1024) bounds every working
set. That covers the level masks, the children of one expansion and the observe batches, so peak device memory stays
around that value plus a few hundred MiB of tables. On a CUDA/ROCm device the progress lines report the peak.
1024 leaves plenty for X11. Raise it only if the peak stays well below what you can spare.
`export PYTORCH_CUDA_ALLOC_CONF=expandable_segments:True` reduces fragmentation on long runs.

## Validate

```bash
cd gpu
DEVICE=cuda python3 -m pytest -q tests          # anchors from the log, reference ≡ engine, MCMC ≈ census, resume
```

Every run also starts with a self-test that compares the device against an independent pure-Python reference. It
refuses to start on a mismatch.

## Run

```bash
python3 run.py batch --list        # the prepared jobs
python3 run.py batch               # all jobs, in order; resumable (Ctrl-C safe)
python3 run.py batch 2 5           # only jobs 2 and 5
python3 run.py census N5 --fibres  # one census
python3 run.py mcmc B4 --chains 65536 --sweeps 6000 --burn 2000 --thin 10
```

Lattice specs: `C5` (chain), `M3` (diamond), `N5`, `B3` (Boolean), `E2` / `D3` (column lattices of the log), `Pi4`
(partitions), products such as `C3xC3`, and families `all6` / `all<=5` (every lattice of that size). A census
refuses lattices with more than 9 elements. Use mcmc there.

Every census first prints a Knuth estimate of its size and, once it is running, the hours left at the measured rate.
The 6-element lattices range from 3.7·10¹⁰ to 1.2·10¹⁴ bifunctions (M4 = L6_0: exactly 133,623,571,885,248). Job 6 is
therefore `auto`: census where the estimate is ≤ `MORDOR_MAX_F`, mcmc otherwise.

Send back `results.jsonl` and `batch.log`. Each run logs a one-line summary: rates, violator counts, tripwire
count, orbit-lax count, and F/s. A line with `!!!` means a nonzero violator or tripwire count. Its witnesses are in the JSON.
Orbit-lax F are not errors: they are expected on lattices where L ∖ {⊤} is not a tree (B2 ⊕ 1: 1,360,132 of 22,969,892), and
0 on the others (C5, N5, M3, …). Example F are in the JSON under `witnesses.orbit_lax`. Results carry `schema: 2`.

| env | default | meaning |
|---|---|---|
| `DEVICE` | auto | `cuda` (also ROCm), `cpu`, `cuda:1`, … |
| `MORDOR_MEM` | 1024 | MiB per working set |
| `MORDOR_GROUP` | 256 | census prefix jobs per checkpoint |
| `MORDOR_MAX_F` | 1e11 | `auto` jobs run a census only if its estimated size is below this; otherwise mcmc |

## Files

- `lattices.py`: lattices, Mon(L), and exact census totals by DP. Numpy only.
- `engine.py`: `Plan`, `observe`, `Hist`, `Fibres`, and the `census` and `mcmc` drivers. Torch.
- `reference.py`: an independent per-F reference, used by the self-test and the tests.
- `run.py`: the CLI and the batch. It writes `results.jsonl`, `batch.log` and `checkpoints/`.
- `tests/test_gpu.py`: the validation suite.
- `analyze.py`: markdown tables from a `results.jsonl` (`python3 analyze.py results.jsonl`). The first run's data is in
  `../data/gpu-2026-10/` (round 25, §33).
