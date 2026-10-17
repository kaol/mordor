# First GPU run (round 25, §33)

`results.jsonl` and `batch.log` from `python3 gpu/run.py batch` on a Radeon Pro W6600 (ROCm 6.4, torch 2.9.1), as sent
back. Jobs 1–5 ran on the schema-1 engine and have no orbit fields; jobs 6–15 are schema 2. Tables:
`python3 gpu/analyze.py data/gpu-2026-10/results.jsonl`. The checkpoint pickles are not committed: they duplicate the
histograms here and hold raw MCMC chain states.
