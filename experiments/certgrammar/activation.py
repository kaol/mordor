"""Joint activation of the 12 exceptional H = 5 terms (log §34.3z⁹⁸).

1. Individual necessity: for each exception e, delete e and every T5 term having e as a subterm (the deletion must
   be upward closed), and run the seeded H = 5 ground test (cut_ground.Ground, no expansion).
2. A deletion-minimal sufficient subset of the 12 (greedy, deepest first), keeping all non-exceptional terms.
3. Which T5 terms the verified Lean replay (CutHeight5.lean, `t N` references in the core) actually uses."""
import sys, re, io, contextlib
sys.argv = ['role_pool.py']
with contextlib.redirect_stdout(io.StringIO()):
    exec(open('role_pool.py').read())
EXC = [56, 65, 66, 70, 73, 74, 76, 77, 82, 83, 84, 85]
def sub(t, u):            # u is a subterm of t
    if t == u: return True
    return not isinstance(t, str) and (sub(t[1], u) or sub(t[2], u))
def above(e):
    te = T5d[e]; return {t for t in T5 if sub(t, te)}
def quiet(H, S, label):
    with contextlib.redirect_stdout(io.StringIO()): r = ground_test(H, S, label)
    return r
print("1. individual necessity (UNSAT = still refuted without that term and its dependents):")
for e in EXC:
    rem = above(e)
    r = quiet(5, T5 - rem, f"T5 minus {e}")
    print(f"   remove t{e} (+{len(rem)-1} dependents): {'UNSAT (not necessary)' if r else 'SAT (necessary)'}", flush=True)
keep = set(EXC)
for e in sorted(EXC, key=lambda e: -depth(T5d[e])):
    trial = keep - {e}
    S = (T5 - {T5d[x] for x in EXC}) | {T5d[x] for x in trial}
    S = {t for t in S if all((not sub(t, T5d[x])) or x in trial or t == T5d[x] for x in EXC if x not in trial)}
    if quiet(5, S, "min"): keep = trial
print(f"2. deletion-minimal sufficient subset of the exceptions: {sorted(keep)}")
txt = open("../../lean/Mordor/CutHeight5.lean").read()
core = txt[txt.index("theorem core5") if "theorem core5" in txt else 0: txt.index("def tv5")]
used = {int(n) for n in re.findall(r"\(t (\d+)\)", core)}
print(f"3. terms referenced by the Lean core: {len(used)} of {len(T5d)}; exceptions referenced: "
      f"{sorted(set(EXC) & used)}; exceptions not referenced: {sorted(set(EXC) - used)}")
