"""Turn a verified unsat core of cut_ground.py into a Lean proof (lean/Mordor/CutHeight<H>.lean).

Every core clause is classified into its axiom family and emitted as an instance of a lemma of
lean/Mordor/GroundCut.lean; `bv_decide` then refutes the conjunction (CaDiCaL + LRAT replay in the kernel).
The terms used are renumbered compactly; `tv F i` is their explicit nested F-expression.

  python3 cut_lean.py H core.cnf maps.pkl out.lean"""
import sys, pickle


def main(H, core_path, maps_path, out_path):
    M = pickle.load(open(maps_path, 'rb'))
    LE, Dv, Gv, terms = M['le'], M['d'], M['g'], M['terms']
    core = [list(map(int, l.split()[:-1])) for l in open(core_path) if l.strip() and not l.startswith('p')]
    used = set()
    for c in core:
        for x in c:
            v = abs(x)
            if v in LE: used |= set(LE[v])
            elif v in Dv: used.add(Dv[v])
            elif v in Gv: used.add(Gv[v][0])
    used |= {0, 1}
    stack = list(used)
    while stack:                                              # close under arguments
        i = stack.pop()
        if terms[i] is not None:
            for j in terms[i]:
                if j not in used: used.add(j); stack.append(j)
    order = sorted(used); ren = {o: k for k, o in enumerate(order)}
    T = lambda i: f"(t {ren[i]})"
    expr = {}
    for o in order:
        if o == 0: expr[o] = "⊥"
        elif o == 1: expr[o] = "⊤"
        else:
            s, t = terms[o]; expr[o] = f"F ({expr[s]}) ({expr[t]})"
    need_e = set(); lines = []; wlog = None
    def e(i): need_e.add(i); return f"e{ren[i]}"
    for c in core:
        pos = [x for x in c if x > 0]; neg = [-x for x in c if x < 0]
        kind = lambda v: 'le' if v in LE else 'd' if v in Dv else 'g'
        if len(c) == 1:
            v = abs(c[0]); k = kind(v)
            if k == 'le' and pos:
                i, j = LE[v]
                if i == j: lines.append(f"cl_refl {T(i)}")
                elif i == 0: lines.append(f"cl_bot h0 {T(j)}")
                elif j == 1: lines.append(f"cl_top h1 {T(i)}")
                else: raise ValueError(c)
            elif k == 'le':
                assert LE[v] == (1, 0); lines.append("cl_topbot H h1 h0")
            elif k == 'd' and (pos or Dv[v] == 1):
                lines.append("cl_dbot H h0" if pos else "cl_dtop H h1")
            elif k == 'd':                                    # WLOG unit F(⊥,⊤) ∉ D (cut_ground.run(wlog=True))
                assert terms[Dv[v]] == (0, 1); wlog = Dv[v]; e(wlog); lines.append("cl_wlog hw")
            else:
                i, kk = Gv[v]; assert not pos and kk == H + 1; lines.append(f"cl_rankmax hn {T(i)}")
            continue
        kinds = sorted(kind(abs(x)) for x in c)
        if kinds == ['le', 'le', 'le']:
            (p,) = pos; (n1, n2) = neg; a, b = LE[p]; x1, y1 = LE[n1]; x2, y2 = LE[n2]
            if y1 == x2 and x1 == a and y2 == b: lines.append(f"cl_trans {T(a)} {T(x2)} {T(b)}")
            elif y2 == x1 and x2 == a and y1 == b: lines.append(f"cl_trans {T(a)} {T(x1)} {T(b)}")
            else:
                ta, tb = terms[a], terms[b]
                ok = False
                for (u, w) in ((LE[n1], LE[n2]), (LE[n2], LE[n1])):
                    if ta is not None and tb is not None and (ta[0], tb[0]) == u and (ta[1], tb[1]) == w:
                        lines.append(f"cl_mono H {e(a)} {e(b)}"); ok = True; break
                if not ok: raise ValueError(('le3', c))
        elif kinds == ['d', 'd', 'le']:
            lev = [x for x in c if abs(x) in LE][0]; ds = [x for x in c if abs(x) in Dv]
            if lev < 0 and len([x for x in ds if x > 0]) == 1 and len([x for x in ds if x < 0]) == 1:
                p, q = LE[-lev]; dpos = [Dv[x] for x in ds if x > 0][0]; dneg = [Dv[-x] for x in ds if x < 0][0]
                if (dpos, dneg) == (p, q): lines.append(f"cl_down H {T(p)} {T(q)}")
                else:
                    # no witness: [-d(s), d(t), -le(i,s)] or [-le(t,i)]
                    s, t = dneg, dpos; i1, i2 = LE[-lev]
                    if i2 == s and terms[i1] == (s, t): lines.append(f"cl_now1 H {e(i1)}")
                    elif i1 == t and terms[i2] == (s, t): lines.append(f"cl_now2 H {e(i2)}")
                    else: raise ValueError(('d', c))
            else: raise ValueError(('d2', c))
        elif kinds == ['g', 'g', 'le', 'le']:
            le_neg = [LE[-x] for x in c if x < 0 and -x in LE][0]; p, q = le_neg
            k = [Gv[-x][1] for x in c if x < 0 and -x in Gv][0]
            lines.append(f"cl_rank {T(p)} {T(q)} {k} {k + 1} rfl")
        elif kinds == ['g', 'le', 'le']:
            le_neg = [LE[-x] for x in c if x < 0 and -x in LE][0]; p, q = le_neg
            lines.append(f"cl_rank0 {T(p)} {T(q)}")
        else: raise ValueError(('?', c))
    N = len(order); name = f"cut_height{H}"
    hyps = "\n".join(f"    (e{ren[i]} : t {ren[i]} = F (t {ren[terms[i][0]]}) (t {ren[terms[i][1]]}))" for i in sorted(need_e))
    haves = "\n".join(f"  have c{k} := {l}" for k, l in enumerate(lines))
    tv = "\n".join(f"  | {ren[o]} => {expr[o]}" for o in order)
    es = " ".join("rfl" for _ in sorted(need_e))
    clears = " ".join(f"e{ren[i]}" for i in sorted(need_e)) + (" hw" if wlog is not None else "")
    hw = f"\n    (hw : t {ren[wlog]} ∉ D)" if wlog is not None else ""
    if wlog is None:
        fin = f"core{H} ⟨hF, hD, hbot, htop, fun x hx y hy => hno x hx y hy⟩ hn (tv{H} F) rfl rfl {es}"
    else:
        fin = (f"cut_of_wlog (fun H hn hw => core{H} H hn (tv{H} _) rfl rfl {es} hw)\n"
               f"    ⟨hF, hD, hbot, htop, fun x hx y hy => hno x hx y hy⟩ hn")
    wl = ("\nThe refutation assumes `F(⊥,⊤) ∉ D`; `cut_of_wlog` (order duality) removes the assumption."
          if wlog is not None else "")
    src = f'''import Mordor.GroundCut

/-!
# The Cut Lemma at edge-height ≤ {H} (machine-generated by `experiments/sat/cut_lean.py`)

`core{H}` refutes the {len(lines)} ground clauses of a drat-trim-verified unsat core of the cut theory
`C_{H}^≤` over {N} F-terms built from `⊥, ⊤` (`experiments/sat/cut_ground.py`); every clause is an instance of a
lemma of `GroundCut.lean`, and `bv_decide` checks the propositional refutation (LRAT, kernel-checked).
`{name}`: in every bounded poset with no chain of {H + 2} elements, every monotone `F` and every down-set
`D ∋ ⊥`, `⊤ ∉ D` have a witness cell.{wl} Do not edit by hand; regenerate.
-/

namespace Mordor.Ground
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem core{H} {{α : Type*}} [PartialOrder α] [OrderBot α] [OrderTop α] {{F : α → α → α}} {{D : Set α}}
    (H : CutCx F D) (hn : NoChain α {H + 1}) (t : ℕ → α) (h0 : t 0 = ⊥) (h1 : t 1 = ⊤)
{hyps}{hw} : False := by
{haves}
  clear {clears} h0 h1 hn H
  bv_decide

/-- The explicit F-terms. -/
def tv{H} {{α : Type*}} [Bot α] [Top α] (F : α → α → α) : ℕ → α
{tv}
  | _ => ⊥

/-- **The Cut Lemma at edge-height ≤ {H}.** -/
theorem {name} {{α : Type*}} [PartialOrder α] [OrderBot α] [OrderTop α] (hn : NoChain α {H + 1})
    (F : α → α → α) (hF : ∀ x x' y y', x ≤ x' → y ≤ y' → F x y ≤ F x' y')
    (D : Set α) (hD : ∀ x y, x ≤ y → y ∈ D → x ∈ D) (hbot : ⊥ ∈ D) (htop : ⊤ ∉ D) :
    ∃ x ∈ D, ∃ y, y ∉ D ∧ (F x y ≤ x ∨ y ≤ F x y) := by
  by_contra hno
  push_neg at hno
  exact {fin}

end Mordor.Ground
'''
    open(out_path, 'w').write(src)
    print(f"wrote {out_path}: {len(lines)} clauses, {N} terms, {len(need_e)} F-equations")


if __name__ == '__main__':
    main(int(sys.argv[1]), sys.argv[2], sys.argv[3], sys.argv[4])
