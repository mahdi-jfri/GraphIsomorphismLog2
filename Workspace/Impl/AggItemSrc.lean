module

public import Workspace.Impl.AggStructDesSrc
public import Workspace.Impl.AggStructCol

@[expose] public section

/-!
# The source tuple of Case 3, from the output of the refinement call

The search for the source tuple of Case 3 (`stDSrc3_spec`) reads the refined
colors as numbers. Its cost is polynomial only when every color is below `2 q^κ`; `stDSrc3_spec`
takes this as the hypothesis `hcl`. The items phase runs the search on the first coloring
returned by the cited joint `κ`-ary refinement (`stRef_spec`, the task **KaryRefinement**). The
output contract of that task (`KaryOut`) bounds its colors by `2 n^k` with `n = q` and `k = κ`.
This file discharges `hcl` from that contract (`it_src3_spec`), so no hypothesis on the colors
remains, and no change to the model (`JointFn`) is needed.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val encKColoring)

/-- **The search for the source tuple on the refinement output.** If `w` is a result of the
joint refinement of `c, c'` (`KaryOut`), then `w = [d, d']` for a joint refinement `(d, d')`,
and on `[d, q, κ]` the search returns the entries of `stSrc3 d`, at cost
`stDSrcK (N + 1)^36` with `N = 30 (q^κ + 1)² + 2q + 2κ + 20`. The color bound of
`stDSrc3_spec` is the bound `d x < 2 q^κ` of `KaryOut`. -/
theorem it_src3_spec {P : Program} {f pw fs rb dc sp des : ℕ}
    (hf : P.funs[f]? = some (stDSrcF pw fs rb dc)) (hpw : P.HasAt pw (stDPowFuns pw))
    (hfs : P.HasAt fs (findFuns fs sp)) (hsp : P.funs[sp]? = some (stDSrcPF des dc))
    (hdes : StDesOK P des) (hdc : P.HasAt dc (stDDecFuns dc)) (hrb : P.HasAt rb (rangeFuns rb))
    {q κ : ℕ} (hq : 2 ≤ q) (hκ : 0 < κ) {c c' : (Fin κ → Fin q) → ℕ} {w : Val}
    (hw : KaryOut c c' w) :
    ∃ d d' : (Fin κ → Fin q) → ℕ, w = .list [encKColoring d, encKColoring d'] ∧
      GI.Cited.JointRefinement c c' d d' ∧
      FunDet P f (.list [encKColoring d, .nat q, .nat κ])
        (natList (stL fun i => (stSrc3 (ℓ := κ + 1) d (Nat.lt_succ_self κ) (by omega) i : ℕ)))
        (stDSrcK * (30 * (q ^ κ + 1) ^ 2 + 2 * q + 2 * κ + 20 + 1) ^ 36) := by
  obtain ⟨d, d', rfl, hd, -, hJ⟩ := hw
  refine ⟨d, d', rfl, hJ, stDSrc3_spec hf hpw hfs hsp hdes hdc hrb d hq hκ hd ?_⟩
  have h1 := wt_encKColoring_le hd
  have h2 := wt_list3_le (encKColoring d) (.nat q) (.nat κ)
  have h3 := wt_nat_le q
  have h4 := wt_nat_le κ
  omega

end GI.Impl
