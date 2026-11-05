module

public import Workspace.Impl.OutbRad
public import Workspace.Impl.RowLayout
public import Workspace.Impl.GenSpecLayout
public import Workspace.Proved.MBlk
public import Workspace.Proved.NClNormal

@[expose] public section

/-!
# The Stage 2 radical subgroup program in the row slot `rad`

`outbRadFuns b` (`OutbRad.lean`) is the code of the Stage 2 radical subgroup program (Lemma A.21′),
written to sit at index `b`. In all, it has 496 functions:
* `0`: `outbRadEntry`,
* `1`–`3`: `mapFuns` (3 functions),
* `4`–`334`: `flRadFuns` (331 functions),
* `335`–`434`: `socPreFuns` (100 functions),
* `435`–`495`: `outbSuppFuns` (61 functions).

The primitive table of the final program is `[pst, mem, pre, fac] ++ gsExtra ++ flRadExtra ++
ext`. The list `flRadExtra` puts the primitives of T2 at indices `7`–`10`:
**MinimalBlocks** `7`, **DerivedSubgroup** `8`, **NormalClosure** `9`,
**NormalizedIntersection** `10`. **Membership** is `1`, **Preimage** is `2`, and **GroupOrder**
is `5` (from `gsExtra`).

`fl_radAt`: the layout `OutbRadAt` holds at `rlb rlRadOff` in
`asmProg … (gsExtra … ++ (flRadExtra … ++ ext)) gen (rlRow flRad cos) agg`, for every `ext`,
`gen`, `cos` and `agg` that fit their slots. `fl_termRadSpec` is then `outbRad_termRadSpec`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val PointwiseStab Preimage NormalizedFactor Membership MinimalBlocks GroupOrder
  CameronRecognition NormalClosure DerivedSubgroup NormalizedIntersection)

set_option maxRecDepth 100000

/-- The primitives of T2 at indices `7`–`10` of the final table. -/
noncomputable def flRadExtra (hder : DerivedSubgroup)
    (hni : NormalizedIntersection) : List Prim :=
  [minimalBlocksPrim GI.Proved.minimalBlocks, derivedSubgroupPrim hder,
   normalClosurePrim GI.Proved.normalClosure, normalizedIntersectionPrim hni]

/-- The code of T2 in the row slot `rad`: base `rlb rlRadOff`, primitives `7, 2, 1, 9, 10, 8, 5`. -/
def flRad : List Expr := outbRadFuns (rlb rlRadOff) 7 2 1 9 10 8 5

theorem length_flRad : flRad.length ≤ rlCosOff - rlRadOff := by
  rw [flRad, length_outbRadFuns]; unfold rlCosOff rlRadOff; omega

/-- The constant of the cost bound of T2 (`outbRadK` of the primitives). -/
noncomputable def flRadK (hder : DerivedSubgroup)
    (hni : NormalizedIntersection) (hm : Membership) (hpre : Preimage) (hO : GroupOrder) : ℕ :=
  outbRadK (tcChainPrim GI.Proved.minimalBlocks hpre hm GI.Proved.normalClosure hni hder)
    (derivedSubgroupPrim hder) (gmpFactorKernelPrim hm hpre)
    (normalizedIntersectionPrim hni) (membershipPrim hm) (gmpRepsPrim hm)
    (normalClosurePrim GI.Proved.normalClosure) (groupOrderPrim hO)

/-- The exponent of the cost bound of T2 (`outbRadD` of the primitives). -/
noncomputable def flRadD (hder : DerivedSubgroup)
    (hni : NormalizedIntersection) (hm : Membership) (hpre : Preimage) (hO : GroupOrder) : ℕ :=
  outbRadD (tcChainPrim GI.Proved.minimalBlocks hpre hm GI.Proved.normalClosure hni hder)
    (derivedSubgroupPrim hder) (gmpFactorKernelPrim hm hpre)
    (normalizedIntersectionPrim hni) (membershipPrim hm) (gmpRepsPrim hm)
    (normalClosurePrim GI.Proved.normalClosure) (groupOrderPrim hO)

section Asm

variable {hst : PointwiseStab} {hm : Membership} {hpre : Preimage} {hfac : NormalizedFactor}
  {hmb : MinimalBlocks} {hO : GroupOrder} {hC : CameronRecognition}
  {hder : DerivedSubgroup} {hni : NormalizedIntersection}
  {ext : List Prim} {gen cos agg : List Expr}

/-- **The layout `OutbRadAt` of T2 in the final program.** -/
theorem fl_radAt (hg : gen.length ≤ asmSlot) (hc : cos.length ≤ asmSlot - rlCosOff) :
    OutbRadAt (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ (flRadExtra hder hni ++ ext))
        gen (rlRow flRad cos) agg)
      (rlb rlRadOff) 7 2 1 9 10 8 5
      GI.Proved.minimalBlocks hpre hm GI.Proved.normalClosure hni hder hO :=
  outbRadAt_of (rl_hasAt_rad hg length_flRad hc) rfl rfl rfl rfl rfl rfl rfl

/-- **T2 in the final program**: `TermRadSpec` at `rlb rlRadOff` (`outbRad_termRadSpec`). -/
theorem fl_termRadSpec
    (hg : gen.length ≤ asmSlot) (hc : cos.length ≤ asmSlot - rlCosOff) :
    Iface.TermRadSpec
      (asmProg hst hm hpre hfac (gsExtra hmb hO hC ++ (flRadExtra hder hni ++ ext))
        gen (rlRow flRad cos) agg)
      (flRadK hder hni hm hpre hO) (flRadD hder hni hm hpre hO) (rlb rlRadOff) :=
  outbRad_termRadSpec (fl_radAt hg hc)

end Asm

end GI.Impl
