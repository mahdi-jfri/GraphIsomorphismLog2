module

public import Workspace.Impl.AggItemHvInitP
public import Workspace.Impl.AggItemOKC1
public import Workspace.Impl.AggBodyKr

@[expose] public section

/-!
# Case 2a: the bounds are polynomial

The init program of Case 2a meets `ItHvInitOK` with the bound `itHvIX pf pst krC`
(`it_hvInitOK`). With the module `kr` of the layout (`krFuns`, cost `abKrC hst`, `ab_krOK`), this
bound is polynomial in `W₀` (`itHvIX_pbu`), and so is the bound `itHvX` of the whole case
(`itHvX_pbu`).
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (PointwiseStab)

/-- **The bound of the Case 2a init program is polynomial.** -/
theorem itHvIX_pbu (pf : Prim) (hst : PointwiseStab) :
    PBU fun _ W _ => itHvIX pf (pointwiseStabPrim hst) (abKrC hst) W := by
  simp only [itHvIX, itHvIC, itHvIP, itHvPreC, itGrpC, itDomC, itHvIMC, itHvDaC, itHvIL,
    itHvLtC, liftLabCost, itHvKgC, abKrC, Prim.boundSize, itHvOutC, itHvIMo, itHvIBK, itHvMK,
    itHvIMd, itSVB, cmOutB, cmPb, cmNb]
  norm_poly

/-- **The bound of Case 2a is polynomial.** -/
theorem itHvX_pbu (pf : Prim) (hst : PointwiseStab) :
    PBU fun _ W _ => itHvX (itHvIX pf (pointwiseStabPrim hst) (abKrC hst)) W := by
  simp only [itHvX, itHvB3C, itHvPcC, itHvBC, itHvRB, itHvBu, itHvIX, itHvIC, itHvIP, itHvPreC,
    itGrpC, itDomC, itHvIMC, itHvDaC, itHvIL, itHvLtC, liftLabCost, itHvKgC, abKrC,
    Prim.boundSize, itHvOutC, itHvIMo, itHvIBK, itHvMK, itHvIMd, itSVB, cmOutB, cmPb, cmNb]
  norm_poly

end GI.Impl
