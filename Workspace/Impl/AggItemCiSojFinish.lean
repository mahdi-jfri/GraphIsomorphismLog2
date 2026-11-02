import Workspace.Impl.AggItemCiSojRes
import Workspace.Impl.AggItemCiSojRF
import Workspace.Impl.AggItemCiSojOV

/-!
# The rectangle answer finalizer

Project all saved answers, drop only empty rows, and collect their representatives.
If no row remains, return the empty item. Otherwise rebuild the full generator
list and encode all overcosets with the fixed alignment.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang
open GI.Cited (Val)

/-- Read the metadata retained by the two-query continuation. -/
def itcsFinPayload (i : ℕ) : Expr := .get (arg 0) (.nat i)

/-- Finalize the nonempty rows after projection and filtering. -/
def itcsFinishBody (fst gb ovs : ℕ) : Expr :=
  .letE (.call fst (mk2 (.nat 0) (.var 2)))
    (.letE (.call gb (mk3 (.var 3)
      (.get (.get (.get (.var 2) (.nat 0)) (.nat 1)) (.nat 1)) (itcsFinPayload 2)))
      (.letE (.call ovs (mk2 (mk2 (itcsFinPayload 1) (.var 4)) (.var 3)))
        (itcsResE (.var 5))))

/-- The actual finalizer on `[payload,canonical answers]`. -/
def itcsFinishF (rows flt fst gb ovs : ℕ) : Expr :=
  .letE (.call rows (.var 0))
    (.letE (.call flt (mk2 (.nat 0) (.var 1)))
      (.ite (.length (.var 2)) (itcsFinishBody fst gb ovs) (itcsResE .nil)))

/-- If every projected row is empty, return the exact empty finished item. -/
theorem itcs_finish_empty {Pg : Program} {f rows flt fst gb ovs Cr Cf : ℕ}
    (hf : Pg.funs[f]? = some (itcsFinishF rows flt fst gb ovs))
    (v : Val) (rs : List Val)
    (hr : FunDet Pg rows v (.list rs) Cr)
    (hflt : FunDet Pg flt (.list [.nat 0,.list rs]) (.list []) Cf) :
    FunDet Pg f v (itcsResV (.list []))
      (50*(100*(v.wt+Cr+Cf+100)+1)+Cr+Cf) := by
  let Bw:=100*(v.wt+Cr+Cf+100)
  have budget : 10*v.wt+10*Cr+10*Cf+1000≤Bw := by dsimp only [Bw]; omega
  have wr:=itcs_det_weight hr
  have wo : (itcsResV (.list [])).wt≤Bw :=
    (itcs_res_weight (.list [])).trans (by simp only [wt_list_nil]; omega)
  have v0 : StDC Pg [v] (.var 0) v 1 0 Bw := StDC.var' rfl (by omega)
  have rc:=StDC.call v0 hr (wr.trans (by omega))
  have r1 : StDC Pg [v,.list rs] (.var 1) (.list rs) 1 0 Bw := StDC.var' rfl (wr.trans (by omega))
  have wa : (Val.list [.nat 0,.list rs]).wt≤Bw := by
    have hh:=wt_list2_le (.nat 0) (.list rs)
    have hz:=wt_nat_le 0
    omega
  have fc:=StDC.call (StDC.mk2 (StDC.nat 0 (by omega)) r1 wa (by omega)) hflt (by simp only [wt_list_nil]; omega)
  have e2 : StDC Pg [v,.list rs,.list []] (.var 2) (.list []) 1 0 Bw :=
    StDC.var' rfl (by simp only [wt_list_nil]; omega)
  have len : StDC Pg [v,.list rs,.list []] (.length (.var 2)) (.nat 0) 2 0 Bw :=
    StDC.length e2 (by change 0+2≤Bw; omega)
  have nils:=itcs_res_dc (StDC.nil (P:=Pg) (env:=[v,.list rs,.list []]) (by omega)) wo (by omega)
  have tail:=StDC.ite (t:=itcsFinishBody fst gb ovs) (nt:=1) (ne:=11) (Et:=0) (Ee:=0) len
    (fun h=>by omega) (fun _=>nils.mono (by omega) (by omega)) wo
  have body:=StDC.letE rc (StDC.letE fc tail wo) wo
  exact StDC.funDet hf body (by dsimp only [Bw]; omega)

end GI.Impl
