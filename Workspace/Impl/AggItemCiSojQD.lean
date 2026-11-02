import Workspace.Impl.AggItemCiSojQuery
import Workspace.Impl.AggItemC1Dat

/-!
# The inherited query domain on the original positions

A nonzero cell code is active only when the position belongs to the parent's
active domain. This intersection is part of `RectRep.Δ` and is retained explicitly.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

open Classical in
/-- The two stored tables used to construct the inherited domain. -/
noncomputable def itcsDomCtx (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R) : Val :=
  .list [encFun (fun i => if e.symm i ∈ S.dom then 1 else 0),
    encFun (fun i => rcCellCode (rep.cell (e.symm i)))]

/-- On `[[parent domain, cells], i]`, the indicator of the actual inherited domain. -/
def itcsDomB : Expr :=
  .arith .mul (.get (.get (arg 0) (.nat 0)) (arg 1))
    (.arith .lt (.nat 0) (.get (.get (arg 0) (.nat 1)) (arg 1)))

open Classical in
/-- One query-domain indicator. -/
theorem itcs_domB_spec {Pg : Program} {f Bw : ℕ}
    (hf : Pg.funs[f]? = some itcsDomB) (e : Ω ≃ Fin k)
    (rep : RectRep P₀ S L W R) (i : Fin k)
    (hin : (Val.list [itcsDomCtx e rep, .nat i]).wt ≤ Bw) (h5 : 5 ≤ Bw) :
    FunDet Pg f (.list [itcsDomCtx e rep, .nat i])
      (.nat (if e.symm i ∈ rep.Δ then 1 else 0)) (40 * (Bw + 1)) := by
  let dv := encFun (fun i : Fin k => if e.symm i ∈ S.dom then 1 else 0)
  let cv := encFun (fun i : Fin k => rcCellCode (rep.cell (e.symm i)))
  let env := [Val.list [itcsDomCtx e rep, .nat i]]
  have hctx : (itcsDomCtx e rep).wt ≤ Bw := (st_wt_mem (by simp)).trans hin
  have hdv : dv.wt ≤ Bw := (st_wt_mem (List.mem_cons_self ..)).trans hctx
  have hcv : cv.wt ≤ Bw := (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans hctx
  have hdi : (Val.nat (if e.symm i ∈ S.dom then 1 else 0)).wt ≤ Bw := by
    split_ifs <;> exact (wt_nat_le _).trans (by omega)
  have hci : (Val.nat (rcCellCode (rep.cell (e.symm i)))).wt ≤ Bw :=
    (st_wt_mem (List.mem_of_getElem? (encFun_getElem?
      (fun j => rcCellCode (rep.cell (e.symm j))) i))).trans hcv
  have a0 : StDC Pg env (arg 0) (itcsDomCtx e rep) 3 0 Bw := StDC.arg rfl hin (by omega) hctx
  have a1 : StDC Pg env (arg 1) (.nat i) 3 0 Bw :=
    StDC.arg rfl hin (by omega) ((st_wt_mem (by simp)).trans hin)
  have dtab := StDC.get a0 (StDC.nat 0 (by omega)) rfl hdv
  have ctab := StDC.get a0 (StDC.nat 1 (by omega)) rfl hcv
  have di := StDC.get dtab a1 (encFun_getElem? (fun j => if e.symm j ∈ S.dom then 1 else 0) i) hdi
  have ci := StDC.get ctab a1 (encFun_getElem? (fun j => rcCellCode (rep.cell (e.symm j))) i) hci
  have lt := StDC.arith' (StDC.nat 0 (by omega)) ci (op := .lt)
    (z := if 0 < rcCellCode (rep.cell (e.symm i)) then 1 else 0) rfl
    (by split_ifs <;> omega)
  have hm : Machine.BinOp.mul.eval (if e.symm i ∈ S.dom then 1 else 0)
      (if 0 < rcCellCode (rep.cell (e.symm i)) then 1 else 0) =
        (if e.symm i ∈ rep.Δ then 1 else 0) := by
    cases he : rep.cell (e.symm i) with
    | none => simp [Machine.BinOp.eval, rcCellCode, RectRep.Δ, he]
    | some c => simp [Machine.BinOp.eval, rcCellCode, RectRep.Δ, he]
  have out := StDC.arith' di lt (op := .mul) hm (by split_ifs <;> omega)
  exact StDC.funDet hf out (by omega)

open Classical in
/-- The complete inherited-domain table, with no change of physical positions. -/
theorem itcs_dom_table {Pg : Program} {mp f Bw : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]? = some itcsDomB)
    (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R) (hk : 1 ≤ k)
    (hin : ∀ i : Fin k, (Val.list [itcsDomCtx e rep, .nat i]).wt ≤ Bw) (h5 : 5 ≤ Bw) :
    FunDet Pg mp (.list [itcsDomCtx e rep, natList (List.range k)])
      (encFun fun i => if e.symm i ∈ rep.Δ then 1 else 0)
      (k * (40 * (Bw + 1)) + mapK * (k + 1) *
        (2 * (itcsDomCtx e rep).wt + 22 * (k + 1) ^ 2)) :=
  it_tab hm _ (fun i => by split_ifs <;> omega)
    (fun i => itcs_domB_spec hf e rep i (hin i) h5)

end GI.Impl
