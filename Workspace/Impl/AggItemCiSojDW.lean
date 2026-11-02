import Workspace.Impl.AggItemCiSojQD
import Workspace.Impl.AggItemCiSojPW

/-! # The inherited-domain map with all table and index bounds discharged -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- A common bit-reader budget for the inherited domain. -/
def itcsDomW (k q : ℕ) : ℕ := 100*(k*(q*q+10)+(k+1)^2+10)

/-- Cost of the complete physical-domain table. -/
def itcsDomC (k q : ℕ) : ℕ :=
  k*(40*(itcsDomW k q+1))+mapK*(k+1)*(100*(k*(q*q+10)+k+10)+22*(k+1)^2)

open Classical in
/-- The rectangle's cell table and parent's domain indicator meet every premise
of the literal inherited-domain program. -/
theorem itcs_dom_prog {Pg : Program} {mp f : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]? = some itcsDomB)
    (e : Ω ≃ Fin k) (rep : RectRep P₀ S L W R) (hk : 1≤ k) :
    FunDet Pg mp (.list [itcsDomCtx e rep,natList (List.range k)])
      (encFun fun i=>if e.symm i∈rep.Δ then 1 else 0) (itcsDomC k L.q) := by
  have hd:=wt_encFun_le (fun i:Fin k=>if e.symm i∈S.dom then 1 else 0)
    (B:=1) (by intro i; dsimp only; split_ifs <;> omega)
  have hcell:=wt_encFun_le (fun i:Fin k=>rcCellCode (rep.cell (e.symm i)))
    (fun i=>itcs_cell_code_le (rep.cell (e.symm i)))
  have hcell' : (encFun fun i:Fin k=>rcCellCode (rep.cell (e.symm i))).wt≤10*(k*(L.q*L.q+10))+4 := by
    calc _ ≤ k*(2*(L.q*L.q+1)+5)+4 := hcell
      _ ≤ k*(10*(L.q*L.q+10))+4 := Nat.add_le_add_right (Nat.mul_le_mul_left k (by omega)) 4
      _ = _ := by ring
  have hctx:=wt_list2_le (encFun fun i:Fin k=>if e.symm i∈S.dom then 1 else 0)
    (encFun fun i:Fin k=>rcCellCode (rep.cell (e.symm i)))
  have hc : (itcsDomCtx e rep).wt≤50*(k*(L.q*L.q+10)+k+10) := by
    dsimp only [itcsDomCtx]
    omega
  have hkp : k+1≤(k+1)^2 := Nat.le_self_pow (by omega) _
  have hin (i:Fin k) : (Val.list [itcsDomCtx e rep,.nat i]).wt≤ itcsDomW k L.q := by
    have hh:=wt_list2_le (itcsDomCtx e rep) (.nat i)
    have hi:=wt_nat_le (i:ℕ)
    have hlt:=i.isLt
    unfold itcsDomW
    have hc' : (itcsDomCtx e rep).wt≤
      20*(k*(L.q*L.q+10))+14*k+22 := by
      dsimp only [itcsDomCtx]
      omega
    omega
  have h:=itcs_dom_table hm hf e rep hk hin (by unfold itcsDomW; omega)
  refine h.mono ?_
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  omega

/-- Polynomial round bound of the inherited-domain construction. -/
theorem itcs_dom_pbu : PBU fun _ W _=>itcsDomC W (2*W+3) := by
  simp only [itcsDomC,itcsDomW,mapK]
  norm_poly

end GI.Impl
