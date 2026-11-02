import Workspace.Impl.AggItemCiSojPT
import Workspace.Impl.AggItemCiSojBP
import Workspace.Impl.AggItemCiSojTW

/-! # Rectangle color pullback with all palette and cell-code bounds discharged -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {q k : ℕ} {W R : Finset (Fin q)}

/-- Every stored cell code is bounded by the square label degree. -/
theorem itcs_cell_code_le (c : Option (W×R)) : rcCellCode c≤ q*q+1 := by
  cases c with
  | none => simp only [rcCellCode]; omega
  | some c =>
    have hm:=Nat.mul_le_mul_right q (Nat.succ_le_of_lt c.1.val.isLt)
    have hr:=c.2.val.isLt
    simp only [Nat.succ_mul] at hm
    change 1+(c.1.val:ℕ)*q+(c.2.val:ℕ)≤ q*q+1
    omega

/-- Common budget for one literal pulled-back bit. -/
def itcsPullW (q B : ℕ) : ℕ :=
  100*(itCfObjB q B+B+(q+1)^2+q*q+q+10)

/-- Full pullback-table cost on the original `k` positions. -/
def itcsPullC (k q B : ℕ) : ℕ :=
  k*(200*(itcsPullW q B+1))+mapK*(k+1)*
    (100*(itCfObjB q B+B+(q+1)^2+q+k*(q*q+10)+10)+9*k+5)

/-- Both literal-reader argument bounds follow from the object palette. -/
theorem itcs_pull_weights (X : PairCfg q) (x₀ : Fin q) {B v : ℕ}
    (hcol : itCfColsLe (.pair X x₀) B) (hv : v≤ B) (p : Perm (Fin q)) (cell : Option (W×R)) :
    (Val.list [itcsPullCtx X v p,.nat (rcCellCode cell)]).wt≤ itcsPullW q B ∧
      (Val.list [rcColVal X,.nat v,.nat q,.nat (rcCellCode cell),encPerm p]).wt≤ itcsPullW q B ∧
      q*q+q+10≤ itcsPullW q B := by
  have ht : (rcColVal X).wt≤ itCfObjB q B :=
    (st_wt_mem (List.mem_cons_self ..)).trans
      ((st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans (itCfOutV_wt_le hcol))
  have vp:=wt_nat_le v
  have qp:=wt_nat_le q
  have cp:=(wt_nat_le (rcCellCode cell)).trans (Nat.add_le_add_right (itcs_cell_code_le cell) 2)
  have pp:=wt_encPerm_le p
  have wc:=wt_list4_le (rcColVal X) (.nat v) (.nat q) (encPerm p)
  have wi:=wt_list2_le (itcsPullCtx X v p) (.nat (rcCellCode cell))
  have wf:=itcs_wt_list5 (rcColVal X) (.nat v) (.nat q) (.nat (rcCellCode cell)) (encPerm p)
  simp only [itcsPullCtx] at *
  unfold itcsPullW
  omega

/-- The complete color-table map has only the source object's palette and edge
color bound as mathematical preconditions. -/
theorem itcs_pull_prog {Pg : Program} {mp f pull B : ℕ}
    (hm : Pg.HasAt mp (mapFuns mp f)) (hf : Pg.funs[f]? = some (itcsPullB pull))
    (hp : Pg.funs[pull]? = some itcsPullF)
    (X : PairCfg q) (x₀ : Fin q) (hcol : itCfColsLe (.pair X x₀) B)
    (v : ℕ) (hv : v≤ B) (p : Perm (Fin q)) (cells : Fin k→Option (W×R)) :
    FunDet Pg mp (.list [itcsPullCtx X v p,encFun fun i=>rcCellCode (cells i)])
      (encFun fun i=>itcsQCode ((cells i).map fun c=>decide (X.col (p c.1.val) (p c.2.val)=v)))
      (itcsPullC k q B) := by
  have ht:=itcs_pull_table hm hf hp X v p cells
    (fun i=>(itcs_pull_weights X x₀ hcol hv p (cells i)).1)
    (fun i=>(itcs_pull_weights X x₀ hcol hv p (cells i)).2.1)
    (by unfold itcsPullW; omega)
  have wcol : (rcColVal X).wt≤ itCfObjB q B :=
    (st_wt_mem (List.mem_cons_self ..)).trans
      ((st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..))).trans (itCfOutV_wt_le hcol))
  have wv:=wt_nat_le v
  have wq:=wt_nat_le q
  have wp:=wt_encPerm_le p
  have wc:=wt_list4_le (rcColVal X) (.nat v) (.nat q) (encPerm p)
  have wcell:=wt_encFun_le (fun i=>rcCellCode (cells i)) (fun i=>itcs_cell_code_le (cells i))
  have wcell' : (encFun fun i=>rcCellCode (cells i)).wt ≤ 10*(k*(q*q+10))+4 := by
    calc _ ≤ k*(2*(q*q+1)+5)+4 := wcell
      _ ≤ k*(10*(q*q+10))+4 := Nat.add_le_add_right (Nat.mul_le_mul_left k (by omega)) 4
      _ = _ := by ring
  have wi:=wt_list2_le (itcsPullCtx X v p) (encFun fun i=>rcCellCode (cells i))
  simp only [itcsPullCtx] at *
  refine ht.mono ?_
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_left
  omega

/-- Polynomial round cost for the complete physical color pullback. -/
theorem itcs_pull_pbu : PBU fun _ W _=>itcsPullC W (2*W+3) (2*(2*W+3)^64) := by
  simp only [itcsPullC,itcsPullW,itCfObjB,mapK]
  norm_poly

end GI.Impl
