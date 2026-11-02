import Workspace.Impl.AggItemCiSojAnswers

/-! # A polynomial cost for processing the full answer list -/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-- The scalar form of the map bound, at local input weight `W`. -/
def itcsRowsBound (pf : Prim) (W : ℕ) : ℕ :=
  let Cr := itcsProcessC pf (10*(W+10))
  let Bw := 100*(10*(W+W+10)+Cr+10)
  50*(100*(Bw+W*(2*Cr+1)+4*(W+1)^2+W+100)+1)+7000*(W+1)^3+
    (W*(50*(Bw+1)+Cr)+mapK*(W+1)*
      (2*W+8*(W+1)^2+6+(W*(2*Cr+1)+4)+1))

/-- The number of answers is bounded by their encoded list's input weight. -/
theorem itcs_answers_length (payload : Val) (answers : List Val) :
    answers.length ≤ (Val.list [payload,.list answers]).wt :=
  (length_lt_wt_list answers).le.trans
    (st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_self ..)))

/-- The actual map cost fits the scalar bound without assuming at most two rows. -/
theorem itcs_rows_bound (pf : Prim) (v : Val) {n : ℕ} (hn : n ≤ v.wt) :
    itcsRowsC v n (itcsProcessC pf (10*(v.wt+10))) ≤ itcsRowsBound pf v.wt := by
  unfold itcsRowsC itcsRowsMC itcsRowsBW itcsRowsBound
  dsimp only
  gcongr

/-- Processing all saved answers costs a polynomial of the actual input weight. -/
theorem itcs_answers_pbu (pf : Prim) : PBU fun _ W _ => itcsRowsBound pf W := by
  simp only [itcsRowsBound,itcsProcessC,itcsProjectB,itcsProjU,itcsLiftB,
    itcsGroupMapB,itcsGenMapB,liftLabCost,liftLabK,mapK,permK]
  norm_poly

end GI.Impl
