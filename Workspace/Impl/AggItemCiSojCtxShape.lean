import Workspace.Impl.AggItemCiSojParentBudget

/-! # Reading the supplied context at rectangle construction calls -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)
open Classical

variable {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {c : C → ℕ}
  {S : State Ω C} {L : SuppliedLabels S} {K : ItSCtx k S L}

/-- Canonical parent bytes supply exactly the physical degree, inherited domain,
hierarchy and original input-size fields read by the query encoders. -/
theorem itcs_ctx_shape (hK : K.OK e c) :
    ∃ (sv : List Val) (hier : Val), K.sv=.list sv ∧ sv[0]?=some (.nat k) ∧
      sv[2]?=some (encFun fun i => if e.symm i∈S.dom then 1 else 0) ∧
      sv[5]?=some hier ∧ sv[9]?=some (.nat S.N) ∧ HierValC e hier S.hier := by
  obtain ⟨gv,dv,xv,yv,hv,rv,hg,hd,hx,hy,hh,hr,he⟩ := hK.can.val
  refine ⟨[.nat k,gv,dv,xv,yv,hv,rv,boolVal S.floor,.nat S.h,.nat S.N],hv,he,rfl,?_,rfl,rfl,hh⟩
  change some dv=some _
  exact congrArg some hd

/-- The stored graph generators are a subvalue of the supplied item context.
Their raw weight is therefore already covered by the parent context bound. -/
theorem itcs_ctx_ps_weight (K : ItSCtx k S L) :
    (Val.list (K.ps.map pairV)).wt ≤ K.v.wt := by
  have hst : K.st.wt ≤ K.v.wt := st_wt_mem (List.mem_cons_self ..)
  have hps : (Val.list (K.ps.map pairV)).wt ≤ K.st.wt :=
    st_wt_mem (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  exact hps.trans hst

end GI.Impl
