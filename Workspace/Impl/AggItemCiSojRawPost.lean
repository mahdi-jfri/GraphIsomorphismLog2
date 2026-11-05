module

public import Workspace.Impl.AggItemCiSojDone
public import Workspace.Impl.AggItemCiSojBudgetStart

@[expose] public section

/-! # The raw finished branches meet the full start postcondition -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {Ω C : Type} {k : ℕ} {S : State Ω C} {L : SuppliedLabels S}

/-- The raw overcoset call already pays for its output. The outer start
expression's finished wrapper and output encoding fit one linear growth stage. -/
theorem itcs_raw_done_post {Pg : Program} {fn Cb f i : ℕ} (R : ItCfIRel)
    (e : Ω ≃ Fin k) (c : C → ℕ) (K : ItSCtx k S L)
    (b : Fin (P₀.κ+1) → Fin L.q) (oX oY : CfgOut L.q)
    (E : Set (ItCfCh S L.toGiantLabels)) (sb : ItCfCh S L.toGiantLabels → Script (Branches Ω))
    (ovs : List (Perm Ω × Subgroup (Perm Ω))) (os : List (LcOver L.q)) (inp : Val)
    (hK : R.Ki e c S L K (.list []) E) (hs : ∀ch∈E,sb ch=.done ⟨[],ovs⟩)
    (ho : ItSOut e L.toGiantLabels ⟨[],ovs⟩ [] os)
    (hp : FunDet Pg fn inp (itciOV os) Cb)
    (pf : Prim) (Bc Br : ℕ → ℕ) (hBc : PBU fun _ W _ => Bc W) (hBr : PBU fun _ W _ => Br W)
    (W : ℕ) (hi : i+1≤128) (hb : Cb≤(itcsGrow pf Bc Br hBc hBr)^[i] (W+100)) :
    ItCfIPost R e c S L K b oX oY E sb f (itcsXs pf Bc Br hBc hBr W) (itcsResV (itciOV os)) := by
  have wraw := (itcs_det_weight hp).trans hb
  have wout := (itcs_out_weight_le (k:=k) os).trans (itcs_res_weight (itciOV os))
  have hlinear : (itSOutV ([] : List (Perm (Fin k) × Acc k)) os).wt≤
      10^9*((itcsGrow pf Bc Br hBc hBr)^[i] (W+100)+100) := by omega
  exact itcs_done_post R e c K b oX oY E sb f _ ovs os hK hs ho
    ((itcs_budget_linear pf Bc Br hBc hBr W i hlinear).trans
      (itcs_budget_iter_le pf Bc Br hBc hBr W hi))

end GI.Impl
