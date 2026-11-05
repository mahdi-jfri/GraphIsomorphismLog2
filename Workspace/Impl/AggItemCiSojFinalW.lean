module

public import Workspace.Impl.AggItemCiSojFinalB
public import Workspace.Impl.AggItemCiSojEncodedRows
public import Workspace.Impl.AggItemCiSojOV

@[expose] public section

/-! # All argument sizes of the full rectangle finalizer -/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Rectangle Equiv Equiv.Perm
open GI.Cited (Val encPerm)

/-- Fixed padding bounds both a stage input and its paid-for result. -/
theorem itcs_pad_bounds (x c : ℕ) : x ≤ 10*(x+c+100) ∧ c ≤ 10*(x+c+100) ∧ 100 ≤ 10*(x+c+100) := by omega

/-- Each finalizer stage bounds all data carried from the preceding stages. -/
theorem itcs_final_envelopes (pf : Prim) (W : ℕ) :
    W ≤ itcsFinalU0 pf W ∧ itcsRowsBound pf W ≤ itcsFinalU0 pf W ∧
    itcsFinalU0 pf W ≤ itcsFinalU1 pf W ∧ itcsFilterB (itcsFinalU0 pf W) ≤ itcsFinalU1 pf W ∧
    itcsFinalU1 pf W ≤ itcsFinalU2 pf W ∧ itcsFirstB (itcsFinalU1 pf W) ≤ itcsFinalU2 pf W ∧
    itcsFinalU2 pf W ≤ itcsFinalU3 pf W ∧ itcsGroupBuildC (10*itcsFinalU2 pf W+10) ≤ itcsFinalU3 pf W ∧
    itcsFinalU3 pf W ≤ itcsFinalU4 pf W ∧ itcsOverB (itcsFinalU3 pf W) ≤ itcsFinalU4 pf W := by
  have h0 := itcs_pad_bounds W (itcsRowsBound pf W)
  have h1 := itcs_pad_bounds (itcsFinalU0 pf W) (itcsFilterB (itcsFinalU0 pf W))
  have h2 := itcs_pad_bounds (itcsFinalU1 pf W) (itcsFirstB (itcsFinalU1 pf W))
  have h3 := itcs_pad_bounds (itcsFinalU2 pf W) (itcsGroupBuildC (10*itcsFinalU2 pf W+10))
  have h4 := itcs_pad_bounds (itcsFinalU3 pf W) (itcsOverB (itcsFinalU3 pf W))
  exact ⟨h0.1,h0.2.1,h1.1,h1.2.1,h2.1,h2.2.1,h3.1,h3.2.1,h4.1,h4.2.1⟩

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}
  {W R : Finset (Fin L.q)}

/-- Dropping empty rows cannot increase the number of query occurrences. -/
theorem itcs_nonempty_length_le (rep : RectRep P₀ S L W R)
    (rows : List (permitted W R × itcsProcessRow rep)) :
    (itcsNonemptyRows rep rows).length ≤ rows.length := List.length_filterMap_le _ rows

/-- The alignment table records the actual label degree, and every stored
payload component fits the finalizer's actual input weight. -/
theorem itcs_final_input_weights {q : ℕ} (a : Perm (Fin q)) (qv fix ctx twists answers : Val) :
    let payload := Val.list [qv,encPerm a,fix,ctx,twists]
    let inp := Val.list [payload,answers]
    q ≤ inp.wt ∧ fix.wt ≤ inp.wt ∧ ctx.wt ≤ inp.wt ∧ (encPerm a).wt ≤ inp.wt := by
  dsimp only
  let payload := Val.list [qv,encPerm a,fix,ctx,twists]
  let inp := Val.list [payload,answers]
  have hp : payload.wt ≤ inp.wt := st_wt_mem (List.mem_cons_self ..)
  have ha : (encPerm a).wt ≤ inp.wt := (st_wt_mem (by simp)).trans hp
  have hf : fix.wt ≤ inp.wt := (st_wt_mem (by simp)).trans hp
  have hc : ctx.wt ≤ inp.wt := (st_wt_mem (by simp)).trans hp
  exact ⟨(itcs_perm_degree a).trans ha,hf,hc,ha⟩

/-- Bounding every overcoset entry bounds the complete encoded result list. -/
theorem itcs_over_output_weight {q n : ℕ} (a : Perm (Fin q)) (rs ms : List (Perm (Fin q)))
    (hq : q≤ n) (hr : rs.length≤ n) (hm : (Val.list (ms.map encPerm)).wt≤ n) :
    (Val.list (rs.map fun r => lcOv (a*r) ms)).wt ≤
      n*(2*(2*(4*(n+1)^2+n)+6)+1)+4 := by
  have he (r : Perm (Fin q)) : (lcOv (a*r) ms).wt ≤ 2*(4*(n+1)^2+n)+6 := by
    have hp := (wt_encPerm_le (a*r)).trans (Nat.mul_le_mul_left 4
      (Nat.pow_le_pow_left (Nat.add_le_add_right hq 1) 2))
    have hh := wt_list2_le (encPerm (a*r)) (.list (ms.map encPerm))
    change (Val.list [encPerm (a*r),.list (ms.map encPerm)]).wt ≤ _
    omega
  exact (wt_list_map_le rs (fun r => lcOv (a*r) ms) (fun r _ => he r)).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hr) 4)

/-- The exact overcoset mapper cost fits its scalar local-input bound. -/
theorem itcs_over_bound {q n : ℕ} (a : Perm (Fin q)) (rs ms : List (Perm (Fin q)))
    (hq : q≤ n) (hr : rs.length≤ n) (hm : (Val.list (ms.map encPerm)).wt≤ n)
    (hi : (Val.list [.list [encPerm a,.list (ms.map encPerm)],.list (rs.map encPerm)]).wt≤ n) :
    rs.length*(50*(itcsOverW q ms+1)+permK*(q+1)^3)+mapK*(rs.length+1)*
      ((Val.list [.list [encPerm a,.list (ms.map encPerm)],.list (rs.map encPerm)]).wt+
        (Val.list (rs.map fun r => lcOv (a*r) ms)).wt+1) ≤ itcsOverB n := by
  have ho := itcs_over_output_weight a rs ms hq hr hm
  unfold itcsOverW itcsOverB
  gcongr

end GI.Impl
