import Workspace.Impl.LinPrimaryInstance

/-! An executable transporter for one primary layer, starting from retained
full affine records and using VectorStabilizer only at its parameter index. -/
namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 16000

theorem linPrimaryInputCost_mono {W V j k : ℕ} (hW : W ≤ V) (hj : j ≤ k) :
    linPrimaryInputCost W j ≤ linPrimaryInputCost V k := by
  have hq : linPrimaryInputPowerBudget W j ≤ linPrimaryInputPowerBudget V k := by
    unfold linPrimaryInputPowerBudget linNatPowerCost
    gcongr
  have hra : linPrimaryInputRecordsArg W j ≤ linPrimaryInputRecordsArg V k := by
    unfold linPrimaryInputRecordsArg
    omega
  have hr : linPrimaryInputRecordsBudget W j ≤ linPrimaryInputRecordsBudget V k :=
    linPrimaryRecordsCost_mono hra
  have ha : linPrimaryInputArg W j ≤ linPrimaryInputArg V k := by
    unfold linPrimaryInputArg
    omega
  have hp : linPrimaryInputProjectBudget W j ≤ linPrimaryInputProjectBudget V k := linProjectCost_mono ha
  have hv : linPrimaryInputVectorBudget W j ≤ linPrimaryInputVectorBudget V k := linPrimaryVectorCost_mono ha hW
  unfold linPrimaryInputCost
  omega

theorem linAffineTransportCost_mono (h : VectorStabilizer) {W V : ℕ} (hw : W ≤ V) :
    linAffineTransportCost h W ≤ linAffineTransportCost h V := by
  have hi := linAffineInputCost_mono hw
  have hv : linAffineTransportVectorCost h W ≤ linAffineTransportVectorCost h V := by
    unfold linAffineTransportVectorCost
    gcongr
  unfold linAffineTransportCost
  omega

def linPrimaryTransportF (input affine : ℕ) : Expr :=
  .letE (.call input (arg 0)) (.call affine (mk2 (.var 1) (arg 1)))

def linPrimaryTransportFuns (b j : ℕ) : List Expr :=
  [linPrimaryTransportF (b + 1) (b + 117)] ++
    linPrimaryInputFuns (b + 1) ++ linAffineTransportFuns (b + 117) j

theorem linPrimaryTransportFuns_length (b j : ℕ) : (linPrimaryTransportFuns b j).length = 229 := by
  simp only [linPrimaryTransportFuns, List.length_append, List.length_singleton,
    linPrimaryInputFuns_length, linAffineTransportFuns_length]

structure linPrimaryTransportAt (P : Program) (b j : ℕ) (h : VectorStabilizer) : Prop where
  entry : P.funs[b]? = some (linPrimaryTransportF (b + 1) (b + 117))
  input : linPrimaryInputAt P (b + 1)
  affine : linAffineTransportAt P (b + 117) j h

theorem linPrimaryTransportAt_of (h : VectorStabilizer) {P : Program} {b j : ℕ}
    (hp : P.HasAt b (linPrimaryTransportFuns b j))
    (hj : P.prims[j]? = some (vectorStabilizerPrim h)) : linPrimaryTransportAt P b j h where
  entry := (hp.block (gs := [linPrimaryTransportF (b + 1) (b + 117)]) 0 rfl).single
  input := linPrimaryInputAt_of (hp.block 1 rfl)
  affine := linAffineTransportAt_of h (hp.block 117 rfl) hj

def linPrimaryTransportInputBudget (W level : ℕ) : ℕ := linPrimaryInputCost W level

def linPrimaryTransportArg (W level : ℕ) : ℕ := 100 * (W + linPrimaryTransportInputBudget W level + 1)
noncomputable def linPrimaryTransportAffineBudget (h : VectorStabilizer) (W level : ℕ) : ℕ :=
  linAffineTransportCost h (linPrimaryTransportArg W level)
noncomputable def linPrimaryTransportCost (h : VectorStabilizer) (W level : ℕ) : ℕ :=
  100000 * (W + linPrimaryTransportInputBudget W level + linPrimaryTransportAffineBudget h W level + 1)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 7000 in
theorem linPrimaryTransport_spec (h : VectorStabilizer) {P : Program} {b j n p d : ℕ}
    (hat : linPrimaryTransportAt P b j h) (gs : List (Equiv.Perm (Fin n)))
    (hs : IsSolvable (gens gs)) (hp : p.Prime) (hpn : p ≤ n) [NeZero n]
    (ν : Fin d → ℕ) (level : ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν))
    (hc : ∀ g k, c (g * k) = ρ g (c k) + c g)
    (hf : ∀ g, linPrimaryFiber p ν level (c g))
    (x : linFiniteVec (linPrimaryOrders p ν)) (w : Fin d → ZMod p) :
    let I := linPrimaryLayerInst gs hs hp hpn ν level ρ x
    let c' := fun g => linPrimaryCoord p ν level (c g)
    let hc' := linPrimaryLayer_cocycle gs hs hp hpn ν level ρ c hc hf x
    let a := Val.list [linPrimaryInputVal gs ν level ρ c x, encVec w]
    FunAll P b a (fun out cost => linAffineTransportOut I c' hc' w out ∧
      cost ≤ linPrimaryTransportCost h a.wt level) := by
  let I := linPrimaryLayerInst gs hs hp hpn ν level ρ x
  let c' := fun g => linPrimaryCoord p ν level (c g)
  let hc' := linPrimaryLayer_cocycle gs hs hp hpn ν level ρ c hc hf x
  let input := linPrimaryInputVal gs ν level ρ c x
  let a := Val.list [input, encVec w]
  let W := a.wt
  let data := linAffineLayerInput I c'
  let arg := Val.list [data, encVec w]
  letI : NeZero I.n := inferInstanceAs (NeZero n)
  have wi : input.wt < W := wt_le_wt_list (by simp [W, a])
  have ww : (encVec w).wt < W := wt_le_wt_list (by simp [W, a])
  have hd := (linPrimaryInput_layer_spec hat.input gs hs hp hpn ν level ρ c x).mono
    (linPrimaryInputCost_mono wi.le le_rfl)
  change FunDet P (b + 1) input data (linPrimaryTransportInputBudget W level) at hd
  have wd := hd.wt_lt.le
  have warg : arg.wt ≤ linPrimaryTransportArg W level := by
    have hh := wt_list2_le data (encVec w)
    unfold linPrimaryTransportArg
    dsimp only [arg]
    omega
  have ha : FunAll P (b + 117) arg (fun out cost => linAffineTransportOut I c' hc' w out ∧
      cost ≤ linPrimaryTransportAffineBudget h W level) :=
    FunAll.mono (linAffineTransport_spec h hat.affine I c' hc' w)
      (fun out cost ho => ⟨ho.1, ho.2.trans (linAffineTransportCost_mono h warg)⟩)
  have di := Det.call (Det.arg' (P := P) (vs := [input, encVec w]) (rest := []) (j := 0) rfl) hd
  have dw := Det.arg' (P := P) (vs := [input, encVec w]) (rest := [data]) (j := 1) rfl
  have da := Det.mk2 (Det.var' (P := P) (env := [a, data]) (i := 1) rfl) dw
  have call := normBound_call da ha
  apply FunAll.intro hat.entry
  apply EvalAll.letE di
  intro v cs hv
  obtain ⟨rfl, hcs⟩ := hv
  refine call.mono fun out cost ho => ⟨ho.1, ?_⟩
  have hcost := ho.2.2
  have wout := ho.2.1
  have wpair := wt_list2_le data (encVec w)
  change _ ≤ linPrimaryTransportCost h W level
  unfold linPrimaryTransportCost
  dsimp only [a, W, input, data, arg, I, c', hc'] at *
  omega

theorem linPrimaryTransportCost_poly (h : VectorStabilizer) :
    PBU (fun level W _ => linPrimaryTransportCost h W level) := by
  have hi : PBU (fun level W _ => linPrimaryTransportInputBudget W level) := linPrimaryInputCost_poly
  have ha : PBU (fun level W _ => linPrimaryTransportArg W level) :=
    PBU.smul 100 (PBU.addc (PBU.add PBU.W hi) 1)
  have ht : PBU (fun level W _ => linPrimaryTransportAffineBudget h W level) :=
    linPoly_subst (linAffineTransportCost_poly h) (PBU.const 0) ha (PBU.const 0)
  exact PBU.smul 100000 (PBU.addc (PBU.add (PBU.add PBU.W hi) ht) 1)

end GI.Impl
