import Workspace.Impl.LinIntSlpTrace

/-! Polynomial-cost SLP evaluation in integer exponent vectors. The table stores
shared entries, so an instruction never expands the word that it denotes. -/
set_option maxRecDepth 4000

namespace GI.Impl
open GI.Cited GI.Lang

/-- On [context,index,table], append the vector of the next instruction. -/
def linSlpLoopStep (step : ℕ) : Expr :=
  .snoc (arg 2) (.call step (mk3 (.get (arg 0) (.nat 0)) (arg 2)
    (.get (.get (arg 0) (.nat 1)) (arg 1))))

def linSlpFuns (b step : ℕ) : List Expr :=
  loopFuns b (.length (arg 1)) .nil (linSlpLoopStep step)

def linSlpStepArg (W L t : ℕ) : ℕ := 10 * (W + linSlpTableBudget L t + 1)
def linSlpLoopStepCost (W L t : ℕ) : ℕ :=
  1000 * (linSlpStepCost (linSlpStepArg W L t) t + W + L + linSlpTableBudget L t + 1)
def linSlpCost (W L t : ℕ) : ℕ :=
  L * linSlpLoopStepCost W L t + loopModK * (L + 1) * (W + L + linSlpTableBudget L t + 1)

set_option maxHeartbeats 2000000 in
theorem linSlp_spec {P : Program} {b step add scale ib t : ℕ}
    (hp : P.HasAt b (linSlpFuns b step))
    (hstep : P.funs[step]? = some (linSlpStepF add scale)) (hi : linIntSpec P ib)
    (ha : P.HasAt add (linVectorBinaryFuns add (ib + 11)))
    (hs : P.HasAt scale (linVectorScaleFuns scale ib))
    (gs : List (Multiplicative (Fin t → ℤ))) (hg : ∀ v ∈ gs, linExponentBound 1 v)
    (prog : List SlpInstr) (es : List (Multiplicative (Fin t → ℤ)))
    (hprog : linSlpEntries gs prog [] = some es) :
    FunDet P b (.list [linSlpTable gs, .list (prog.map encSlpInstr)]) (linSlpTable es)
      (linSlpCost (Val.list [linSlpTable gs, .list (prog.map encSlpInstr)]).wt prog.length t) := by
  let a := Val.list [linSlpTable gs, .list (prog.map encSlpInstr)]
  let W := a.wt
  let M := linSlpTableBudget prog.length t
  have wg : (linSlpTable gs).wt < W := wt_le_wt_list (by simp)
  have wp : (Val.list (prog.map encSlpInstr)).wt < W := wt_le_wt_list (by simp)
  have hacc (i : ℕ) : (linSlpTable (linSlpPrefix gs prog i)).wt ≤ M :=
    linSlpPrefix_wt gs hg prog es hprog i
  have h0 : linSlpTable (linSlpPrefix gs prog 0) = .list [] := rfl
  have hlast : linSlpPrefix gs prog prog.length = es := by simp [linSlpPrefix, hprog]
  have dl := Det.length (Det.arg' (P := P) (vs := [linSlpTable gs, .list (prog.map encSlpInstr)])
    (rest := []) (j := 1) rfl)
  simp only [List.length_map] at dl
  have hp' : P.HasAt b (loopFuns b (.length (arg 1)) .nil (linSlpLoopStep step)) := hp
  have hlp := loopBdd_spec hp' dl Det.nil (by
    change 2 * a.wt + 1 + 5 + prog.length + 3 + 5 ≤ 10 * (a.wt + prog.length + 1)
    have := a.two_le_size
    have := a.size_le_wt
    omega)
    (Inv := fun i acc => acc = linSlpTable (linSlpPrefix gs prog i)) (M := M)
    (D := fun _ => linSlpLoopStepCost W prog.length t) h0.symm
    (fun i acc _ he => he ▸ hacc i) (fun i acc hlt he => ?_)
  · refine hlp.mono fun out cost ho => ⟨?_, ?_⟩
    · simpa only [hlast] using ho.1
    · simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, linSlpCost] using ho.2
  · subst acc
    obtain ⟨x, hx, hnext⟩ := linSlpPrefix_step gs prog es hprog i hlt
    let prev := linSlpPrefix gs prog i
    have wprev : (linSlpTable prev).wt ≤ M := hacc i
    have wnext := hacc (i + 1)
    have wins : (encSlpInstr prog[i]).wt < W :=
      (wt_le_wt_list (List.mem_map.mpr ⟨prog[i], List.getElem_mem hlt, rfl⟩)).trans wp
    have wsa := wt_list3_le (linSlpTable gs) (linSlpTable prev) (encSlpInstr prog[i])
    have wstep : (Val.list [linSlpTable gs, linSlpTable prev, encSlpInstr prog[i]]).wt ≤ linSlpStepArg W prog.length t := by
      unfold linSlpStepArg
      omega
    have hss := (linSlpStep_spec hstep hi ha hs gs prev prog[i] x hx).mono (linSlpStepCost_mono wstep t)
    have wx : (linVecVal (Multiplicative.toAdd x)).wt ≤ M := by
      rw [hnext] at wnext
      exact (wt_le_wt_list (by simp [linSlpTable])).le.trans wnext
    have dctx := Det.arg' (P := P) (vs := [a, .nat i, linSlpTable prev]) (rest := []) (j := 0) rfl
    have dg := Det.get' dctx (Det.nat 0) rfl
    have dp := Det.get' dctx (Det.nat 1) rfl
    have di := Det.arg' (P := P) (vs := [a, .nat i, linSlpTable prev]) (rest := []) (j := 1) rfl
    have dins := Det.get' dp di (by simpa using congrArg (Option.map encSlpInstr) (List.getElem?_eq_getElem hlt))
    have da := Det.arg' (P := P) (vs := [a, .nat i, linSlpTable prev]) (rest := []) (j := 2) rfl
    have dc := Det.call (Det.mk3 dg da dins) hss
    have dn := Det.snoc da dc
    refine dn.post fun cost hc => ⟨?_, ?_⟩
    · dsimp only
      rw [hnext]
      simp only [linSlpTable, List.map_append, List.map_cons, List.map_nil]
      rfl
    · have wi := wt_nat_le i
      have wal := wt_list3_le a (.nat i) (linSlpTable prev)
      have wn : (Val.list ((prev.map fun v => linVecVal (Multiplicative.toAdd v)) ++ [linVecVal (Multiplicative.toAdd x)])).wt ≤ M := by
        simpa [linSlpTable, hnext, List.map_append] using wnext
      change cost ≤ linSlpLoopStepCost W prog.length t + 100 * (W + prog.length + M + 1)
      unfold linSlpLoopStepCost
      simp only [prev, W, a, linSlpTable] at *
      omega

end GI.Impl
