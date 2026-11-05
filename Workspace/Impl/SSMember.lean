module

public import Workspace.Impl.SSWrapProg

@[expose] public section

/-!
# The membership wrapper

`ssMemF` builds the table for the base `[0, …, n-1]`, sifts `x`, and answers `1` when `x` sifts
through (`ssMemF_spec`). By `ss_mem_correct`, this happens exactly when `x ∈ ⟨gs⟩`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- **Correctness.** `x` sifts through the table of `ssBuild` exactly when `x ∈ ⟨gs⟩`. -/
theorem ss_mem_correct (gs : List (Perm (Fin n))) (x : Perm (Fin n)) :
    (ssSift (List.finRange n) (ssBuild (List.finRange n) gs).1 x).2.2 = 0 ↔ x ∈ gens gs := by
  obtain ⟨hinv, hc, hgen⟩ := ssBuild_spec (B := List.finRange n) (gs := gs)
  rw [ss_mem_gens_iff (fun i => List.mem_finRange i) hinv.wf hc hinv.entry_mem hgen x, mem_ssS,
    ssSift_eq, ssSiftR_stop]
  simp

/-- The membership wrapper: `1` if `x` sifts through, `0` otherwise. -/
def ssMemF (stsift : ℕ) : Expr :=
  .arith .eq (.get (.get (.call stsift (.var 0)) (.nat 1)) (.nat 2)) (.nat 0)

/-- **Membership.** -/
theorem ssMemF_spec {P : Program} (hw : SsWrapAt P) (hf : P.funs[52]? = some (ssMemF 51))
    (gs : List (Perm (Fin n))) (x : Perm (Fin n)) :
    FunAll P 52 (.list [encGroup gs, encPerm x]) (fun v c =>
      ((v = .nat 1 ∧ x ∈ gens gs) ∨ (v = .nat 0 ∧ x ∉ gens gs)) ∧
        c ≤ 10 * ssPolyK * ((Val.list [encGroup gs, encPerm x]).wt + 1) ^ 32) := by
  set w := (Val.list [encGroup gs, encPerm x]).wt with hwdef
  have hY := ss_wrap_Y (gs := gs) (vs := [encGroup gs, encPerm x]) (by simp)
  rw [← hwdef] at hY
  set Y := 3 * (w + 1) with hYdef
  have hss := ssStSiftF_spec hw.stsift hw.range hw.start hw.core x hY
  have hRw := hss.wt_lt
  obtain ⟨hYW, hWC⟩ := ss_le_core (Y := Y) (by omega)
  generalize hr : ssSift (List.finRange n) (ssBuild (List.finRange n) gs).1 x = r at hss hRw
  generalize ssEncSt (ssBuild (List.finRange n) gs) = S at hss hRw
  set W := 4 * ssCoreCost Y with hW
  set a := Val.list [encGroup gs, encPerm x] with ha
  have haW : a.wt ≤ W := by omega
  clear_value W a
  have dC : StDC P [a] (.call 51 (.var 0)) (.list [S, ssEncAcc r]) (1 + 1) (0 + W)
      W := StDC.call (StDC.var' rfl haW) hss (by omega)
  have hAw : (ssEncAcc r).wt < (Val.list [S, ssEncAcc r]).wt := wt_le_wt_list (by simp)
  have d1 := StDC.get (x := 1) (v := ssEncAcc r) dC (StDC.nat 1 (by omega)) rfl (by omega)
  have hsw : (Val.nat r.2.2).wt < (ssEncAcc r).wt := wt_le_wt_list (by simp)
  have d2 := StDC.get (vs := [encPerm r.1, natList r.2.1, .nat r.2.2]) (x := 2) (v := .nat r.2.2)
    d1 (StDC.nat 2 (by omega)) rfl (by omega)
  have d3 := StDC.arith (op := .eq) (z := if r.2.2 = 0 then 1 else 0) d2 (StDC.nat 0 (by omega))
    rfl ((wt_nat_le _).trans (by split_ifs <;> omega))
  refine FunAll.mono (StDC.funDet hf d3 le_rfl) fun v c ⟨hv, hc⟩ => ⟨?_, ss_wrap_cost ?_⟩
  · subst hv
    by_cases h : r.2.2 = 0
    · rw [if_pos h]
      exact Or.inl ⟨rfl, (ss_mem_correct gs x).mp (hr ▸ h)⟩
    · rw [if_neg h]
      exact Or.inr ⟨rfl, fun hx => h (hr ▸ (ss_mem_correct gs x).mpr hx)⟩
  · show c ≤ 100 * ssCoreCost Y
    omega

end GI.Impl
