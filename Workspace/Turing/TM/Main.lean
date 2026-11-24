/-
Simulation of stack machine runs and halting on Mathlib's Turing machines (`GI.Turing.SimulatesSM`).

Multi-step simulation (`steps_sim`) follows by induction on `SM.Steps` from `step_sim`. At a
`halt` instruction, `halt_sim` drains the ten non-output stacks, reverses `outBuf` onto `out`,
resets the internal state to `initState`, and halts in `haltList (tm P) c.out` in time linear in
the total stack length. Combining this with `reachesIn_totalLen_le` yields a linear (hence
quadratic) time bound in `S + x.length + 1`, proving `GI.Turing.simulatesSM`.
-/
module

public import Workspace.Turing.TM.Step

@[expose] public section

namespace GI.Turing.TM

open _root_.Turing (TM2OutputsInTime initList haltList)
open _root_.Turing.TM2 (stepAux)
open Function (update)

/-- Multi-step simulation: a stack-machine run of total cost `S` is simulated by at most
`(P.length + 4) * S` steps of `tm P`, preserving `Rel P`. -/
theorem steps_sim {P : SM.Program} {c₁ c₂ : SM.Config} {S : ℕ}
    (hsteps : SM.Steps P c₁ c₂ S) {cfg₁ : (tm P).Cfg} (hrel : Rel P c₁ cfg₁) :
    ∃ cfg₂ t, Rel P c₂ cfg₂ ∧ ReachesIn (tm P) cfg₁ cfg₂ t ∧ t ≤ (P.length + 4) * S := by
  induction hsteps generalizing cfg₁ with
  | refl c =>
    exact ⟨cfg₁, 0, hrel, ReachesIn.refl cfg₁, Nat.zero_le _⟩
  | step hs _ ih =>
    obtain ⟨cfg', t₁, hrel', hrun₁, ht₁⟩ := step_sim hrel hs
    obtain ⟨cfg₂, t₂, hrel₂, hrun₂, ht₂⟩ := ih hrel'
    refine ⟨cfg₂, t₁ + t₂, hrel₂, hrun₁.trans hrun₂, ?_⟩
    rw [Nat.mul_add]
    omega

private theorem tmProg_halt {P : SM.Program} (μ : Micro) :
    tmProg P (⟨P.length, Nat.lt_succ_self P.length⟩, μ) = haltStmt P.length μ := by
  simp [tmProg]

private theorem drain_step {P : SM.Program} (i : Fin 10) (v : State P.length) (S : K → List Bool) :
    let haltIdx : Fin (P.length + 1) := ⟨P.length, Nat.lt_succ_self P.length⟩
    let nextLab : Lab P.length :=
      if h : i.val + 1 < 10 then (haltIdx, .drain ⟨i.val + 1, h⟩) else (haltIdx, .flushOut)
    ReachesIn (tm P) ⟨some (haltIdx, .drain i), v, S⟩
      ⟨some nextLab, { v with flag := false }, update S (drainOrder i) []⟩
      ((S (drainOrder i)).length + 1) := by
  intro haltIdx nextLab
  have hm : tmProg P (haltIdx, .drain i) =
      drainLoopStmt (drainOrder i) (haltIdx, .drain i) (.goto (fun _ => nextLab)) := by
    rw [tmProg_halt]; rfl
  have h := reachesIn_drainLoop (P := P) (k := drainOrder i) (self := (haltIdx, .drain i))
    (exitStmt := .goto (fun _ => nextLab)) hm (S (drainOrder i)) v S rfl
  simpa only [stepAux] using h

private theorem halt_from_drain {P : SM.Program} (v : State P.length) (S : K → List Bool)
    (hout : S .out = []) (hscr0 : S .scr0 = []) (hscr1 : S .scr1 = []) :
    ∃ t, ReachesIn (tm P) ⟨some (⟨P.length, Nat.lt_succ_self P.length⟩, .drain 0), v, S⟩
      (haltList (tm P) (S .outBuf).reverse) t ∧ t = totalLen S + 11 := by
  let h0 := drain_step (P := P) ⟨0, by decide⟩ v S
  let S1 := update S .inp []
  let v1 := { v with flag := false }
  let h1 := drain_step (P := P) ⟨1, by decide⟩ v1 S1
  let S2 := update S1 .ret []
  let v2 := { v1 with flag := false }
  let h2 := drain_step (P := P) ⟨2, by decide⟩ v2 S2
  let S3 := update S2 (.num 0) []
  let v3 := { v2 with flag := false }
  let h3 := drain_step (P := P) ⟨3, by decide⟩ v3 S3
  let S4 := update S3 (.num 1) []
  let v4 := { v3 with flag := false }
  let h4 := drain_step (P := P) ⟨4, by decide⟩ v4 S4
  let S5 := update S4 (.num 2) []
  let v5 := { v4 with flag := false }
  let h5 := drain_step (P := P) ⟨5, by decide⟩ v5 S5
  let S6 := update S5 (.num 3) []
  let v6 := { v5 with flag := false }
  let h6 := drain_step (P := P) ⟨6, by decide⟩ v6 S6
  let S7 := update S6 (.num 4) []
  let v7 := { v6 with flag := false }
  let h7 := drain_step (P := P) ⟨7, by decide⟩ v7 S7
  let S8 := update S7 (.num 5) []
  let v8 := { v7 with flag := false }
  let h8 := drain_step (P := P) ⟨8, by decide⟩ v8 S8
  let S9 := update S8 (.num 6) []
  let v9 := { v8 with flag := false }
  let h9 := drain_step (P := P) ⟨9, by decide⟩ v9 S9
  let S10 := update S9 (.num 7) []
  let v10 := { v9 with flag := false }
  have hS10_buf : S10 .outBuf = S .outBuf := by
    simp [S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, Function.update_of_ne]
  have hS10_out : S10 .out = [] := by
    simp [S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, Function.update_of_ne, hout]
  have hflush := reachesIn_flushOut (P := P)
    (self := (⟨P.length, Nat.lt_succ_self P.length⟩, .flushOut))
    (by rw [tmProg_halt]; rfl) (S .outBuf) v10 S10 hS10_buf
  have hchain := (((((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans h6).trans
    h7).trans h8).trans h9).trans hflush
  have hfinal : (⟨none, initState P.length,
      update (update S10 .outBuf []) .out ((S .outBuf).reverse ++ S10 .out)⟩ : (tm P).Cfg) =
      haltList (tm P) (S .outBuf).reverse := by
    cases hcfg : haltList (tm P) (S .outBuf).reverse with
    | mk l var stk =>
      have hl : l = none := by
        have := congrArg Turing.TM2.Cfg.l hcfg; simpa [haltList] using this.symm
      have hvar : var = initState P.length := by
        have := congrArg Turing.TM2.Cfg.var hcfg; simpa [haltList, tm] using this.symm
      have hstk : update (update S10 .outBuf []) .out ((S .outBuf).reverse ++ S10 .out) = stk := by
        funext k
        have hk := congrFun (congrArg Turing.TM2.Cfg.stk hcfg) k
        dsimp only at hk
        rw [← hk, haltList_stk]
        cases k with
        | out => simp [hS10_out]
        | outBuf => simp [Function.update_of_ne]
        | inp => simp [S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, Function.update_of_ne]
        | ret => simp [S10, S9, S8, S7, S6, S5, S4, S3, S2, Function.update_of_ne]
        | scr0 => simp [S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, Function.update_of_ne, hscr0]
        | scr1 => simp [S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, Function.update_of_ne, hscr1]
        | num s =>
          fin_cases s <;>
            simp [S10, S9, S8, S7, S6, S5, S4, S3, S2, S1, Function.update_of_ne]
      subst hl; subst hvar; rw [hstk]
  rw [hfinal] at hchain
  refine ⟨_, hchain, ?_⟩
  have hlen := totalLen_eq S
  simp only [hout, hscr0, hscr1, List.length_nil] at hlen
  simp only [drainOrder, S1, S2, S3, S4, S5, S6, S7, S8, S9, Function.update_of_ne, ne_eq,
    K.num.injEq, reduceCtorEq, not_false_eq_true, Fin.reduceEq]
  omega

/-- Halting phase: from a configuration related to a `halt` instruction, `tm P` reaches
`haltList (tm P) c.out` in `totalLen cfg.stk + 12` steps. -/
theorem halt_sim {P : SM.Program} {c : SM.Config} {cfg : (tm P).Cfg}
    (hrel : Rel P c cfg) (hhalt : P[c.pc]? = some .halt) :
    ∃ t, ReachesIn (tm P) cfg (haltList (tm P) c.out) t ∧ t = totalLen cfg.stk + 12 := by
  have hlt : c.pc < P.length := by
    by_contra h
    rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hhalt
    cases hhalt
  have hval : (clampPc P.length c.pc).val = c.pc := Nat.min_eq_left (Nat.le_of_lt hlt)
  have hget : P[c.pc] = .halt := by
    rw [List.getElem?_eq_getElem hlt] at hhalt
    exact Option.some.inj hhalt
  have hstep1 : (tm P).step cfg =
      some ⟨some (⟨P.length, Nat.lt_succ_self P.length⟩, .drain 0), cfg.var, cfg.stk⟩ := by
    rcases cfg with ⟨l, v, S⟩
    have hl := hrel.label
    dsimp only at hl
    subst hl
    change some (stepAux (tmProg P (clampPc P.length c.pc, .start)) v S) = _
    simp only [tmProg, hval, hlt, ↓reduceDIte, hget, instrStmt, stepAux]
    rfl
  obtain ⟨t, hrun, ht⟩ := halt_from_drain (P := P) cfg.var cfg.stk hrel.stk_out hrel.stk_scr0
    hrel.stk_scr1
  rw [hrel.stk_outBuf, List.reverse_reverse] at hrun
  exact ⟨t + 1, ReachesIn.step_head hstep1 hrun, by omega⟩

end GI.Turing.TM

namespace GI.Turing

open GI.Turing.TM

/-- **Step 3.** Every stack machine program runs on a Mathlib Turing machine with `Bool` input
and output alphabets, in time quadratic in the cost of the run and the input length. -/
theorem simulatesSM : SimulatesSM := by
  intro P
  refine ⟨tmAux P, (maxPush P + 1) * (P.length + 4) + 12, ?_⟩
  intro x y S ⟨c, hsteps, hhalt, hout⟩
  obtain ⟨cfg, t₁, hrel, hrun₁, ht₁⟩ := steps_sim hsteps (rel_init P x)
  obtain ⟨t₂, hrun₂, ht₂⟩ := halt_sim hrel hhalt
  have htotal : totalLen cfg.stk ≤ x.length + maxPush P * t₁ := by
    have h := reachesIn_totalLen_le hrun₁
    rwa [totalLen_initList] at h
  have hrun : ReachesIn (tm P) (_root_.Turing.initList (tm P) x)
      (_root_.Turing.haltList (tm P) y) (t₁ + t₂) := by
    rw [← hout]
    exact hrun₁.trans hrun₂
  have hbound : t₁ + t₂ ≤ ((maxPush P + 1) * (P.length + 4) + 12) * (S + x.length + 1) ^ 2 := by
    have hlin1 : t₁ + t₂ ≤ (maxPush P + 1) * t₁ + x.length + 12 := by
      have : (maxPush P + 1) * t₁ = maxPush P * t₁ + t₁ := by
        rw [Nat.add_mul, Nat.one_mul]
      omega
    have hmul : (maxPush P + 1) * t₁ ≤ (maxPush P + 1) * ((P.length + 4) * S) :=
      Nat.mul_le_mul_left _ ht₁
    have hlin2 : (maxPush P + 1) * ((P.length + 4) * S) + x.length + 12 ≤
        ((maxPush P + 1) * (P.length + 4) + 12) * (S + x.length + 1) := by
      have h1 : (maxPush P + 1) * ((P.length + 4) * S) =
          ((maxPush P + 1) * (P.length + 4)) * S := (Nat.mul_assoc _ _ _).symm
      rw [h1]
      generalize (maxPush P + 1) * (P.length + 4) = M
      have h2 : (M + 12) * (S + x.length + 1) =
          M * S + M * x.length + M + 12 * S + 12 * x.length + 12 := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one,
          Nat.mul_add, Nat.mul_add, Nat.mul_one]
        omega
      omega
    have hsq : S + x.length + 1 ≤ (S + x.length + 1) ^ 2 := by
      rw [Nat.pow_two]
      exact Nat.le_mul_self _
    have hlin3 : ((maxPush P + 1) * (P.length + 4) + 12) * (S + x.length + 1) ≤
        ((maxPush P + 1) * (P.length + 4) + 12) * (S + x.length + 1) ^ 2 :=
      Nat.mul_le_mul_left _ hsq
    omega
  refine ⟨⟨⟨t₁ + t₂, ?_⟩, hbound⟩⟩
  have hx : x.map (tmAux P).inputAlphabet.symm = x := List.map_id x
  have hy : y.map (tmAux P).outputAlphabet.symm = y := List.map_id y
  rw [hx, hy]
  exact hrun

end GI.Turing
