/-
The main theorem for Turing machines from the log-cost machine theorem and the two simulation
steps.

`GI.Turing.turing_of` composes:
1. the wrapper program `wrap p` (`Workspace.Turing.Wrap.Program`),
2. the RAM-to-stack-machine simulation `SimulatesRAM`,
3. the stack-machine-to-Turing-machine simulation `SimulatesSM`, and
4. the polynomial-to-exponential bound (`Workspace.Turing.Wrap.Bound`),
to obtain `GI.Statement.TuringGraphIsomorphismInDegreeTime` from
`GI.Statement.GraphIsomorphismInDegreeTime`.
-/
module

public import Workspace.Turing.Interface
public import Workspace.Turing.Wrap.Bound
public import Workspace.Turing.Wrap.Program

@[expose] public section

namespace GI.Turing

open GI.Machine GI.Statement

/-- Theorem 1.1 for Turing machines, from Theorem 1.1 for the log-cost machine and the two
simulation steps. -/
theorem turing_of (h : GraphIsomorphismInDegreeTime)
    (hR : SimulatesRAM) (hS : SimulatesSM) :
    TuringGraphIsomorphismInDegreeTime := by
  obtain ⟨p, C, hp⟩ := h
  obtain ⟨P, cR, kR, hP⟩ := hR (wrap p)
  obtain ⟨M, cS, hM⟩ := hS P
  -- Combine the wrapper, RAM-simulation and SM-simulation polynomials into `cTot * U ^ kTot`.
  set c₁ := 40004
  set k₁ := 8
  set c₂ := cR * c₁ ^ kR
  set k₂ := k₁ * kR
  set c₃ := c₂ + 3
  set k₃ := max k₂ 2
  set cTot := cS * c₃ ^ 2
  set kTot := k₃ * 2
  obtain ⟨C', hC'⟩ := poly_le_exp_degree C cTot kTot
  refine ⟨M, C', fun n d G H hG hH => ?_⟩
  obtain ⟨fuel, mem', r, T, hrun, hout, hcost⟩ :=
    hp n d G H (Function.update (rawInput (inputBits G H)) 0 n)
      (inputLayout_update_rawInput G H) hG hH
  obtain ⟨fuel', mem_w, B, T_w, a, hwrun, ha, hraw, hTw, hmB⟩ := wrap_run hrun hout
  obtain ⟨S, hHalts, hS_le⟩ := hP (inputBits G H) fuel' mem_w B T_w hwrun
  rw [hraw] at hHalts
  have hTM := hM (inputBits G H) (answerBits a) S hHalts
  refine ⟨a, ha, tm2OutputsInTime_mono ?_ hTM⟩
  -- Chain the polynomial bounds in `U := T + n + 2`.
  set U := T + n + 2
  have hU1 : 1 ≤ U := by omega
  have hU2 : 2 ≤ U := by omega
  have hlen_x : (inputBits G H).length ≤ 2 * U ^ 2 := by
    rw [inputBits_length]
    have hnn : n * n ≤ U ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    have h2nn : 2 * n * n = 2 * (n * n) := by ring
    omega
  have hU2_le8 : U ^ 2 ≤ U ^ 8 := Nat.pow_le_pow_right hU1 (by omega)
  have hbase1 : T_w + (inputBits G H).length + mem_w B + 2 ≤ c₁ * U ^ k₁ := by
    have h2_le : 2 ≤ 2 * U ^ 8 := by
      have : 1 ≤ U ^ 8 := Nat.one_le_pow 8 U (by omega)
      omega
    dsimp only [c₁, k₁]
    omega
  have hS_poly : S ≤ c₂ * U ^ k₂ := by
    calc
      S ≤ cR * (T_w + (inputBits G H).length + mem_w B + 2) ^ kR := hS_le
      _ ≤ cR * (c₁ * U ^ k₁) ^ kR :=
        Nat.mul_le_mul_left cR (Nat.pow_le_pow_left hbase1 kR)
      _ = c₂ * U ^ k₂ := by
        rw [pow_poly_le, ← Nat.mul_assoc]
  have hbase2 : S + (inputBits G H).length + 1 ≤ c₃ * U ^ k₃ := by
    have h1 : (inputBits G H).length + 1 ≤ 3 * U ^ 2 := by
      have : 1 ≤ U ^ 2 := Nat.one_le_pow 2 U (by omega)
      omega
    have h2 : S + ((inputBits G H).length + 1) ≤ c₂ * U ^ k₂ + 3 * U ^ 2 :=
      Nat.add_le_add hS_poly h1
    have h3 := add_poly_le (B := U) (c₁ := c₂) (c₂ := 3) (k₁ := k₂) (k₂ := 2) hU1
    dsimp only [c₃, k₃]
    omega
  have hTM_poly : cS * (S + (inputBits G H).length + 1) ^ 2 ≤ cTot * U ^ kTot := by
    calc
      cS * (S + (inputBits G H).length + 1) ^ 2
          ≤ cS * (c₃ * U ^ k₃) ^ 2 :=
            Nat.mul_le_mul_left cS (Nat.pow_le_pow_left hbase2 2)
      _ = cTot * U ^ kTot := by
        rw [pow_poly_le, ← Nat.mul_assoc]
  exact hTM_poly.trans (hC' n d T hcost)

end GI.Turing
