/-
Assembling a full stack machine simulation of the log-cost RAM (`GI.Turing.SimulatesRAM`) from
`FrontEnd`, `BackEnd` and `CoreSim`.

For any program `p : GI.Machine.Program`, we concatenate the front end at index `0`, the core
simulation of `p` right after it, the back end right after that, and a final `halt`. Starting from
`SM.init x`, all stacks are empty, so the three blocks chain directly and yield a halting run whose
cost is polynomial in `T`, `x.length` and `mem' B`.
-/
module

public import Workspace.Turing.Lib.Logic
public import Workspace.Machine.Run

@[expose] public section

namespace GI.Turing

open GI.Machine (len run Runs)
open GI.Turing.SM

/-- The value returned by `GI.Machine.run` has binary length at most the cost of the run. -/
theorem len_run_le {p : GI.Machine.Program} {mem mem' : ℕ → ℕ} {fuel B T : ℕ}
    (h : run p mem fuel = some (mem', B, T)) : len B ≤ T := by
  unfold run at h
  cases fuel with
  | zero => simp [GI.Machine.exec] at h
  | succ f =>
    simp only [GI.Machine.exec, GI.Machine.evalArgs, List.getD_nil] at h
    cases hb : p.procs[0]? with
    | none => simp [hb] at h
    | some body =>
      simp only [hb] at h
      cases he : GI.Machine.exec p f body { mem := mem, regs := fun _ => 0 } with
      | none => simp [he] at h
      | some res =>
        obtain ⟨o, st', c'⟩ := res
        simp only [he] at h
        cases o with
        | normal =>
          simp only [Option.some.injEq, Prod.mk.injEq, Function.update_self] at h
          obtain ⟨_, rfl, _⟩ := h
          simp [GI.Machine.len_zero]
        | returned w =>
          simp only [Option.some.injEq, Prod.mk.injEq, Function.update_self] at h
          obtain ⟨_, rfl, rfl⟩ := h
          have hruns : Runs p body { mem := mem, regs := fun _ => 0 }
              (.returned w) st' c' := ⟨f, he⟩
          have hle := Runs.len_returned_le hruns
          omega

/-- Combine `FrontEnd`, `BackEnd` and `CoreSim` to simulate any log-cost RAM program on the stack
machine. -/
theorem simulatesRAM_of (hFront : FrontEnd) (hBack : BackEnd) (hCore : CoreSim) : SimulatesRAM := by
  obtain ⟨fe, cF, hfe⟩ := hFront
  obtain ⟨be, cB, hbe⟩ := hBack
  intro p
  obtain ⟨co, cC, kC, hco⟩ := hCore p
  let a₁ := (fe 0).length
  let a₂ := a₁ + (co a₁).length
  let a₃ := a₂ + (be a₂).length
  let P : Program := fe 0 ++ co a₁ ++ be a₂ ++ [.halt]
  have hcodeAll : CodeAt P 0 (((fe 0 ++ co a₁) ++ be a₂) ++ [.halt]) := CodeAt.self P
  have hhalt_code : CodeAt P a₃ [.halt] := by
    have h := hcodeAll.append_right
    simpa [a₃, a₂, a₁, List.length_append, Nat.add_assoc] using h
  have hhalt_at : P[a₃]? = some .halt := hhalt_code.cons
  have hpref2 := hcodeAll.append_left
  have hbe_code : CodeAt P a₂ (be a₂) := by
    have h := hpref2.append_right
    simpa [a₂, a₁, List.length_append] using h
  have hpref1 := hpref2.append_left
  have hco_code : CodeAt P a₁ (co a₁) := by
    have h := hpref1.append_right
    simpa [a₁] using h
  have hfe_code : CodeAt P 0 (fe 0) := hpref1.append_left
  let k₀ := max kC 2
  let C := cF + cC * (cF + 1) ^ kC + cB * (cF + cC + 2) ^ 3
  refine ⟨P, C, 3 * k₀, fun x fuel mem' B T hrun => ?_⟩
  -- 1. Front end from SM.init x.
  obtain ⟨cfg₁, S₁, hs₁, hpc₁, hmem₁, hsz₁, hstk₁, hrs₁, hout₁, hS₁⟩ :=
    hfe P 0 (SM.init x) hfe_code rfl rfl
  simp only [SM.init] at hmem₁ hsz₁ hS₁
  have hpc₁' : cfg₁.pc = a₁ := by simpa [a₁] using hpc₁
  have hzero_other : ∀ t, t ≠ E → t ≠ Mem → cfg₁.stk t = [] := fun t _ htM => by
    rw [hstk₁ t htM]; rfl
  have hE₁ : cfg₁.stk E = [] := by rw [hstk₁ E (by decide)]; rfl
  have hrun₁ : run p (memOf (cfg₁.stk Mem)) fuel = some (mem', B, T) := by
    rwa [hmem₁]
  -- 2. Core simulation.
  obtain ⟨cfg₂, S₂, hs₂, hpc₂, hmem₂, hE₂, hk₂, hsz₂, hS₂⟩ :=
    hco P a₁ cfg₁ fuel mem' B T hco_code hpc₁' hzero_other hrun₁
  have hpc₂' : cfg₂.pc = a₂ := by simpa [a₂] using hpc₂
  have hE₂' : cfg₂.stk E = B :: [] := by rw [hE₂, hE₁]
  have hout₂ : cfg₂.out = [] := by rw [hk₂.out_eq, hout₁]; rfl
  -- 3. Back end.
  obtain ⟨cfg₃, S₃, hs₃, hpc₃, hout₃, hS₃⟩ :=
    hbe P a₂ cfg₂ B [] hbe_code hpc₂' hE₂'
  have hpc₃' : cfg₃.pc = a₃ := by simpa [a₃] using hpc₃
  have hout₃' : cfg₃.out = rawOutput mem' B := by simpa [hout₂, hmem₂] using hout₃
  -- 4. Halt and bound total cost S₁ + S₂ + S₃.
  refine ⟨S₁ + S₂ + S₃, ⟨cfg₃, (hs₁.trans hs₂).trans hs₃, by rw [hpc₃']; exact hhalt_at, hout₃'⟩, ?_⟩
  let N := T + x.length + mem' B + 2
  have hN_ge : 2 ≤ N := by omega
  have hN_pos : 1 ≤ N := by omega
  have hlenB : len B ≤ T := len_run_le hrun
  have hpow2 : N ^ 2 ≤ N ^ (3 * k₀) :=
    Nat.pow_le_pow_right hN_pos (by omega)
  have hpow2kC : N ^ (2 * kC) ≤ N ^ (3 * k₀) :=
    Nat.pow_le_pow_right hN_pos (by omega)
  have hpow2_k₀ : N ^ 2 ≤ N ^ k₀ :=
    Nat.pow_le_pow_right hN_pos (by omega)
  have hpowkC_k₀ : N ^ kC ≤ N ^ k₀ :=
    Nat.pow_le_pow_right hN_pos (by omega)
  have hsz₁_le : listSize (cfg₁.stk Mem) ≤ cF * N ^ 2 :=
    le_trans hsz₁ (Nat.mul_le_mul_left cF (Nat.pow_le_pow_left (by omega) 2))
  have hS₁_le : S₁ ≤ cF * N ^ (3 * k₀) :=
    le_trans (le_trans hS₁ (Nat.mul_le_mul_left cF (Nat.pow_le_pow_left (by omega) 2)))
      (Nat.mul_le_mul_left cF hpow2)
  have hbase₂ : T + listSize (cfg₁.stk Mem) + 1 ≤ (cF + 1) * N ^ 2 := by
    have hN_le_N2 : N ≤ N ^ 2 := Nat.le_self_pow (by omega) N
    calc T + listSize (cfg₁.stk Mem) + 1 ≤ N + cF * N ^ 2 := by omega
      _ ≤ 1 * N ^ 2 + cF * N ^ 2 := by omega
      _ = (cF + 1) * N ^ 2 := by ring
  have hS₂_le : S₂ ≤ cC * (cF + 1) ^ kC * N ^ (3 * k₀) := by
    calc S₂ ≤ cC * (T + listSize (cfg₁.stk Mem) + 1) ^ kC := hS₂
      _ ≤ cC * ((cF + 1) * N ^ 2) ^ kC :=
        Nat.mul_le_mul_left cC (Nat.pow_le_pow_left hbase₂ kC)
      _ = cC * ((cF + 1) ^ kC * (N ^ 2) ^ kC) := by rw [Nat.mul_pow]
      _ = cC * (cF + 1) ^ kC * N ^ (2 * kC) := by rw [← Nat.pow_mul, Nat.mul_assoc]
      _ ≤ cC * (cF + 1) ^ kC * N ^ (3 * k₀) := Nat.mul_le_mul_left _ hpow2kC
  have hsz₂_le : listSize (cfg₂.stk Mem) ≤ (cF + cC) * N ^ k₀ := by
    have h1 : cF * N ^ 2 ≤ cF * N ^ k₀ := Nat.mul_le_mul_left cF hpow2_k₀
    have h2 : cC * (T + 1) ^ kC ≤ cC * N ^ k₀ :=
      le_trans (Nat.mul_le_mul_left cC (Nat.pow_le_pow_left (by omega) kC))
        (Nat.mul_le_mul_left cC hpowkC_k₀)
    calc listSize (cfg₂.stk Mem)
        ≤ listSize (cfg₁.stk Mem) + cC * (T + 1) ^ kC := hsz₂
      _ ≤ cF * N ^ k₀ + cC * N ^ k₀ := by omega
      _ = (cF + cC) * N ^ k₀ := by ring
  have hbase₃ : memOf (cfg₂.stk Mem) B + listSize (cfg₂.stk Mem) + len B + 1 ≤
      (cF + cC + 2) * N ^ k₀ := by
    rw [hmem₂]
    have hN_le_Nk₀ : N ≤ N ^ k₀ := Nat.le_self_pow (by omega) N
    calc mem' B + listSize (cfg₂.stk Mem) + len B + 1
        ≤ N + (cF + cC) * N ^ k₀ + N := by omega
      _ ≤ N ^ k₀ + (cF + cC) * N ^ k₀ + N ^ k₀ := by omega
      _ = (cF + cC + 2) * N ^ k₀ := by ring
  have hS₃_le : S₃ ≤ cB * (cF + cC + 2) ^ 3 * N ^ (3 * k₀) := by
    calc S₃ ≤ cB * (memOf (cfg₂.stk Mem) B + listSize (cfg₂.stk Mem) + len B + 1) ^ 3 := hS₃
      _ ≤ cB * ((cF + cC + 2) * N ^ k₀) ^ 3 :=
        Nat.mul_le_mul_left cB (Nat.pow_le_pow_left hbase₃ 3)
      _ = cB * ((cF + cC + 2) ^ 3 * (N ^ k₀) ^ 3) := by rw [Nat.mul_pow]
      _ = cB * (cF + cC + 2) ^ 3 * N ^ (3 * k₀) := by rw [← Nat.pow_mul, Nat.mul_comm k₀ 3, Nat.mul_assoc]
  calc S₁ + S₂ + S₃
      ≤ cF * N ^ (3 * k₀) + cC * (cF + 1) ^ kC * N ^ (3 * k₀) +
          cB * (cF + cC + 2) ^ 3 * N ^ (3 * k₀) := by omega
    _ = C * N ^ (3 * k₀) := by simp only [C]; ring

end GI.Turing
