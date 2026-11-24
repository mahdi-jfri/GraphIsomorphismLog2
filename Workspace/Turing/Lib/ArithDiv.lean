/-
Stack machine code blocks for integer division and remainder, and the combined `ArithBlocks`
theorem covering every operation of `GI.Machine.BinOp`.

Long division works in two loops: the first pushes the binary digits of `x` (plus 1, above a
sentinel 0) onto a scratch stack, and the second pops them highest first to build the quotient `q`
and remainder `r`. Division by 0 is handled up front (`x / 0 = 0`, `x % 0 = x`).
-/
module

public import Workspace.Turing.Lib.ArithBasic

@[expose] public section

namespace GI.Turing

open GI.Machine (len)
open GI.Turing.SM

/-! ### Binary digit accumulation -/

/-- Value reconstructed from an accumulator `acc` and a list `ds` of shifted binary digits
(each digit is `b + 1` for `b ∈ {0, 1}`, highest digit first). -/
def fromDigits : ℕ → List ℕ → ℕ
  | acc, [] => acc
  | acc, d :: ds => fromDigits (2 * acc + (d - 1)) ds

theorem le_fromDigits (acc : ℕ) (ds : List ℕ) : acc ≤ fromDigits acc ds := by
  induction ds generalizing acc with
  | nil => exact le_rfl
  | cons d ds ih => exact le_trans (by omega) (ih _)

/-! ### Division and remainder code -/

/-- Long-division block for `div` (`isMod = false`) and `mod` (`isMod = true`).
Scratch stacks `s + 1 .. s + 5` hold `y`, `n`/`r`, the shifted digits of `x` above sentinel 0,
and two single-word temporaries. -/
def divModCode (isMod : Bool) (s : Stk) (a : ℕ) : List Instr :=
  let t₁ := scratch s 1
  let t₂ := scratch s 2
  let t₃ := scratch s 3
  let t₄ := scratch s 4
  let t₅ := scratch s 5
  let lZero := if isMod then a + 36 else a + 35
  let tail : List Instr :=
    if isMod then
      [.pop s, .move t₂ s, .jmp (a + 37), .pop t₁]
    else
      [.pop t₂, .jmp (a + 38), .pop t₁, .pop s, .push s 0]
  [ .move s t₁, .copy t₁ t₄, .jz t₄ lZero,
    .move s t₂, .push s 0, .push t₃ 0,
    .copy t₂ t₄, .jz t₄ (a + 14),
    .copy t₂ t₃, .parity t₃, .push t₄ 1, .add t₃ t₄, .half t₂, .jmp (a + 6),
    .copy t₃ t₄, .jz t₄ (a + 31),
    .push t₄ 1, .sub t₃ t₄, .double t₂, .add t₂ t₃, .double s,
    .copy t₁ t₄, .copy t₂ t₅, .sub t₄ t₅, .jz t₄ (a + 26), .jmp (a + 14),
    .copy t₁ t₄, .sub t₂ t₄, .push t₄ 1, .add s t₄, .jmp (a + 14),
    .pop t₃, .pop t₁ ] ++ tail

private theorem divModBlock (isMod : Bool) :
    BinBlock (fun x y => if isMod then x % y else x / y) (divModCode isMod) 50 := by
  intro s P a cfg x y rest hcode hpc hs
  let t₁ := scratch s 1
  let t₂ := scratch s 2
  let t₃ := scratch s 3
  let t₄ := scratch s 4
  let t₅ := scratch s 5
  have hs1 : s ≠ t₁ := (scratch_ne_self s (by decide)).symm
  have hs2 : s ≠ t₂ := (scratch_ne_self s (by decide)).symm
  have hs3 : s ≠ t₃ := (scratch_ne_self s (by decide)).symm
  have hs4 : s ≠ t₄ := (scratch_ne_self s (by decide)).symm
  have hs5 : s ≠ t₅ := (scratch_ne_self s (by decide)).symm
  have h12 : t₁ ≠ t₂ := scratch_ne (by decide)
  have h13 : t₁ ≠ t₃ := scratch_ne (by decide)
  have h14 : t₁ ≠ t₄ := scratch_ne (by decide)
  have h15 : t₁ ≠ t₅ := scratch_ne (by decide)
  have h23 : t₂ ≠ t₃ := scratch_ne (by decide)
  have h24 : t₂ ≠ t₄ := scratch_ne (by decide)
  have h25 : t₂ ≠ t₅ := scratch_ne (by decide)
  have h34 : t₃ ≠ t₄ := scratch_ne (by decide)
  have h35 : t₃ ≠ t₅ := scratch_ne (by decide)
  have h45 : t₄ ≠ t₅ := scratch_ne (by decide)
  let lZero := if isMod then a + 36 else a + 35
  let allStks5 : List Stk := [s, t₁, t₂, t₃, t₄, t₅]
  have ms : s ∈ allStks5 := by simp [allStks5]
  have m1 : t₁ ∈ allStks5 := by simp [allStks5]
  have m2 : t₂ ∈ allStks5 := by simp [allStks5]
  have m3 : t₃ ∈ allStks5 := by simp [allStks5]
  have m4 : t₄ ∈ allStks5 := by simp [allStks5]
  have m5 : t₅ ∈ allStks5 := by simp [allStks5]
  have hpref : CodeAt P a
      [ .move s t₁, .copy t₁ t₄, .jz t₄ lZero,
        .move s t₂, .push s 0, .push t₃ 0,
        .copy t₂ t₄, .jz t₄ (a + 14),
        .copy t₂ t₃, .parity t₃, .push t₄ 1, .add t₃ t₄, .half t₂, .jmp (a + 6),
        .copy t₃ t₄, .jz t₄ (a + 31),
        .push t₄ 1, .sub t₃ t₄, .double t₂, .add t₂ t₃, .double s,
        .copy t₁ t₄, .copy t₂ t₅, .sub t₄ t₅, .jz t₄ (a + 26), .jmp (a + 14),
        .copy t₁ t₄, .sub t₂ t₄, .push t₄ 1, .add s t₄, .jmp (a + 14),
        .pop t₃, .pop t₁ ] := by
    unfold divModCode at hcode
    exact hcode.append_left
  have htail : CodeAt P (a + 33)
      (if isMod then [.pop s, .move t₂ s, .jmp (a + 37), .pop t₁]
       else [.pop t₂, .jmp (a + 38), .pop t₁, .pop s, .push s 0]) := by
    unfold divModCode at hcode
    simpa using hcode.append_right
  have hlen_code : (divModCode isMod s a).length = if isMod then 37 else 38 := by
    cases isMod <;> simp [divModCode]
  have i0 : CodeAt P a [.move s t₁] := by simpa using hpref.at_offset 0 (by simp)
  have i1 : CodeAt P (a + 1) [.copy t₁ t₄] := by simpa using hpref.at_offset 1 (by simp)
  have i2 : CodeAt P (a + 2) [.jz t₄ lZero] := by simpa using hpref.at_offset 2 (by simp)
  -- Phase 0: move y to t₁, test y = 0.
  let c₁ : Config :=
    { cfg with pc := a + 1, stk := Function.update (Function.update cfg.stk s (x :: rest)) t₁ (y :: cfg.stk t₁) }
  have s0 : Steps P cfg c₁ (1 + len y) := Steps.move_ne hs1 i0 hpc hs
  have c₁s : c₁.stk s = x :: rest := by simp [c₁, hs1]
  have c₁t1 : c₁.stk t₁ = y :: cfg.stk t₁ := by simp [c₁]
  have c₁t2 : c₁.stk t₂ = cfg.stk t₂ := by simp [c₁, h12.symm, hs2.symm]
  have c₁t3 : c₁.stk t₃ = cfg.stk t₃ := by simp [c₁, h13.symm, hs3.symm]
  have c₁t4 : c₁.stk t₄ = cfg.stk t₄ := by simp [c₁, h14.symm, hs4.symm]
  have c₁t5 : c₁.stk t₅ = cfg.stk t₅ := by simp [c₁, h15.symm, hs5.symm]
  let c₂ : Config := { c₁ with pc := a + 2, stk := Function.update c₁.stk t₄ (y :: c₁.stk t₄) }
  have s1 : Steps P c₁ c₂ (1 + len y) := Steps.copy i1 rfl c₁t1
  have c₂s : c₂.stk s = x :: rest := by simp [c₂, hs4, c₁s]
  have c₂t1 : c₂.stk t₁ = y :: cfg.stk t₁ := by simp [c₂, h14, c₁t1]
  have c₂t2 : c₂.stk t₂ = cfg.stk t₂ := by simp [c₂, h24, c₁t2]
  have c₂t3 : c₂.stk t₃ = cfg.stk t₃ := by simp [c₂, h34, c₁t3]
  have c₂t4 : c₂.stk t₄ = y :: cfg.stk t₄ := by simp [c₂, c₁t4]
  have c₂t5 : c₂.stk t₅ = cfg.stk t₅ := by simp [c₂, h45.symm, c₁t5]
  have hk01 : Keeps allStks5 cfg c₂ :=
    (Keeps.update_stk₂_mem cfg (a + 1) m1 ms _ _).trans (Keeps.update_stk_mem c₁ (a + 2) m4 _)
  by_cases hy : y = 0
  · -- Division by zero.
    subst hy
    let c₃ : Config := { c₂ with pc := lZero, stk := Function.update c₂.stk t₄ (cfg.stk t₄) }
    have s2 : Steps P c₂ c₃ 1 := Steps.jz_zero i2 rfl c₂t4
    have c₃s : c₃.stk s = x :: rest := by simp [c₃, hs4, c₂s]
    have c₃t1 : c₃.stk t₁ = 0 :: cfg.stk t₁ := by simp [c₃, h14, c₂t1]
    have c₃t2 : c₃.stk t₂ = cfg.stk t₂ := by simp [c₃, h24, c₂t2]
    have c₃t3 : c₃.stk t₃ = cfg.stk t₃ := by simp [c₃, h34, c₂t3]
    have c₃t4 : c₃.stk t₄ = cfg.stk t₄ := by simp [c₃]
    have c₃t5 : c₃.stk t₅ = cfg.stk t₅ := by simp [c₃, h45.symm, c₂t5]
    cases isMod
    · -- div by 0 -> 0
      simp only [Bool.false_eq_true, ↓reduceIte] at htail hlen_code lZero c₃ ⊢
      have i35 : CodeAt P (a + 35) [.pop t₁] := by
        have h := htail.at_offset 2 (by simp)
        simpa [Nat.add_assoc] using h
      have i36 : CodeAt P (a + 36) [.pop s] := by
        have h := htail.at_offset 3 (by simp)
        simpa [Nat.add_assoc] using h
      have i37 : CodeAt P (a + 37) [.push s 0] := by
        have h := htail.at_offset 4 (by simp)
        simpa [Nat.add_assoc] using h
      let c₄ : Config := { c₃ with pc := a + 36, stk := Function.update c₃.stk t₁ (cfg.stk t₁) }
      have s3 : Steps P c₃ c₄ (1 + len 0) := Steps.pop i35 rfl c₃t1
      have c₄s : c₄.stk s = x :: rest := by simp [c₄, hs1, c₃s]
      let c₅ : Config := { c₄ with pc := a + 37, stk := Function.update c₄.stk s rest }
      have s4 : Steps P c₄ c₅ (1 + len x) := Steps.pop i36 rfl c₄s
      let c₆ : Config := { c₅ with pc := a + 38, stk := Function.update c₅.stk s (0 :: c₅.stk s) }
      have s5 : Steps P c₅ c₆ (1 + len 0) := Steps.push i37 rfl
      have hk_end : Keeps allStks5 c₂ c₆ :=
        (((Keeps.update_stk_mem c₂ (a + 35) m4 _).trans
          (Keeps.update_stk_mem c₃ (a + 36) m1 _)).trans
          (Keeps.update_stk_mem c₄ (a + 37) ms _)).trans
          (Keeps.update_stk_mem c₅ (a + 38) ms _)
      have hkeeps : Keeps [s] cfg c₆ := (hk01.trans hk_end).of_subset_eq fun w hw hnot => by
        simp only [allStks5, List.mem_cons, List.not_mem_nil, or_false] at hw hnot
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl hnot
        · simp [c₆, c₅, c₄, hs1.symm]
        · simp [c₆, c₅, c₄, hs2.symm, h12.symm, c₃t2]
        · simp [c₆, c₅, c₄, hs3.symm, h13.symm, c₃t3]
        · simp [c₆, c₅, c₄, hs4.symm, h14.symm, c₃t4]
        · simp [c₆, c₅, c₄, hs5.symm, h15.symm, c₃t5]
      refine ⟨c₆, _, ((((s0.trans s1).trans s2).trans s3).trans s4).trans s5, ?_, ?_, hkeeps, ?_⟩
      · simp [c₆, hlen_code]
      · simp [c₆, c₅]
      · simp only [GI.Machine.len_zero]
        have h1 : len x + 0 + 1 ≤ (len x + 0 + 1) ^ 2 := Nat.le_self_pow (by omega) _
        omega
    · -- mod by 0 -> x
      simp only [↓reduceIte] at htail hlen_code lZero c₃ ⊢
      have i36 : CodeAt P (a + 36) [.pop t₁] := by
        have h := htail.at_offset 3 (by simp)
        simpa [Nat.add_assoc] using h
      let c₄ : Config := { c₃ with pc := a + 37, stk := Function.update c₃.stk t₁ (cfg.stk t₁) }
      have s3 : Steps P c₃ c₄ (1 + len 0) := Steps.pop i36 rfl c₃t1
      have hk_end : Keeps allStks5 c₂ c₄ :=
        (Keeps.update_stk_mem c₂ (a + 36) m4 _).trans (Keeps.update_stk_mem c₃ (a + 37) m1 _)
      have hkeeps : Keeps [s] cfg c₄ := (hk01.trans hk_end).of_subset_eq fun w hw hnot => by
        simp only [allStks5, List.mem_cons, List.not_mem_nil, or_false] at hw hnot
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl hnot
        · simp [c₄]
        · simp [c₄, h12.symm, c₃t2]
        · simp [c₄, h13.symm, c₃t3]
        · simp [c₄, h14.symm, c₃t4]
        · simp [c₄, h15.symm, c₃t5]
      refine ⟨c₄, _, ((s0.trans s1).trans s2).trans s3, ?_, ?_, hkeeps, ?_⟩
      · simp [c₄, hlen_code]
      · simp [c₄, hs1, c₃s]
      · simp only [GI.Machine.len_zero]
        have h1 : len x + 0 + 1 ≤ (len x + 0 + 1) ^ 2 := Nat.le_self_pow (by omega) _
        omega
  · -- Main case: y > 0.
    have hy_pos : 0 < y := Nat.pos_of_ne_zero hy
    have i3 : CodeAt P (a + 3) [.move s t₂] := by simpa using hpref.at_offset 3 (by simp)
    have i4 : CodeAt P (a + 4) [.push s 0] := by simpa using hpref.at_offset 4 (by simp)
    have i5 : CodeAt P (a + 5) [.push t₃ 0] := by simpa using hpref.at_offset 5 (by simp)
    have i6 : CodeAt P (a + 6) [.copy t₂ t₄] := by simpa using hpref.at_offset 6 (by simp)
    have i7 : CodeAt P (a + 7) [.jz t₄ (a + 14)] := by simpa using hpref.at_offset 7 (by simp)
    have i8 : CodeAt P (a + 8) [.copy t₂ t₃] := by simpa using hpref.at_offset 8 (by simp)
    have i9 : CodeAt P (a + 9) [.parity t₃] := by simpa using hpref.at_offset 9 (by simp)
    have i10 : CodeAt P (a + 10) [.push t₄ 1] := by simpa using hpref.at_offset 10 (by simp)
    have i11 : CodeAt P (a + 11) [.add t₃ t₄] := by simpa using hpref.at_offset 11 (by simp)
    have i12 : CodeAt P (a + 12) [.half t₂] := by simpa using hpref.at_offset 12 (by simp)
    have i13 : CodeAt P (a + 13) [.jmp (a + 6)] := by simpa using hpref.at_offset 13 (by simp)
    have i14 : CodeAt P (a + 14) [.copy t₃ t₄] := by simpa using hpref.at_offset 14 (by simp)
    have i15 : CodeAt P (a + 15) [.jz t₄ (a + 31)] := by simpa using hpref.at_offset 15 (by simp)
    have i16 : CodeAt P (a + 16) [.push t₄ 1] := by simpa using hpref.at_offset 16 (by simp)
    have i17 : CodeAt P (a + 17) [.sub t₃ t₄] := by simpa using hpref.at_offset 17 (by simp)
    have i18 : CodeAt P (a + 18) [.double t₂] := by simpa using hpref.at_offset 18 (by simp)
    have i19 : CodeAt P (a + 19) [.add t₂ t₃] := by simpa using hpref.at_offset 19 (by simp)
    have i20 : CodeAt P (a + 20) [.double s] := by simpa using hpref.at_offset 20 (by simp)
    have i21 : CodeAt P (a + 21) [.copy t₁ t₄] := by simpa using hpref.at_offset 21 (by simp)
    have i22 : CodeAt P (a + 22) [.copy t₂ t₅] := by simpa using hpref.at_offset 22 (by simp)
    have i23 : CodeAt P (a + 23) [.sub t₄ t₅] := by simpa using hpref.at_offset 23 (by simp)
    have i24 : CodeAt P (a + 24) [.jz t₄ (a + 26)] := by simpa using hpref.at_offset 24 (by simp)
    have i25 : CodeAt P (a + 25) [.jmp (a + 14)] := by simpa using hpref.at_offset 25 (by simp)
    have i26 : CodeAt P (a + 26) [.copy t₁ t₄] := by simpa using hpref.at_offset 26 (by simp)
    have i27 : CodeAt P (a + 27) [.sub t₂ t₄] := by simpa using hpref.at_offset 27 (by simp)
    have i28 : CodeAt P (a + 28) [.push t₄ 1] := by simpa using hpref.at_offset 28 (by simp)
    have i29 : CodeAt P (a + 29) [.add s t₄] := by simpa using hpref.at_offset 29 (by simp)
    have i30 : CodeAt P (a + 30) [.jmp (a + 14)] := by simpa using hpref.at_offset 30 (by simp)
    have i31 : CodeAt P (a + 31) [.pop t₃] := by simpa using hpref.at_offset 31 (by simp)
    have i32 : CodeAt P (a + 32) [.pop t₁] := by simpa using hpref.at_offset 32 (by simp)
    -- Fall through jz, setup q = 0, n = x, sentinel 0 on t₃.
    let c₃ : Config := { c₂ with pc := a + 3, stk := Function.update c₂.stk t₄ (cfg.stk t₄) }
    have s2 : Steps P c₂ c₃ (1 + len y) := Steps.jz_ne_zero i2 rfl c₂t4 hy
    have c₃s : c₃.stk s = x :: rest := by simp [c₃, hs4, c₂s]
    have c₃t1 : c₃.stk t₁ = y :: cfg.stk t₁ := by simp [c₃, h14, c₂t1]
    have c₃t2 : c₃.stk t₂ = cfg.stk t₂ := by simp [c₃, h24, c₂t2]
    have c₃t3 : c₃.stk t₃ = cfg.stk t₃ := by simp [c₃, h34, c₂t3]
    have c₃t4 : c₃.stk t₄ = cfg.stk t₄ := by simp [c₃]
    have c₃t5 : c₃.stk t₅ = cfg.stk t₅ := by simp [c₃, h45.symm, c₂t5]
    let c₄ : Config :=
      { c₃ with pc := a + 4, stk := Function.update (Function.update c₃.stk s rest) t₂ (x :: c₃.stk t₂) }
    have s3 : Steps P c₃ c₄ (1 + len x) := Steps.move_ne hs2 i3 rfl c₃s
    have c₄s : c₄.stk s = rest := by simp [c₄, hs2]
    have c₄t1 : c₄.stk t₁ = y :: cfg.stk t₁ := by simp [c₄, h12, hs1.symm, c₃t1]
    have c₄t2 : c₄.stk t₂ = x :: cfg.stk t₂ := by simp [c₄, c₃t2]
    have c₄t3 : c₄.stk t₃ = cfg.stk t₃ := by simp [c₄, h23.symm, hs3.symm, c₃t3]
    have c₄t4 : c₄.stk t₄ = cfg.stk t₄ := by simp [c₄, h24.symm, hs4.symm, c₃t4]
    have c₄t5 : c₄.stk t₅ = cfg.stk t₅ := by simp [c₄, h25.symm, hs5.symm, c₃t5]
    let c₅ : Config := { c₄ with pc := a + 5, stk := Function.update c₄.stk s (0 :: c₄.stk s) }
    have s4 : Steps P c₄ c₅ (1 + len 0) := Steps.push i4 rfl
    have c₅s : c₅.stk s = 0 :: rest := by simp [c₅, c₄s]
    have c₅t1 : c₅.stk t₁ = y :: cfg.stk t₁ := by simp [c₅, hs1.symm, c₄t1]
    have c₅t2 : c₅.stk t₂ = x :: cfg.stk t₂ := by simp [c₅, hs2.symm, c₄t2]
    have c₅t3 : c₅.stk t₃ = cfg.stk t₃ := by simp [c₅, hs3.symm, c₄t3]
    have c₅t4 : c₅.stk t₄ = cfg.stk t₄ := by simp [c₅, hs4.symm, c₄t4]
    have c₅t5 : c₅.stk t₅ = cfg.stk t₅ := by simp [c₅, hs5.symm, c₄t5]
    let c₆ : Config := { c₅ with pc := a + 6, stk := Function.update c₅.stk t₃ (0 :: c₅.stk t₃) }
    have s5 : Steps P c₅ c₆ (1 + len 0) := Steps.push i5 rfl
    have c₆s : c₆.stk s = 0 :: rest := by simp [c₆, hs3, c₅s]
    have c₆t1 : c₆.stk t₁ = y :: cfg.stk t₁ := by simp [c₆, h13, c₅t1]
    have c₆t2 : c₆.stk t₂ = x :: cfg.stk t₂ := by simp [c₆, h23, c₅t2]
    have c₆t3 : c₆.stk t₃ = 0 :: cfg.stk t₃ := by simp [c₆, c₅t3]
    have c₆t4 : c₆.stk t₄ = cfg.stk t₄ := by simp [c₆, h34.symm, c₅t4]
    have c₆t5 : c₆.stk t₅ = cfg.stk t₅ := by simp [c₆, h35.symm, c₅t5]
    have hk_setup : Keeps allStks5 cfg c₆ :=
      (((hk01.trans (Keeps.update_stk_mem c₂ (a + 3) m4 _)).trans
        (Keeps.update_stk₂_mem c₃ (a + 4) m2 ms _ _)).trans
        (Keeps.update_stk_mem c₄ (a + 5) ms _)).trans
        (Keeps.update_stk_mem c₅ (a + 6) m3 _)
    -- Loop 1: extract digits of x onto t₃.
    let Inv1 : Config → Prop := fun c =>
      c.pc = a + 6 ∧ Keeps allStks5 cfg c ∧
      c.stk s = 0 :: rest ∧ c.stk t₁ = y :: cfg.stk t₁ ∧
      c.stk t₄ = cfg.stk t₄ ∧ c.stk t₅ = cfg.stk t₅ ∧
      ∃ n ds, c.stk t₂ = n :: cfg.stk t₂ ∧ c.stk t₃ = ds ++ (0 :: cfg.stk t₃) ∧
        (∀ d ∈ ds, d = 1 ∨ d = 2) ∧ fromDigits n ds = x ∧ ds.length + len n = len x
    let Done1 : Config → Prop := fun c =>
      c.pc = a + 14 ∧ Keeps allStks5 cfg c ∧
      c.stk s = 0 :: rest ∧ c.stk t₁ = y :: cfg.stk t₁ ∧ c.stk t₂ = 0 :: cfg.stk t₂ ∧
      c.stk t₄ = cfg.stk t₄ ∧ c.stk t₅ = cfg.stk t₅ ∧
      ∃ ds, c.stk t₃ = ds ++ (0 :: cfg.stk t₃) ∧
        (∀ d ∈ ds, d = 1 ∨ d = 2) ∧ fromDigits 0 ds = x ∧ ds.length = len x
    let μ1 : Config → ℕ := fun c => len (c.stk t₂).head!
    have hloop1 : ∀ c, Inv1 c →
        ∃ c' S, Steps P c c' S ∧ Done1 c' ∧ S ≤ μ1 c * (12 + 5 * len x) + 2 := by
      refine Steps.loop Inv1 Done1 μ1 (12 + 5 * len x) 2 (fun c hI => ?_)
      obtain ⟨hpc_c, hk_c, hcs, hct1, hct4, hct5, n, ds, hct2, hct3, hds, hfd, hdl⟩ := hI
      let d₁ : Config := { c with pc := a + 7, stk := Function.update c.stk t₄ (n :: c.stk t₄) }
      have st6 : Steps P c d₁ (1 + len n) := Steps.copy i6 hpc_c hct2
      have d₁t4 : d₁.stk t₄ = n :: cfg.stk t₄ := by simp [d₁, hct4]
      by_cases hn : n = 0
      · subst hn
        let d₂ : Config := { d₁ with pc := a + 14, stk := Function.update d₁.stk t₄ (cfg.stk t₄) }
        have st7 : Steps P d₁ d₂ 1 := Steps.jz_zero i7 rfl d₁t4
        have hk_st : Keeps allStks5 c d₂ :=
          (Keeps.update_stk_mem c (a + 7) m4 _).trans (Keeps.update_stk_mem d₁ (a + 14) m4 _)
        refine Or.inl ⟨d₂, _, st6.trans st7, ⟨rfl, hk_c.trans hk_st,
          by simp [d₂, d₁, hs4, hcs], by simp [d₂, d₁, h14, hct1], by simp [d₂, d₁, h24, hct2],
          by simp [d₂], by simp [d₂, d₁, h45.symm, hct5],
          ds, by simp [d₂, d₁, h34, hct3], hds, hfd, by simpa [GI.Machine.len_zero] using hdl⟩, ?_⟩
        simp [GI.Machine.len_zero]
      · let d₂ : Config := { d₁ with pc := a + 8, stk := Function.update d₁.stk t₄ (cfg.stk t₄) }
        have st7 : Steps P d₁ d₂ (1 + len n) := Steps.jz_ne_zero i7 rfl d₁t4 hn
        have d₂t2 : d₂.stk t₂ = n :: cfg.stk t₂ := by simp [d₂, d₁, h24, hct2]
        have d₂t3 : d₂.stk t₃ = ds ++ (0 :: cfg.stk t₃) := by simp [d₂, d₁, h34, hct3]
        have d₂t4 : d₂.stk t₄ = cfg.stk t₄ := by simp [d₂]
        let d₃ : Config := { d₂ with pc := a + 9, stk := Function.update d₂.stk t₃ (n :: d₂.stk t₃) }
        have st8 : Steps P d₂ d₃ (1 + len n) := Steps.copy i8 rfl d₂t2
        have d₃t3 : d₃.stk t₃ = n :: ds ++ (0 :: cfg.stk t₃) := by simp [d₃, d₂t3]
        let d₄ : Config := { d₃ with pc := a + 10, stk := Function.update d₃.stk t₃ ((n % 2) :: ds ++ (0 :: cfg.stk t₃)) }
        have st9 : Steps P d₃ d₄ (1 + len n) := Steps.parity i9 rfl d₃t3
        have d₄t3 : d₄.stk t₃ = (n % 2) :: ds ++ (0 :: cfg.stk t₃) := by simp [d₄]
        have d₄t4 : d₄.stk t₄ = cfg.stk t₄ := by simp [d₄, d₃, h34.symm, d₂t4]
        let d₅ : Config := { d₄ with pc := a + 11, stk := Function.update d₄.stk t₄ (1 :: d₄.stk t₄) }
        have st10 : Steps P d₄ d₅ (1 + len 1) := Steps.push i10 rfl
        have d₅t3 : d₅.stk t₃ = (n % 2) :: ds ++ (0 :: cfg.stk t₃) := by simp [d₅, h34, d₄t3]
        have d₅t4 : d₅.stk t₄ = 1 :: cfg.stk t₄ := by simp [d₅, d₄t4]
        let d₆ : Config := { d₅ with pc := a + 12, stk := Function.update (Function.update d₅.stk t₄ (cfg.stk t₄)) t₃ (((n % 2) + 1) :: ds ++ (0 :: cfg.stk t₃)) }
        have st11 : Steps P d₅ d₆ (1 + len (n % 2) + len 1) := Steps.add h34 i11 rfl d₅t3 d₅t4
        have d₆t2 : d₆.stk t₂ = n :: cfg.stk t₂ := by simp [d₆, d₅, d₄, d₃, h23, h24, d₂t2]
        let d₇ : Config := { d₆ with pc := a + 13, stk := Function.update d₆.stk t₂ ((n / 2) :: cfg.stk t₂) }
        have st12 : Steps P d₆ d₇ (1 + len n) := Steps.half i12 rfl d₆t2
        let d₈ : Config := { d₇ with pc := a + 6 }
        have st13 : Steps P d₇ d₈ 1 := Steps.jmp i13 rfl
        have hk_st : Keeps allStks5 c d₈ :=
          ((((((Keeps.update_stk_mem c (a + 7) m4 _).trans
            (Keeps.update_stk_mem d₁ (a + 8) m4 _)).trans
            (Keeps.update_stk_mem d₂ (a + 9) m3 _)).trans
            (Keeps.update_stk_mem d₃ (a + 10) m3 _)).trans
            (Keeps.update_stk_mem d₄ (a + 11) m4 _)).trans
            (Keeps.update_stk₂_mem d₅ (a + 12) m3 m4 _ _)).trans
            ((Keeps.update_stk_mem d₆ (a + 13) m2 _).trans
              (Keeps.with_pc_mem allStks5 d₇ (a + 6)))
        have hInv1' : Inv1 d₈ := by
          refine ⟨rfl, hk_c.trans hk_st,
            by simp [d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, hs2, hs3, hs4, hcs],
            by simp [d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, h12, h13, h14, hct1],
            by simp [d₈, d₇, d₆, h24.symm, h34.symm],
            by simp [d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, h25.symm, h35.symm, h45.symm, hct5],
            n / 2, (n % 2 + 1) :: ds,
            by simp [d₈, d₇],
            by simp [d₈, d₇, d₆, h23.symm],
            fun d hd => ?_, ?_, ?_⟩
          · simp only [List.mem_cons] at hd
            rcases hd with rfl | hmem
            · omega
            · exact hds d hmem
          · simp only [fromDigits, Nat.add_sub_cancel]
            rw [Nat.div_add_mod n 2]
            exact hfd
          · simp only [List.length_cons]
            have := len_div_two_add_one hn
            omega
        have hμ_lt : μ1 d₈ < μ1 c := by
          simp only [μ1, d₈, d₇, Function.update_self, hct2, List.head!_cons]
          exact len_div_two_lt hn
        refine Or.inr ⟨d₈, _,
          ((((((st6.trans st7).trans st8).trans st9).trans st10).trans st11).trans st12).trans st13,
          hInv1', hμ_lt, ?_⟩
        have hm := len_mod_two_le n
        simp only [GI.Machine.len_one]
        omega
    have hInv1_0 : Inv1 c₆ :=
      ⟨rfl, hk_setup, c₆s, c₆t1, c₆t4, c₆t5, x, [], c₆t2, by simp [c₆t3], by simp, rfl, by simp⟩
    obtain ⟨c₇, S₁, hst1, hDone1, hS₁⟩ := hloop1 c₆ hInv1_0
    have hμ1_0 : μ1 c₆ = len x := by simp [μ1, c₆t2]
    rw [hμ1_0] at hS₁
    -- Loop 2: process digits from t₃ highest first.
    let Inv2 : Config → Prop := fun c =>
      c.pc = a + 14 ∧ Keeps allStks5 cfg c ∧
      c.stk t₁ = y :: cfg.stk t₁ ∧ c.stk t₄ = cfg.stk t₄ ∧ c.stk t₅ = cfg.stk t₅ ∧
      ∃ q r ds, c.stk s = q :: rest ∧ c.stk t₂ = r :: cfg.stk t₂ ∧
        c.stk t₃ = ds ++ (0 :: cfg.stk t₃) ∧
        (∀ d ∈ ds, d = 1 ∨ d = 2) ∧ r < y ∧ fromDigits (q * y + r) ds = x
    let Done2 : Config → Prop := fun c =>
      c.pc = a + 31 ∧ Keeps allStks5 cfg c ∧
      c.stk t₁ = y :: cfg.stk t₁ ∧ c.stk t₃ = 0 :: cfg.stk t₃ ∧
      c.stk t₄ = cfg.stk t₄ ∧ c.stk t₅ = cfg.stk t₅ ∧
      ∃ q r, c.stk s = q :: rest ∧ c.stk t₂ = r :: cfg.stk t₂ ∧ r < y ∧ q * y + r = x
    let μ2 : Config → ℕ := fun c => (c.stk t₃).length - (cfg.stk t₃).length - 1
    have hloop2 : ∀ c, Inv2 c →
        ∃ c' S, Steps P c c' S ∧ Done2 c' ∧ S ≤ μ2 c * (36 + 2 * len x + 10 * len y) + 2 := by
      refine Steps.loop Inv2 Done2 μ2 (36 + 2 * len x + 10 * len y) 2 (fun c hI => ?_)
      obtain ⟨hpc_c, hk_c, hct1, hct4, hct5, q, r, ds, hcs, hct2, hct3, hds, hry, hfd⟩ := hI
      cases ds with
      | nil =>
        simp only [List.nil_append] at hct3
        let d₁ : Config := { c with pc := a + 15, stk := Function.update c.stk t₄ (0 :: c.stk t₄) }
        have st14 : Steps P c d₁ (1 + len 0) := Steps.copy i14 hpc_c hct3
        have d₁t4 : d₁.stk t₄ = 0 :: cfg.stk t₄ := by simp [d₁, hct4]
        let d₂ : Config := { d₁ with pc := a + 31, stk := Function.update d₁.stk t₄ (cfg.stk t₄) }
        have st15 : Steps P d₁ d₂ 1 := Steps.jz_zero i15 rfl d₁t4
        have hk_st : Keeps allStks5 c d₂ :=
          (Keeps.update_stk_mem c (a + 15) m4 _).trans (Keeps.update_stk_mem d₁ (a + 31) m4 _)
        refine Or.inl ⟨d₂, _, st14.trans st15, ⟨rfl, hk_c.trans hk_st,
          by simp [d₂, d₁, h14, hct1], by simp [d₂, d₁, h34, hct3],
          by simp [d₂], by simp [d₂, d₁, h45.symm, hct5],
          q, r, by simp [d₂, d₁, hs4, hcs], by simp [d₂, d₁, h24, hct2], hry, hfd⟩, ?_⟩
        simp [GI.Machine.len_zero]
      | cons d ds' =>
        simp only [List.cons_append] at hct3
        have hd_cases : d = 1 ∨ d = 2 := hds d (by simp)
        have hd_ne : d ≠ 0 := by omega
        have hd_len : len d ≤ 2 := by
          rcases hd_cases with rfl | rfl
          · simp [GI.Machine.len_one]
          · rw [GI.Machine.len_le_iff]; omega
        have hq_le_x : q ≤ x := by
          have h1 : q * y + r ≤ x := hfd ▸ le_fromDigits _ _
          have h2 : q ≤ q * y := Nat.le_mul_of_pos_right q hy_pos
          omega
        have hq_len : len q ≤ len x := GI.Machine.len_mono hq_le_x
        have hr_len : len r ≤ len y := GI.Machine.len_mono (le_of_lt hry)
        let r' := 2 * r + (d - 1)
        have hr'_len : len r' ≤ len y + 1 :=
          le_trans (len_two_mul_add_bit_le (by omega)) (by omega)
        have h2r_len : len (2 * r) ≤ len y + 1 :=
          le_trans (len_two_mul_le r) (by omega)
        have hdm1_len : len (d - 1) ≤ 1 := GI.Machine.len_le_one_iff.mpr (by omega)
        let d₁ : Config := { c with pc := a + 15, stk := Function.update c.stk t₄ (d :: c.stk t₄) }
        have st14 : Steps P c d₁ (1 + len d) := Steps.copy i14 hpc_c hct3
        have d₁t4 : d₁.stk t₄ = d :: cfg.stk t₄ := by simp [d₁, hct4]
        let d₂ : Config := { d₁ with pc := a + 16, stk := Function.update d₁.stk t₄ (cfg.stk t₄) }
        have st15 : Steps P d₁ d₂ (1 + len d) := Steps.jz_ne_zero i15 rfl d₁t4 hd_ne
        have d₂t4 : d₂.stk t₄ = cfg.stk t₄ := by simp [d₂]
        let d₃ : Config := { d₂ with pc := a + 17, stk := Function.update d₂.stk t₄ (1 :: d₂.stk t₄) }
        have st16 : Steps P d₂ d₃ (1 + len 1) := Steps.push i16 rfl
        have d₃t3 : d₃.stk t₃ = d :: (ds' ++ (0 :: cfg.stk t₃)) := by simp [d₃, d₂, d₁, h34, hct3]
        have d₃t4 : d₃.stk t₄ = 1 :: cfg.stk t₄ := by simp [d₃, d₂t4]
        let d₄ : Config := { d₃ with pc := a + 18, stk := Function.update (Function.update d₃.stk t₄ (cfg.stk t₄)) t₃ ((d - 1) :: (ds' ++ (0 :: cfg.stk t₃))) }
        have st17 : Steps P d₃ d₄ (1 + len d + len 1) := Steps.sub h34 i17 rfl d₃t3 d₃t4
        have d₄t2 : d₄.stk t₂ = r :: cfg.stk t₂ := by simp [d₄, d₃, d₂, d₁, h23, h24, hct2]
        have d₄t3 : d₄.stk t₃ = (d - 1) :: (ds' ++ (0 :: cfg.stk t₃)) := by simp [d₄]
        let d₅ : Config := { d₄ with pc := a + 19, stk := Function.update d₄.stk t₂ ((2 * r) :: cfg.stk t₂) }
        have st18 : Steps P d₄ d₅ (1 + len r) := Steps.double i18 rfl d₄t2
        have d₅t2 : d₅.stk t₂ = (2 * r) :: cfg.stk t₂ := by simp [d₅]
        have d₅t3 : d₅.stk t₃ = (d - 1) :: (ds' ++ (0 :: cfg.stk t₃)) := by simp [d₅, h23.symm, d₄t3]
        let d₆ : Config := { d₅ with pc := a + 20, stk := Function.update (Function.update d₅.stk t₃ (ds' ++ (0 :: cfg.stk t₃))) t₂ (r' :: cfg.stk t₂) }
        have st19 : Steps P d₅ d₆ (1 + len (2 * r) + len (d - 1)) := Steps.add h23 i19 rfl d₅t2 d₅t3
        have d₆s : d₆.stk s = q :: rest := by simp [d₆, d₅, d₄, d₃, d₂, d₁, hs2, hs3, hs4, hcs]
        let d₇ : Config := { d₆ with pc := a + 21, stk := Function.update d₆.stk s ((2 * q) :: rest) }
        have st20 : Steps P d₆ d₇ (1 + len q) := Steps.double i20 rfl d₆s
        have d₇t1 : d₇.stk t₁ = y :: cfg.stk t₁ := by simp [d₇, d₆, d₅, d₄, d₃, d₂, d₁, hs1.symm, h12, h13, h14, hct1]
        have d₇t2 : d₇.stk t₂ = r' :: cfg.stk t₂ := by simp [d₇, d₆, hs2.symm]
        have d₇t3 : d₇.stk t₃ = ds' ++ (0 :: cfg.stk t₃) := by simp [d₇, d₆, hs3.symm, h23.symm]
        have d₇t4 : d₇.stk t₄ = cfg.stk t₄ := by simp [d₇, d₆, d₅, d₄, hs4.symm, h24.symm, h34.symm]
        have d₇t5 : d₇.stk t₅ = cfg.stk t₅ := by simp [d₇, d₆, d₅, d₄, d₃, d₂, d₁, hs5.symm, h25.symm, h35.symm, h45.symm, hct5]
        let d₈ : Config := { d₇ with pc := a + 22, stk := Function.update d₇.stk t₄ (y :: d₇.stk t₄) }
        have st21 : Steps P d₇ d₈ (1 + len y) := Steps.copy i21 rfl d₇t1
        have d₈t2 : d₈.stk t₂ = r' :: cfg.stk t₂ := by simp [d₈, h24, d₇t2]
        have d₈t4 : d₈.stk t₄ = y :: cfg.stk t₄ := by simp [d₈, d₇t4]
        have d₈t5 : d₈.stk t₅ = cfg.stk t₅ := by simp [d₈, h45.symm, d₇t5]
        let d₉ : Config := { d₈ with pc := a + 23, stk := Function.update d₈.stk t₅ (r' :: d₈.stk t₅) }
        have st22 : Steps P d₈ d₉ (1 + len r') := Steps.copy i22 rfl d₈t2
        have d₉t4 : d₉.stk t₄ = y :: cfg.stk t₄ := by simp [d₉, h45, d₈t4]
        have d₉t5 : d₉.stk t₅ = r' :: cfg.stk t₅ := by simp [d₉, d₈t5]
        let d₁₀ : Config := { d₉ with pc := a + 24, stk := Function.update (Function.update d₉.stk t₅ (cfg.stk t₅)) t₄ ((y - r') :: cfg.stk t₄) }
        have st23 : Steps P d₉ d₁₀ (1 + len y + len r') := Steps.sub h45 i23 rfl d₉t4 d₉t5
        have d₁₀s : d₁₀.stk s = (2 * q) :: rest := by simp [d₁₀, d₉, d₈, d₇, hs4, hs5]
        have d₁₀t1 : d₁₀.stk t₁ = y :: cfg.stk t₁ := by simp [d₁₀, d₉, d₈, h14, h15, d₇t1]
        have d₁₀t2 : d₁₀.stk t₂ = r' :: cfg.stk t₂ := by simp [d₁₀, d₉, d₈, h24, h25, d₇t2]
        have d₁₀t3 : d₁₀.stk t₃ = ds' ++ (0 :: cfg.stk t₃) := by simp [d₁₀, d₉, d₈, h34, h35, d₇t3]
        have d₁₀t4 : d₁₀.stk t₄ = (y - r') :: cfg.stk t₄ := by simp [d₁₀]
        have d₁₀t5 : d₁₀.stk t₅ = cfg.stk t₅ := by simp [d₁₀, h45.symm]
        have hk_pre : Keeps allStks5 c d₁₀ :=
          (((((((((Keeps.update_stk_mem c (a + 15) m4 _).trans
            (Keeps.update_stk_mem d₁ (a + 16) m4 _)).trans
            (Keeps.update_stk_mem d₂ (a + 17) m4 _)).trans
            (Keeps.update_stk₂_mem d₃ (a + 18) m3 m4 _ _)).trans
            (Keeps.update_stk_mem d₄ (a + 19) m2 _)).trans
            (Keeps.update_stk₂_mem d₅ (a + 20) m2 m3 _ _)).trans
            (Keeps.update_stk_mem d₆ (a + 21) ms _)).trans
            (Keeps.update_stk_mem d₇ (a + 22) m4 _)).trans
            (Keeps.update_stk_mem d₈ (a + 23) m5 _)).trans
            (Keeps.update_stk₂_mem d₉ (a + 24) m4 m5 _ _)
        have st_pre := (((((((((st14.trans st15).trans st16).trans st17).trans st18).trans st19).trans st20).trans st21).trans st22).trans st23)
        have hds' : ∀ d' ∈ ds', d' = 1 ∨ d' = 2 := fun d' hd' => hds d' (by simp [hd'])
        by_cases hge : y ≤ r'
        · -- y ≤ r': subtract y from r' and add 1 to 2*q.
          have hsub0 : y - r' = 0 := by omega
          let e₁ : Config := { d₁₀ with pc := a + 26, stk := Function.update d₁₀.stk t₄ (cfg.stk t₄) }
          have st24 : Steps P d₁₀ e₁ 1 := Steps.jz_zero i24 rfl (by rw [d₁₀t4, hsub0])
          have e₁t1 : e₁.stk t₁ = y :: cfg.stk t₁ := by simp [e₁, h14, d₁₀t1]
          have e₁t4 : e₁.stk t₄ = cfg.stk t₄ := by simp [e₁]
          let e₂ : Config := { e₁ with pc := a + 27, stk := Function.update e₁.stk t₄ (y :: e₁.stk t₄) }
          have st26 : Steps P e₁ e₂ (1 + len y) := Steps.copy i26 rfl e₁t1
          have e₂t2 : e₂.stk t₂ = r' :: cfg.stk t₂ := by simp [e₂, e₁, h24, d₁₀t2]
          have e₂t4 : e₂.stk t₄ = y :: cfg.stk t₄ := by simp [e₂, e₁t4]
          let e₃ : Config := { e₂ with pc := a + 28, stk := Function.update (Function.update e₂.stk t₄ (cfg.stk t₄)) t₂ ((r' - y) :: cfg.stk t₂) }
          have st27 : Steps P e₂ e₃ (1 + len r' + len y) := Steps.sub h24 i27 rfl e₂t2 e₂t4
          have e₃t4 : e₃.stk t₄ = cfg.stk t₄ := by simp [e₃, h24.symm]
          let e₄ : Config := { e₃ with pc := a + 29, stk := Function.update e₃.stk t₄ (1 :: e₃.stk t₄) }
          have st28 : Steps P e₃ e₄ (1 + len 1) := Steps.push i28 rfl
          have e₄s : e₄.stk s = (2 * q) :: rest := by simp [e₄, e₃, e₂, e₁, hs4, hs2, d₁₀s]
          have e₄t4 : e₄.stk t₄ = 1 :: cfg.stk t₄ := by simp [e₄, e₃t4]
          let e₅ : Config := { e₄ with pc := a + 30, stk := Function.update (Function.update e₄.stk t₄ (cfg.stk t₄)) s ((2 * q + 1) :: rest) }
          have st29 : Steps P e₄ e₅ (1 + len (2 * q) + len 1) := Steps.add hs4 i29 rfl e₄s e₄t4
          let e₆ : Config := { e₅ with pc := a + 14 }
          have st30 : Steps P e₅ e₆ 1 := Steps.jmp i30 rfl
          have hk_post : Keeps allStks5 d₁₀ e₆ :=
            (((((Keeps.update_stk_mem d₁₀ (a + 26) m4 _).trans
              (Keeps.update_stk_mem e₁ (a + 27) m4 _)).trans
              (Keeps.update_stk₂_mem e₂ (a + 28) m2 m4 _ _)).trans
              (Keeps.update_stk_mem e₃ (a + 29) m4 _)).trans
              (Keeps.update_stk₂_mem e₄ (a + 30) ms m4 _ _)).trans
              (Keeps.with_pc_mem allStks5 e₅ (a + 14))
          have heq_new : (2 * q + 1) * y + (r' - y) = 2 * (q * y + r) + (d - 1) := by
            have : (2 * q + 1) * y = 2 * (q * y) + y := by ring
            omega
          have hInv2' : Inv2 e₆ := by
            refine ⟨rfl, (hk_c.trans hk_pre).trans hk_post,
              by simp [e₆, e₅, e₄, e₃, e₂, e₁, hs1.symm, h14, h12, d₁₀t1],
              by simp [e₆, e₅, hs4.symm],
              by simp [e₆, e₅, e₄, e₃, e₂, e₁, hs5.symm, h45.symm, h25.symm, d₁₀t5],
              2 * q + 1, r' - y, ds',
              by simp [e₆, e₅],
              by simp [e₆, e₅, e₄, e₃, hs2.symm, h24],
              by simp [e₆, e₅, e₄, e₃, e₂, e₁, hs3.symm, h34, h23.symm, d₁₀t3],
              hds', by omega, ?_⟩
            rw [heq_new]
            exact hfd
          have hμ_lt : μ2 e₆ < μ2 c := by
            have h3e : e₆.stk t₃ = ds' ++ (0 :: cfg.stk t₃) := by
              simp [e₆, e₅, e₄, e₃, e₂, e₁, hs3.symm, h34, h23.symm, d₁₀t3]
            simp only [μ2, h3e, hct3, List.length_cons, List.length_append]
            omega
          have h2q_len : len (2 * q) ≤ len x + 1 := le_trans (len_two_mul_le q) (by omega)
          refine Or.inr ⟨e₆, _,
            st_pre.trans (((((st24.trans st26).trans st27).trans st28).trans st29).trans st30),
            hInv2', hμ_lt, ?_⟩
          simp only [GI.Machine.len_one]
          omega
        · -- r' < y: jump back to a + 14.
          have hsub_ne : y - r' ≠ 0 := by omega
          let e₁ : Config := { d₁₀ with pc := a + 25, stk := Function.update d₁₀.stk t₄ (cfg.stk t₄) }
          have st24 : Steps P d₁₀ e₁ (1 + len (y - r')) := Steps.jz_ne_zero i24 rfl d₁₀t4 hsub_ne
          let e₂ : Config := { e₁ with pc := a + 14 }
          have st25 : Steps P e₁ e₂ 1 := Steps.jmp i25 rfl
          have hk_post : Keeps allStks5 d₁₀ e₂ :=
            (Keeps.update_stk_mem d₁₀ (a + 25) m4 _).trans
              (Keeps.with_pc_mem allStks5 e₁ (a + 14))
          have heq_new : (2 * q) * y + r' = 2 * (q * y + r) + (d - 1) := by
            simp only [r']; ring
          have hInv2' : Inv2 e₂ := by
            refine ⟨rfl, (hk_c.trans hk_pre).trans hk_post,
              by simp [e₂, e₁, h14, d₁₀t1],
              by simp [e₂, e₁],
              by simp [e₂, e₁, h45.symm, d₁₀t5],
              2 * q, r', ds',
              by simp [e₂, e₁, hs4, d₁₀s],
              by simp [e₂, e₁, h24, d₁₀t2],
              by simp [e₂, e₁, h34, d₁₀t3],
              hds', by omega, ?_⟩
            rw [heq_new]
            exact hfd
          have hμ_lt : μ2 e₂ < μ2 c := by
            have h3e : e₂.stk t₃ = ds' ++ (0 :: cfg.stk t₃) := by simp [e₂, e₁, h34, d₁₀t3]
            simp only [μ2, h3e, hct3, List.length_cons, List.length_append]
            omega
          have hsub_len : len (y - r') ≤ len y := GI.Machine.len_sub_le y r'
          refine Or.inr ⟨e₂, _, st_pre.trans (st24.trans st25), hInv2', hμ_lt, ?_⟩
          simp only [GI.Machine.len_one]
          omega
    obtain ⟨hc₇pc, hk_c₇, hc₇s, hc₇t1, hc₇t2, hc₇t4, hc₇t5, ds0, hc₇t3, hds0, hfd0, hds0_len⟩ := hDone1
    have hInv2_0 : Inv2 c₇ :=
      ⟨hc₇pc, hk_c₇, hc₇t1, hc₇t4, hc₇t5, 0, 0, ds0, hc₇s, hc₇t2, hc₇t3, hds0, hy_pos, by simpa using hfd0⟩
    obtain ⟨c₈, S₂, hst2, hDone2, hS₂⟩ := hloop2 c₇ hInv2_0
    have hμ2_0 : μ2 c₇ = len x := by
      simp only [μ2, hc₇t3, List.length_append, List.length_cons, hds0_len]
      omega
    rw [hμ2_0] at hS₂
    -- Cleanup at a + 31.
    obtain ⟨hc₈pc, hk_c₈, hc₈t1, hc₈t3, hc₈t4, hc₈t5, q, r, hc₈s, hc₈t2, hry, hqr⟩ := hDone2
    have hq_eq : q = x / y := by
      have hq1 : (q * y + r) / y = q := by
        rw [Nat.mul_comm, Nat.mul_add_div hy_pos, Nat.div_eq_of_lt hry, Nat.add_zero]
      rw [← hqr, hq1]
    have hr_eq : r = x % y := by
      have h1 : (q * y + r) % y = r := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hry]
      rw [← hqr, h1]
    have hq_len : len q ≤ len x := by rw [hq_eq]; exact GI.Machine.len_div_le x y
    have hr_len : len r ≤ len y := GI.Machine.len_mono (le_of_lt hry)
    let c₉ : Config := { c₈ with pc := a + 32, stk := Function.update c₈.stk t₃ (cfg.stk t₃) }
    have st31 : Steps P c₈ c₉ (1 + len 0) := Steps.pop i31 hc₈pc hc₈t3
    have c₉t1 : c₉.stk t₁ = y :: cfg.stk t₁ := by simp [c₉, h13, hc₈t1]
    let c₁₀ : Config := { c₉ with pc := a + 33, stk := Function.update c₉.stk t₁ (cfg.stk t₁) }
    have st32 : Steps P c₉ c₁₀ (1 + len y) := Steps.pop i32 rfl c₉t1
    have c₁₀s : c₁₀.stk s = q :: rest := by simp [c₁₀, c₉, hs1, hs3, hc₈s]
    have c₁₀t1 : c₁₀.stk t₁ = cfg.stk t₁ := by simp [c₁₀]
    have c₁₀t2 : c₁₀.stk t₂ = r :: cfg.stk t₂ := by simp [c₁₀, c₉, h12.symm, h23, hc₈t2]
    have c₁₀t3 : c₁₀.stk t₃ = cfg.stk t₃ := by simp [c₁₀, c₉, h13.symm]
    have c₁₀t4 : c₁₀.stk t₄ = cfg.stk t₄ := by simp [c₁₀, c₉, h14.symm, h34.symm, hc₈t4]
    have c₁₀t5 : c₁₀.stk t₅ = cfg.stk t₅ := by simp [c₁₀, c₉, h15.symm, h35.symm, hc₈t5]
    have hk_cl : Keeps allStks5 cfg c₁₀ :=
      (hk_c₈.trans (Keeps.update_stk_mem c₈ (a + 32) m3 _)).trans
        (Keeps.update_stk_mem c₉ (a + 33) m1 _)
    have st_all := ((((((s0.trans s1).trans s2).trans s3).trans s4).trans s5).trans hst1).trans
      (hst2.trans (st31.trans st32))
    cases isMod
    · -- div: pop t₂, jmp a + 38.
      simp only [Bool.false_eq_true, ↓reduceIte] at htail hlen_code ⊢
      have i33 : CodeAt P (a + 33) [.pop t₂] := by simpa using htail.at_offset 0 (by simp)
      have i34 : CodeAt P (a + 34) [.jmp (a + 38)] := by
        have h := htail.at_offset 1 (by simp); simpa [Nat.add_assoc] using h
      let c₁₁ : Config := { c₁₀ with pc := a + 34, stk := Function.update c₁₀.stk t₂ (cfg.stk t₂) }
      have st33 : Steps P c₁₀ c₁₁ (1 + len r) := Steps.pop i33 rfl c₁₀t2
      let c₁₂ : Config := { c₁₁ with pc := a + 38 }
      have st34 : Steps P c₁₁ c₁₂ 1 := Steps.jmp i34 rfl
      have hk_fin : Keeps allStks5 cfg c₁₂ :=
        (hk_cl.trans (Keeps.update_stk_mem c₁₀ (a + 34) m2 _)).trans
          (Keeps.with_pc_mem allStks5 c₁₁ (a + 38))
      have hkeeps : Keeps [s] cfg c₁₂ := hk_fin.of_subset_eq fun w hw hnot => by
        simp only [allStks5, List.mem_cons, List.not_mem_nil, or_false] at hw hnot
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl hnot
        · simp [c₁₂, c₁₁, h12, c₁₀t1]
        · simp [c₁₂, c₁₁]
        · simp [c₁₂, c₁₁, h23.symm, c₁₀t3]
        · simp [c₁₂, c₁₁, h24.symm, c₁₀t4]
        · simp [c₁₂, c₁₁, h25.symm, c₁₀t5]
      refine ⟨c₁₂, _, st_all.trans (st33.trans st34), ?_, ?_, hkeeps, ?_⟩
      · simp [c₁₂, hlen_code]
      · simp [c₁₂, c₁₁, hs2, c₁₀s, hq_eq]
      · simp only [GI.Machine.len_zero]
        nlinarith
    · -- mod: pop s, move t₂ s, jmp a + 37.
      simp only [↓reduceIte] at htail hlen_code ⊢
      have i33 : CodeAt P (a + 33) [.pop s] := by simpa using htail.at_offset 0 (by simp)
      have i34 : CodeAt P (a + 34) [.move t₂ s] := by
        have h := htail.at_offset 1 (by simp); simpa [Nat.add_assoc] using h
      have i35 : CodeAt P (a + 35) [.jmp (a + 37)] := by
        have h := htail.at_offset 2 (by simp); simpa [Nat.add_assoc] using h
      let c₁₁ : Config := { c₁₀ with pc := a + 34, stk := Function.update c₁₀.stk s rest }
      have st33 : Steps P c₁₀ c₁₁ (1 + len q) := Steps.pop i33 rfl c₁₀s
      have c₁₁s : c₁₁.stk s = rest := by simp [c₁₁]
      have c₁₁t2 : c₁₁.stk t₂ = r :: cfg.stk t₂ := by simp [c₁₁, hs2.symm, c₁₀t2]
      let c₁₂ : Config := { c₁₁ with pc := a + 35, stk := Function.update (Function.update c₁₁.stk t₂ (cfg.stk t₂)) s (r :: c₁₁.stk s) }
      have st34 : Steps P c₁₁ c₁₂ (1 + len r) := Steps.move_ne hs2.symm i34 rfl c₁₁t2
      let c₁₃ : Config := { c₁₂ with pc := a + 37 }
      have st35 : Steps P c₁₂ c₁₃ 1 := Steps.jmp i35 rfl
      have hk_fin : Keeps allStks5 cfg c₁₃ :=
        ((hk_cl.trans (Keeps.update_stk_mem c₁₀ (a + 34) ms _)).trans
          (Keeps.update_stk₂_mem c₁₁ (a + 35) ms m2 _ _)).trans
          (Keeps.with_pc_mem allStks5 c₁₂ (a + 37))
      have hkeeps : Keeps [s] cfg c₁₃ := hk_fin.of_subset_eq fun w hw hnot => by
        simp only [allStks5, List.mem_cons, List.not_mem_nil, or_false] at hw hnot
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl hnot
        · simp [c₁₃, c₁₂, c₁₁, hs1.symm, h12, c₁₀t1]
        · simp [c₁₃, c₁₂, hs2.symm]
        · simp [c₁₃, c₁₂, c₁₁, hs3.symm, h23.symm, c₁₀t3]
        · simp [c₁₃, c₁₂, c₁₁, hs4.symm, h24.symm, c₁₀t4]
        · simp [c₁₃, c₁₂, c₁₁, hs5.symm, h25.symm, c₁₀t5]
      refine ⟨c₁₃, _, st_all.trans ((st33.trans st34).trans st35), ?_, ?_, hkeeps, ?_⟩
      · simp [c₁₃, hlen_code]
      · simp [c₁₃, c₁₂, c₁₁s, hr_eq]
      · simp only [GI.Machine.len_zero]
        nlinarith

/-- Code for integer division `x / y`. -/
def divCode (s : Stk) (a : ℕ) : List Instr := divModCode false s a

/-- Code for remainder `x % y`. -/
def modCode (s : Stk) (a : ℕ) : List Instr := divModCode true s a

theorem divBlock : BinBlock (· / ·) divCode 50 :=
  divModBlock false

theorem modBlock : BinBlock (· % ·) modCode 50 :=
  divModBlock true

/-- Every binary operation of `GI.Machine.BinOp` has a stack machine block. -/
theorem arithBlocks : ArithBlocks := by
  intro op
  cases op with
  | add => exact ⟨addCode, 4, addBlock⟩
  | sub => exact ⟨subCode, 4, subBlock⟩
  | mul => exact ⟨mulCode, 20, mulBlock⟩
  | div => exact ⟨divCode, 50, divBlock⟩
  | mod => exact ⟨modCode, 50, modBlock⟩
  | lt => exact ⟨ltCode, 8, ltBlock⟩
  | eq => exact ⟨eqCode, 16, eqBlock⟩

end GI.Turing
