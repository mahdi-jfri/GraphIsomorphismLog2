/-
Stack machine back end (`GI.Turing.BackEnd`).

Starting with the base address `B` on top of stack `E` and memory encoded on stack `Mem`,
`backEndCode a` looks up `L = memOf (stk Mem) B` using `lookupCode E Mem` and then loops `L`
times, looking up cells `B + 1, B + 2, …, B + L` and writing each bit to the output.
-/
module

public import Workspace.Turing.Lib.Lookup

@[expose] public section

namespace GI.Turing

open GI.Machine (len)
open GI.Turing.SM

/-- Back-end code placed at index `a`. Uses `lookupCode E Mem` and stacks 2, 3, 4 to emit
`rawOutput (memOf (stk Mem)) B`. -/
def backEndCode (a : ℕ) : List Instr :=
  let t₁ : Stk := 2
  let t₂ : Stk := 3
  let t₃ : Stk := 4
  [ .copy E t₂, .push t₃ 1, .add t₂ t₃ ] ++
  lookupCode E Mem (a + 3) ++
  [ .move E t₁,
    .copy t₁ t₃, .jz t₃ (a + 61),
    .copy t₂ E ] ++
  lookupCode E Mem (a + 31) ++
  [ .write E,
    .push t₃ 1, .add t₂ t₃,
    .push t₃ 1, .sub t₁ t₃,
    .jmp (a + 28) ]

theorem backEndCode_length (a : ℕ) : (backEndCode a).length = 61 := by
  simp [backEndCode, lookupCode]

theorem backEnd_spec (P : Program) (a : ℕ) (cfg : Config) (B : ℕ) (rest : List ℕ)
    (hcode : CodeAt P a (backEndCode a)) (hpc : cfg.pc = a) (hE : cfg.stk E = B :: rest) :
    ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + (backEndCode a).length ∧
      cfg'.out = cfg.out ++ rawOutput (memOf (cfg.stk Mem)) B ∧
      S ≤ 110 * (memOf (cfg.stk Mem) B + listSize (cfg.stk Mem) + len B + 1) ^ 3 := by
  let t₁ : Stk := 2
  let t₂ : Stk := 3
  let t₃ : Stk := 4
  have hEM : E ≠ Mem := by decide
  have hE1 : E ≠ t₁ := by decide
  have hE2 : E ≠ t₂ := by decide
  have hE3 : E ≠ t₃ := by decide
  have hM1 : Mem ≠ t₁ := by decide
  have hM2 : Mem ≠ t₂ := by decide
  have hM3 : Mem ≠ t₃ := by decide
  have h12 : t₁ ≠ t₂ := by decide
  have h13 : t₁ ≠ t₃ := by decide
  have h23 : t₂ ≠ t₃ := by decide
  -- Extract CodeAt for each segment of backEndCode.
  have hlen_lu : ∀ k, (lookupCode E Mem k).length = 24 := fun k => by simp [lookupCode]
  have hcode' : CodeAt P a
      (([ .copy E t₂, .push t₃ 1, .add t₂ t₃ ] ++ lookupCode E Mem (a + 3) ++
        [ .move E t₁, .copy t₁ t₃, .jz t₃ (a + 61), .copy t₂ E ] ++ lookupCode E Mem (a + 31)) ++
        [ .write E, .push t₃ 1, .add t₂ t₃, .push t₃ 1, .sub t₁ t₃, .jmp (a + 28) ]) := hcode
  have hseg5 : CodeAt P (a + 55)
      [ .write E, .push t₃ 1, .add t₂ t₃, .push t₃ 1, .sub t₁ t₃, .jmp (a + 28) ] := by
    have h := hcode'.append_right
    simpa [List.length_append, hlen_lu] using h
  have hpref4 := hcode'.append_left
  have hlu2 : CodeAt P (a + 31) (lookupCode E Mem (a + 31)) := by
    have h := hpref4.append_right
    simpa [List.length_append, hlen_lu] using h
  have hpref3 := hpref4.append_left
  have hseg3 : CodeAt P (a + 27) [ .move E t₁, .copy t₁ t₃, .jz t₃ (a + 61), .copy t₂ E ] := by
    have h := hpref3.append_right
    simpa [List.length_append, hlen_lu] using h
  have hpref2 := hpref3.append_left
  have hlu1 : CodeAt P (a + 3) (lookupCode E Mem (a + 3)) := by
    have h := hpref2.append_right
    simpa using h
  have hseg1 : CodeAt P a [ .copy E t₂, .push t₃ 1, .add t₂ t₃ ] := hpref2.append_left
  have i0 : CodeAt P a [.copy E t₂] := by simpa using hseg1.at_offset 0 (by simp)
  have i1 : CodeAt P (a + 1) [.push t₃ 1] := by simpa using hseg1.at_offset 1 (by simp)
  have i2 : CodeAt P (a + 2) [.add t₂ t₃] := by simpa using hseg1.at_offset 2 (by simp)
  have i27 : CodeAt P (a + 27) [.move E t₁] := by simpa using hseg3.at_offset 0 (by simp)
  have i28 : CodeAt P (a + 28) [.copy t₁ t₃] := by
    have h := hseg3.at_offset 1 (by simp); simpa [Nat.add_assoc] using h
  have i29 : CodeAt P (a + 29) [.jz t₃ (a + 61)] := by
    have h := hseg3.at_offset 2 (by simp); simpa [Nat.add_assoc] using h
  have i30 : CodeAt P (a + 30) [.copy t₂ E] := by
    have h := hseg3.at_offset 3 (by simp); simpa [Nat.add_assoc] using h
  have i55 : CodeAt P (a + 55) [.write E] := by simpa using hseg5.at_offset 0 (by simp)
  have i56 : CodeAt P (a + 56) [.push t₃ 1] := by
    have h := hseg5.at_offset 1 (by simp); simpa [Nat.add_assoc] using h
  have i57 : CodeAt P (a + 57) [.add t₂ t₃] := by
    have h := hseg5.at_offset 2 (by simp); simpa [Nat.add_assoc] using h
  have i58 : CodeAt P (a + 58) [.push t₃ 1] := by
    have h := hseg5.at_offset 3 (by simp); simpa [Nat.add_assoc] using h
  have i59 : CodeAt P (a + 59) [.sub t₁ t₃] := by
    have h := hseg5.at_offset 4 (by simp); simpa [Nat.add_assoc] using h
  have i60 : CodeAt P (a + 60) [.jmp (a + 28)] := by
    have h := hseg5.at_offset 5 (by simp); simpa [Nat.add_assoc] using h
  -- Setup: t₂ := B + 1, lookup L := mem B on E, move L to t₁.
  let mem := memOf (cfg.stk Mem)
  let L := mem B
  let M := listSize (cfg.stk Mem)
  let N := L + M + len B + 1
  have hN_def : N = L + M + len B + 1 := rfl
  let c₁ : Config := { cfg with pc := a + 1, stk := Function.update cfg.stk t₂ (B :: cfg.stk t₂) }
  have s0 : Steps P cfg c₁ (1 + len B) := Steps.copy i0 hpc hE
  let c₂ : Config := { c₁ with pc := a + 2, stk := Function.update c₁.stk t₃ (1 :: c₁.stk t₃) }
  have s1 : Steps P c₁ c₂ (1 + len 1) := Steps.push i1 rfl
  have c₂t2 : c₂.stk t₂ = B :: cfg.stk t₂ := by simp [c₂, c₁, h23]
  have c₂t3 : c₂.stk t₃ = 1 :: cfg.stk t₃ := by simp [c₂, c₁, h23.symm]
  let c₃ : Config := { c₂ with pc := a + 3, stk := Function.update (Function.update c₂.stk t₃ (cfg.stk t₃)) t₂ ((B + 1) :: cfg.stk t₂) }
  have s2 : Steps P c₂ c₃ (1 + len B + len 1) := Steps.add h23 i2 rfl c₂t2 c₂t3
  have c₃E : c₃.stk E = B :: rest := by simp [c₃, c₂, c₁, hE2, hE3, hE]
  have c₃M : c₃.stk Mem = cfg.stk Mem := by simp [c₃, c₂, c₁, hM2, hM3]
  have c₃t1 : c₃.stk t₁ = cfg.stk t₁ := by simp [c₃, c₂, c₁, h12, h13]
  have c₃t2 : c₃.stk t₂ = (B + 1) :: cfg.stk t₂ := by simp [c₃]
  have c₃t3 : c₃.stk t₃ = cfg.stk t₃ := by simp [c₃, h23.symm]
  obtain ⟨c₄, S_lu1, hst_lu1, hc₄pc, hc₄E, hk_lu1, hS_lu1⟩ :=
    lookupBlock_spec E Mem hEM P (a + 3) c₃ B rest hlu1 rfl c₃E
  have hc₄pc' : c₄.pc = a + 27 := by rw [hc₄pc, hlen_lu]
  have hc₄M : c₄.stk Mem = cfg.stk Mem := by rw [hk_lu1.stk_eq (by simp [hEM.symm]), c₃M]
  have hc₄t1 : c₄.stk t₁ = cfg.stk t₁ := by rw [hk_lu1.stk_eq (by simp [hE1.symm]), c₃t1]
  have hc₄t2 : c₄.stk t₂ = (B + 1) :: cfg.stk t₂ := by rw [hk_lu1.stk_eq (by simp [hE2.symm]), c₃t2]
  have hc₄t3 : c₄.stk t₃ = cfg.stk t₃ := by rw [hk_lu1.stk_eq (by simp [hE3.symm]), c₃t3]
  have hc₄out : c₄.out = cfg.out := hk_lu1.out_eq
  rw [c₃M] at hc₄E hS_lu1
  let c₅ : Config := { c₄ with pc := a + 28, stk := Function.update (Function.update c₄.stk E rest) t₁ (L :: c₄.stk t₁) }
  have s27 : Steps P c₄ c₅ (1 + len L) := Steps.move_ne hE1 i27 hc₄pc' hc₄E
  have c₅E : c₅.stk E = rest := by simp [c₅, hE1]
  have c₅M : c₅.stk Mem = cfg.stk Mem := by simp [c₅, hM1, hEM.symm, hc₄M]
  have c₅t1 : c₅.stk t₁ = L :: cfg.stk t₁ := by simp [c₅, hc₄t1]
  have c₅t2 : c₅.stk t₂ = (B + 1) :: cfg.stk t₂ := by simp [c₅, h12.symm, hE2.symm, hc₄t2]
  have c₅t3 : c₅.stk t₃ = cfg.stk t₃ := by simp [c₅, h13.symm, hE3.symm, hc₄t3]
  have c₅out : c₅.out = cfg.out := hc₄out
  -- Main output loop at a + 28.
  let Inv : Config → Prop := fun c =>
    c.pc = a + 28 ∧ c.stk E = rest ∧ c.stk Mem = cfg.stk Mem ∧ c.stk t₃ = cfg.stk t₃ ∧
    ∃ i, i ≤ L ∧ c.stk t₁ = (L - i) :: cfg.stk t₁ ∧ c.stk t₂ = (B + 1 + i) :: cfg.stk t₂ ∧
      c.out = cfg.out ++ (List.range i).map (fun j => decide (mem (B + 1 + j) ≠ 0))
  let Done : Config → Prop := fun c =>
    c.pc = a + 61 ∧ c.out = cfg.out ++ rawOutput mem B
  let μ : Config → ℕ := fun c => (c.stk t₁).head!
  have hloop : ∀ c, Inv c → ∃ c' S, Steps P c c' S ∧ Done c' ∧ S ≤ μ c * (70 * N ^ 2) + 2 := by
    refine Steps.loop Inv Done μ (70 * N ^ 2) 2 (fun c hI => ?_)
    obtain ⟨hpc_c, hcE, hcM, hct3, i, hiL, hct1, hct2, hcout⟩ := hI
    let d₁ : Config := { c with pc := a + 29, stk := Function.update c.stk t₃ ((L - i) :: c.stk t₃) }
    have st28 : Steps P c d₁ (1 + len (L - i)) := Steps.copy i28 hpc_c hct1
    have d₁t3 : d₁.stk t₃ = (L - i) :: cfg.stk t₃ := by simp [d₁, hct3]
    by_cases hrem : L - i = 0
    · -- Exit loop: i = L.
      have hi_eq : i = L := by omega
      let d₂ : Config := { d₁ with pc := a + 61, stk := Function.update d₁.stk t₃ (cfg.stk t₃) }
      have st29 : Steps P d₁ d₂ 1 := Steps.jz_zero i29 rfl (by rw [d₁t3, hrem])
      refine Or.inl ⟨d₂, _, st28.trans st29, ⟨rfl, ?_⟩, ?_⟩
      · simp only [d₂, d₁, hcout, hi_eq, rawOutput, L, mem]
      · rw [hrem, GI.Machine.len_zero]
    · -- Continue: i < L.
      have hilt : i < L := by omega
      let d₂ : Config := { d₁ with pc := a + 30, stk := Function.update d₁.stk t₃ (cfg.stk t₃) }
      have st29 : Steps P d₁ d₂ (1 + len (L - i)) := Steps.jz_ne_zero i29 rfl d₁t3 hrem
      have d₂E : d₂.stk E = rest := by simp [d₂, d₁, hE3, hcE]
      have d₂M : d₂.stk Mem = cfg.stk Mem := by simp [d₂, d₁, hM3, hcM]
      have d₂t1 : d₂.stk t₁ = (L - i) :: cfg.stk t₁ := by simp [d₂, d₁, h13, hct1]
      have d₂t2 : d₂.stk t₂ = (B + 1 + i) :: cfg.stk t₂ := by simp [d₂, d₁, h23, hct2]
      have d₂t3 : d₂.stk t₃ = cfg.stk t₃ := by simp [d₂]
      let d₃ : Config := { d₂ with pc := a + 31, stk := Function.update d₂.stk E ((B + 1 + i) :: d₂.stk E) }
      have st30 : Steps P d₂ d₃ (1 + len (B + 1 + i)) := Steps.copy i30 rfl d₂t2
      have d₃E : d₃.stk E = (B + 1 + i) :: rest := by simp [d₃, d₂E]
      have d₃M : d₃.stk Mem = cfg.stk Mem := by simp [d₃, hEM.symm, d₂M]
      have d₃t1 : d₃.stk t₁ = (L - i) :: cfg.stk t₁ := by simp [d₃, hE1.symm, d₂t1]
      have d₃t2 : d₃.stk t₂ = (B + 1 + i) :: cfg.stk t₂ := by simp [d₃, hE2.symm, d₂t2]
      have d₃t3 : d₃.stk t₃ = cfg.stk t₃ := by simp [d₃, hE3.symm, d₂t3]
      obtain ⟨d₄, S_lu2, hst_lu2, hd₄pc, hd₄E, hk_lu2, hS_lu2⟩ :=
        lookupBlock_spec E Mem hEM P (a + 31) d₃ (B + 1 + i) rest hlu2 rfl d₃E
      have hd₄pc' : d₄.pc = a + 55 := by rw [hd₄pc, hlen_lu]
      have hd₄M : d₄.stk Mem = cfg.stk Mem := by rw [hk_lu2.stk_eq (by simp [hEM.symm]), d₃M]
      have hd₄t1 : d₄.stk t₁ = (L - i) :: cfg.stk t₁ := by rw [hk_lu2.stk_eq (by simp [hE1.symm]), d₃t1]
      have hd₄t2 : d₄.stk t₂ = (B + 1 + i) :: cfg.stk t₂ := by rw [hk_lu2.stk_eq (by simp [hE2.symm]), d₃t2]
      have hd₄t3 : d₄.stk t₃ = cfg.stk t₃ := by rw [hk_lu2.stk_eq (by simp [hE3.symm]), d₃t3]
      have hd₄out : d₄.out = c.out := hk_lu2.out_eq
      rw [d₃M] at hd₄E hS_lu2
      let v := mem (B + 1 + i)
      let d₅ : Config := { d₄ with pc := a + 56, stk := Function.update d₄.stk E rest, out := d₄.out ++ [decide (v ≠ 0)] }
      have st55 : Steps P d₄ d₅ (1 + len v) := Steps.write i55 hd₄pc' hd₄E
      have d₅t2 : d₅.stk t₂ = (B + 1 + i) :: cfg.stk t₂ := by simp [d₅, hE2.symm, hd₄t2]
      have d₅t3 : d₅.stk t₃ = cfg.stk t₃ := by simp [d₅, hE3.symm, hd₄t3]
      let d₆ : Config := { d₅ with pc := a + 57, stk := Function.update d₅.stk t₃ (1 :: d₅.stk t₃) }
      have st56 : Steps P d₅ d₆ (1 + len 1) := Steps.push i56 rfl
      have d₆t2 : d₆.stk t₂ = (B + 1 + i) :: cfg.stk t₂ := by simp [d₆, h23, d₅t2]
      have d₆t3 : d₆.stk t₃ = 1 :: cfg.stk t₃ := by simp [d₆, d₅t3]
      let d₇ : Config := { d₆ with pc := a + 58, stk := Function.update (Function.update d₆.stk t₃ (cfg.stk t₃)) t₂ ((B + 1 + i + 1) :: cfg.stk t₂) }
      have st57 : Steps P d₆ d₇ (1 + len (B + 1 + i) + len 1) := Steps.add h23 i57 rfl d₆t2 d₆t3
      have d₇t1 : d₇.stk t₁ = (L - i) :: cfg.stk t₁ := by simp [d₇, d₆, d₅, h12, h13, hE1.symm, hd₄t1]
      have d₇t3 : d₇.stk t₃ = cfg.stk t₃ := by simp [d₇, h23.symm]
      let d₈ : Config := { d₇ with pc := a + 59, stk := Function.update d₇.stk t₃ (1 :: d₇.stk t₃) }
      have st58 : Steps P d₇ d₈ (1 + len 1) := Steps.push i58 rfl
      have d₈t1 : d₈.stk t₁ = (L - i) :: cfg.stk t₁ := by simp [d₈, h13, d₇t1]
      have d₈t3 : d₈.stk t₃ = 1 :: cfg.stk t₃ := by simp [d₈, d₇t3]
      let d₉ : Config := { d₈ with pc := a + 60, stk := Function.update (Function.update d₈.stk t₃ (cfg.stk t₃)) t₁ ((L - i - 1) :: cfg.stk t₁) }
      have st59 : Steps P d₈ d₉ (1 + len (L - i) + len 1) := Steps.sub h13 i59 rfl d₈t1 d₈t3
      let d₁₀ : Config := { d₉ with pc := a + 28 }
      have st60 : Steps P d₉ d₁₀ 1 := Steps.jmp i60 rfl
      have hInv' : Inv d₁₀ := by
        refine ⟨rfl,
          by simp [d₁₀, d₉, d₈, d₇, d₆, d₅, hE1, hE2, hE3],
          by simp [d₁₀, d₉, d₈, d₇, d₆, d₅, hM1, hM2, hM3, hEM.symm, hd₄M],
          by simp [d₁₀, d₉, h13.symm],
          i + 1, hilt,
          by simp [d₁₀, d₉, Nat.sub_sub],
          by simp [d₁₀, d₉, d₈, d₇, h12.symm, h23, Nat.add_assoc], ?_⟩
        simp only [d₁₀, d₉, d₈, d₇, d₆, d₅, hd₄out, hcout, List.range_succ, List.map_append,
          List.map_singleton, List.append_assoc, v]
      have hμ_lt : μ d₁₀ < μ c := by
        simp only [μ, d₁₀, d₉, Function.update_self, hct1, List.head!_cons]
        omega
      have hlen_rem : len (L - i) ≤ L := le_trans (GI.Machine.len_le_self _) (Nat.sub_le L i)
      have hlen_addr : len (B + 1 + i) ≤ len B + L + 1 := by
        have h1 := GI.Machine.len_add_le_add B (1 + i)
        have h2 : len (1 + i) ≤ L := le_trans (GI.Machine.len_le_self _) (by omega)
        rw [Nat.add_assoc]
        omega
      have hlen_v : len v ≤ M := len_memOf_le_listSize (cfg.stk Mem) (B + 1 + i)
      refine Or.inr ⟨d₁₀, _,
        (((((((((st28.trans st29).trans st30).trans hst_lu2).trans st55).trans st56).trans st57).trans st58).trans st59).trans st60),
        hInv', hμ_lt, ?_⟩
      simp only [GI.Machine.len_one]
      have hM_def : M = listSize (cfg.stk Mem) := rfl
      have hN1 : (M + 1) * (len (B + 1 + i) + 1) ≤ N * (N + 1) :=
        Nat.mul_le_mul (by omega) (by omega)
      nlinarith
  have hInv0 : Inv c₅ :=
    ⟨rfl, c₅E, c₅M, c₅t3, 0, Nat.zero_le L, by simpa using c₅t1, by simpa using c₅t2, by simp [c₅out]⟩
  obtain ⟨c₆, S_loop, hst_loop, ⟨hpc₆, hout₆⟩, hS_loop⟩ := hloop c₅ hInv0
  have hμ0 : μ c₅ = L := by simp [μ, c₅t1]
  rw [hμ0] at hS_loop
  refine ⟨c₆, _, ((((s0.trans s1).trans s2).trans hst_lu1).trans s27).trans hst_loop, ?_, hout₆, ?_⟩
  · rw [hpc₆, backEndCode_length]
  · simp only [GI.Machine.len_one]
    change _ ≤ 110 * N ^ 3
    have hM_def : M = listSize (cfg.stk Mem) := rfl
    have hL_len : len L ≤ M := len_memOf_le_listSize (cfg.stk Mem) B
    have h1 : 1 ≤ N := by omega
    have hN2 : N ≤ N ^ 2 := by nlinarith
    have hN3 : N ^ 2 ≤ N ^ 3 := by nlinarith
    have hS1 : (M + 1) * (len B + 1) ≤ N ^ 2 := by nlinarith
    have hSL : L * (70 * N ^ 2) ≤ 70 * N ^ 3 := by
      have : L * N ^ 2 ≤ N * N ^ 2 := Nat.mul_le_mul_right (N ^ 2) (by omega)
      nlinarith
    nlinarith

/-- `BackEnd`: outputs `rawOutput (memOf (stk Mem)) B` in cubic cost. -/
theorem backEnd : BackEnd :=
  ⟨backEndCode, 110, backEnd_spec⟩

end GI.Turing
