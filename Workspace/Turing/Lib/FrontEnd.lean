/-
Stack machine front end (`GI.Turing.FrontEnd`).

Starting with stack `Mem` empty and input bits `x`, `frontEndCode a` reads the input bits one by
one while maintaining a counter `i` on stack 2. For each `true` bit at index `i`, it pushes value
`1` and address `i + 1` onto `Mem`. At end-of-input (`read` returns `2`), it moves `i = x.length`
onto `Mem` and pushes address `0` on top, restoring all scratch stacks.
-/
module

public import Workspace.Turing.Lib.Logic

@[expose] public section

namespace GI.Turing

open GI.Machine (len)
open GI.Turing.SM

/-- Front-end code placed at index `a`. Uses stacks 2, 3, 4 as scratch and leaves `rawInput inp`
on `Mem`. -/
def frontEndCode (a : ℕ) : List Instr :=
  let t₁ : Stk := 2
  let t₂ : Stk := 3
  let t₃ : Stk := 4
  [ .push t₁ 0,
    .read t₂, .copy t₂ t₃, .jz t₃ (a + 13),
    .push t₃ 1, .sub t₂ t₃, .jz t₂ (a + 8), .jmp (a + 17),
    .push t₃ 1, .add t₁ t₃, .push Mem 1, .copy t₁ Mem, .jmp (a + 1),
    .pop t₂, .push t₃ 1, .add t₁ t₃, .jmp (a + 1),
    .move t₁ Mem, .push Mem 0 ]

theorem frontEnd_spec (P : Program) (a : ℕ) (cfg : Config)
    (hcode : CodeAt P a (frontEndCode a)) (hpc : cfg.pc = a) (hmem0 : cfg.stk Mem = []) :
    ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + (frontEndCode a).length ∧
      memOf (cfg'.stk Mem) = rawInput cfg.inp ∧
      listSize (cfg'.stk Mem) ≤ 25 * (cfg.inp.length + 1) ^ 2 ∧
      (∀ t, t ≠ Mem → cfg'.stk t = cfg.stk t) ∧ cfg'.rs = cfg.rs ∧ cfg'.out = cfg.out ∧
      S ≤ 25 * (cfg.inp.length + 1) ^ 2 := by
  let t₁ : Stk := 2
  let t₂ : Stk := 3
  let t₃ : Stk := 4
  have hm1 : Mem ≠ t₁ := by decide
  have hm2 : Mem ≠ t₂ := by decide
  have hm3 : Mem ≠ t₃ := by decide
  have h12 : t₁ ≠ t₂ := by decide
  have h13 : t₁ ≠ t₃ := by decide
  have h23 : t₂ ≠ t₃ := by decide
  let used : List Stk := [Mem, t₁, t₂, t₃]
  have mm : Mem ∈ used := by simp [used]
  have m1 : t₁ ∈ used := by simp [used]
  have m2 : t₂ ∈ used := by simp [used]
  have m3 : t₃ ∈ used := by simp [used]
  have i0 : CodeAt P a [.push t₁ 0] := by simpa [frontEndCode] using hcode.at_offset 0 (by simp [frontEndCode])
  have i1 : CodeAt P (a + 1) [.read t₂] := by simpa [frontEndCode] using hcode.at_offset 1 (by simp [frontEndCode])
  have i2 : CodeAt P (a + 2) [.copy t₂ t₃] := by simpa [frontEndCode] using hcode.at_offset 2 (by simp [frontEndCode])
  have i3 : CodeAt P (a + 3) [.jz t₃ (a + 13)] := by simpa [frontEndCode] using hcode.at_offset 3 (by simp [frontEndCode])
  have i4 : CodeAt P (a + 4) [.push t₃ 1] := by simpa [frontEndCode] using hcode.at_offset 4 (by simp [frontEndCode])
  have i5 : CodeAt P (a + 5) [.sub t₂ t₃] := by simpa [frontEndCode] using hcode.at_offset 5 (by simp [frontEndCode])
  have i6 : CodeAt P (a + 6) [.jz t₂ (a + 8)] := by simpa [frontEndCode] using hcode.at_offset 6 (by simp [frontEndCode])
  have i7 : CodeAt P (a + 7) [.jmp (a + 17)] := by simpa [frontEndCode] using hcode.at_offset 7 (by simp [frontEndCode])
  have i8 : CodeAt P (a + 8) [.push t₃ 1] := by simpa [frontEndCode] using hcode.at_offset 8 (by simp [frontEndCode])
  have i9 : CodeAt P (a + 9) [.add t₁ t₃] := by simpa [frontEndCode] using hcode.at_offset 9 (by simp [frontEndCode])
  have i10 : CodeAt P (a + 10) [.push Mem 1] := by simpa [frontEndCode] using hcode.at_offset 10 (by simp [frontEndCode])
  have i11 : CodeAt P (a + 11) [.copy t₁ Mem] := by simpa [frontEndCode] using hcode.at_offset 11 (by simp [frontEndCode])
  have i12 : CodeAt P (a + 12) [.jmp (a + 1)] := by simpa [frontEndCode] using hcode.at_offset 12 (by simp [frontEndCode])
  have i13 : CodeAt P (a + 13) [.pop t₂] := by simpa [frontEndCode] using hcode.at_offset 13 (by simp [frontEndCode])
  have i14 : CodeAt P (a + 14) [.push t₃ 1] := by simpa [frontEndCode] using hcode.at_offset 14 (by simp [frontEndCode])
  have i15 : CodeAt P (a + 15) [.add t₁ t₃] := by simpa [frontEndCode] using hcode.at_offset 15 (by simp [frontEndCode])
  have i16 : CodeAt P (a + 16) [.jmp (a + 1)] := by simpa [frontEndCode] using hcode.at_offset 16 (by simp [frontEndCode])
  have i17 : CodeAt P (a + 17) [.move t₁ Mem] := by simpa [frontEndCode] using hcode.at_offset 17 (by simp [frontEndCode])
  have i18 : CodeAt P (a + 18) [.push Mem 0] := by simpa [frontEndCode] using hcode.at_offset 18 (by simp [frontEndCode])
  let n := cfg.inp.length
  let c₁ : Config := { cfg with pc := a + 1, stk := Function.update cfg.stk t₁ (0 :: cfg.stk t₁) }
  have s0 : Steps P cfg c₁ (1 + len 0) := Steps.push i0 hpc
  -- Loop invariant: the other stacks, rs, out, the remaining input, the counter i and Mem.
  let Inv : Config → Prop := fun c =>
    c.pc = a + 1 ∧
    (∀ u, u ∉ used → c.stk u = cfg.stk u) ∧ c.rs = cfg.rs ∧ c.out = cfg.out ∧
    c.stk t₂ = cfg.stk t₂ ∧ c.stk t₃ = cfg.stk t₃ ∧
    ∃ i, i ≤ n ∧ c.inp = cfg.inp.drop i ∧ c.stk t₁ = i :: cfg.stk t₁ ∧
      (∀ k, memOf (c.stk Mem) k = if 1 ≤ k ∧ k ≤ i ∧ cfg.inp.getD (k - 1) false then 1 else 0) ∧
      listSize (c.stk Mem) ≤ i * (n + 4)
  let Done : Config → Prop := fun c =>
    c.pc = a + 19 ∧ memOf (c.stk Mem) = rawInput cfg.inp ∧
    listSize (c.stk Mem) ≤ 25 * (n + 1) ^ 2 ∧
    (∀ t, t ≠ Mem → c.stk t = cfg.stk t) ∧ c.rs = cfg.rs ∧ c.out = cfg.out
  let μ : Config → ℕ := fun c => c.inp.length
  have hloop : ∀ c, Inv c →
      ∃ c' S, Steps P c c' S ∧ Done c' ∧ S ≤ μ c * (20 + 2 * n) + (18 + n) := by
    refine Steps.loop Inv Done μ (20 + 2 * n) (18 + n) (fun c hI => ?_)
    obtain ⟨hpc_c, hother, hrs, hout, hct2, hct3, i, hle, hinp, hct1, hmem, hsz⟩ := hI
    have hlen_i : len i ≤ n := le_trans (GI.Machine.len_le_self i) hle
    by_cases hilt : i < n
    · -- Unread bit exists at index i.
      have hdrop : cfg.inp.drop i = cfg.inp[i] :: cfg.inp.drop (i + 1) := List.drop_eq_getElem_cons hilt
      have hinp_cons : c.inp = cfg.inp[i] :: cfg.inp.drop (i + 1) := hinp.trans hdrop
      let b := cfg.inp[i]
      have hb_getD : cfg.inp.getD i false = b := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt]; rfl
      let bv : ℕ := if b then 1 else 0
      let d₁ : Config := { c with pc := a + 2, stk := Function.update c.stk t₂ (bv :: c.stk t₂), inp := cfg.inp.drop (i + 1) }
      have st1 : Steps P c d₁ 1 := Steps.read_cons i1 hpc_c hinp_cons
      have d₁t2 : d₁.stk t₂ = bv :: cfg.stk t₂ := by simp [d₁, hct2]
      have d₁t3 : d₁.stk t₃ = cfg.stk t₃ := by simp [d₁, h23.symm, hct3]
      let d₂ : Config := { d₁ with pc := a + 3, stk := Function.update d₁.stk t₃ (bv :: d₁.stk t₃) }
      have st2 : Steps P d₁ d₂ (1 + len bv) := Steps.copy i2 rfl d₁t2
      have d₂t1 : d₂.stk t₁ = i :: cfg.stk t₁ := by simp [d₂, d₁, h13, h12, hct1]
      have d₂t2 : d₂.stk t₂ = bv :: cfg.stk t₂ := by simp [d₂, h23, d₁t2]
      have d₂t3 : d₂.stk t₃ = bv :: cfg.stk t₃ := by simp [d₂, d₁t3]
      cases hb : b
      · -- Bit is false: bv = 0, jump to a + 13, pop t₂, increment t₁, jump to a + 1.
        have hbv0 : bv = 0 := by simp [bv, hb]
        let d₃ : Config := { d₂ with pc := a + 13, stk := Function.update d₂.stk t₃ (cfg.stk t₃) }
        have st3 : Steps P d₂ d₃ 1 := Steps.jz_zero i3 rfl (by rw [d₂t3, hbv0])
        have d₃t2 : d₃.stk t₂ = 0 :: cfg.stk t₂ := by simp [d₃, h23, d₂t2, hbv0]
        let d₄ : Config := { d₃ with pc := a + 14, stk := Function.update d₃.stk t₂ (cfg.stk t₂) }
        have st13 : Steps P d₃ d₄ (1 + len 0) := Steps.pop i13 rfl d₃t2
        let d₅ : Config := { d₄ with pc := a + 15, stk := Function.update d₄.stk t₃ (1 :: d₄.stk t₃) }
        have st14 : Steps P d₄ d₅ (1 + len 1) := Steps.push i14 rfl
        have d₅t1 : d₅.stk t₁ = i :: cfg.stk t₁ := by simp [d₅, d₄, d₃, h13, h12, d₂t1]
        have d₅t3 : d₅.stk t₃ = 1 :: cfg.stk t₃ := by simp [d₅, d₄, d₃, h23.symm]
        let d₆ : Config := { d₅ with pc := a + 16, stk := Function.update (Function.update d₅.stk t₃ (cfg.stk t₃)) t₁ ((i + 1) :: cfg.stk t₁) }
        have st15 : Steps P d₅ d₆ (1 + len i + len 1) := Steps.add h13 i15 rfl d₅t1 d₅t3
        let d₇ : Config := { d₆ with pc := a + 1 }
        have st16 : Steps P d₆ d₇ 1 := Steps.jmp i16 rfl
        have hd₇m : d₇.stk Mem = c.stk Mem := by simp [d₇, d₆, d₅, d₄, d₃, d₂, d₁, hm1, hm2, hm3]
        have hInv' : Inv d₇ := by
          refine ⟨rfl, fun u hu => ?_, hrs, hout,
            by simp [d₇, d₆, d₅, d₄, h12.symm, h23],
            by simp [d₇, d₆, h13.symm],
            i + 1, hilt, rfl, by simp [d₇, d₆], fun k => ?_, ?_⟩
          · simp only [used, List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
            simp [d₇, d₆, d₅, d₄, d₃, d₂, d₁, hu.2.1, hu.2.2.1, hu.2.2.2, hother u (by simp [used, hu])]
          · rw [hd₇m, hmem k]
            by_cases hk : k = i + 1
            · subst hk
              have hget : cfg.inp.getD i false = false := by rw [hb_getD, hb]
              simp only [Nat.add_sub_cancel, hget, and_false, Bool.false_eq_true, ↓reduceIte]
            · have hiff : (1 ≤ k ∧ k ≤ i ∧ cfg.inp.getD (k - 1) false = true) ↔
                  (1 ≤ k ∧ k ≤ i + 1 ∧ cfg.inp.getD (k - 1) false = true) :=
                ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩⟩
              simp only [hiff]
          · rw [hd₇m]
            calc listSize (c.stk Mem) ≤ i * (n + 4) := hsz
              _ ≤ (i + 1) * (n + 4) := Nat.mul_le_mul_right _ (Nat.le_succ i)
        have hμ_lt : μ d₇ < μ c := by
          simp only [μ, d₇, d₆, d₅, d₄, d₃, d₂, d₁, hinp_cons, List.length_cons]
          omega
        refine Or.inr ⟨d₇, _, (((((st1.trans st2).trans st3).trans st13).trans st14).trans st15).trans st16,
          hInv', hμ_lt, ?_⟩
        simp only [hbv0, GI.Machine.len_zero, GI.Machine.len_one]
        omega
      · -- Bit is true: bv = 1, fall through a + 3, sub 1, jz to a + 8, increment t₁, push (i+1, 1) on Mem.
        have hbv1 : bv = 1 := by simp [bv, hb]
        let d₃ : Config := { d₂ with pc := a + 4, stk := Function.update d₂.stk t₃ (cfg.stk t₃) }
        have st3 : Steps P d₂ d₃ (1 + len 1) := Steps.jz_ne_zero i3 rfl (by rw [d₂t3, hbv1]) (by omega)
        have d₃t2 : d₃.stk t₂ = 1 :: cfg.stk t₂ := by simp [d₃, h23, d₂t2, hbv1]
        have d₃t3 : d₃.stk t₃ = cfg.stk t₃ := by simp [d₃]
        let d₄ : Config := { d₃ with pc := a + 5, stk := Function.update d₃.stk t₃ (1 :: d₃.stk t₃) }
        have st4 : Steps P d₃ d₄ (1 + len 1) := Steps.push i4 rfl
        have d₄t2 : d₄.stk t₂ = 1 :: cfg.stk t₂ := by simp [d₄, h23, d₃t2]
        have d₄t3 : d₄.stk t₃ = 1 :: cfg.stk t₃ := by simp [d₄, d₃t3]
        let d₅ : Config := { d₄ with pc := a + 6, stk := Function.update (Function.update d₄.stk t₃ (cfg.stk t₃)) t₂ ((1 - 1) :: cfg.stk t₂) }
        have st5 : Steps P d₄ d₅ (1 + len 1 + len 1) := Steps.sub h23 i5 rfl d₄t2 d₄t3
        have d₅t2 : d₅.stk t₂ = 0 :: cfg.stk t₂ := by simp [d₅]
        let d₆ : Config := { d₅ with pc := a + 8, stk := Function.update d₅.stk t₂ (cfg.stk t₂) }
        have st6 : Steps P d₅ d₆ 1 := Steps.jz_zero i6 rfl d₅t2
        have d₆t1 : d₆.stk t₁ = i :: cfg.stk t₁ := by simp [d₆, d₅, d₄, d₃, h12, h13, d₂t1]
        have d₆t3 : d₆.stk t₃ = cfg.stk t₃ := by simp [d₆, d₅, h23.symm]
        let d₇ : Config := { d₆ with pc := a + 9, stk := Function.update d₆.stk t₃ (1 :: d₆.stk t₃) }
        have st8 : Steps P d₆ d₇ (1 + len 1) := Steps.push i8 rfl
        have d₇t1 : d₇.stk t₁ = i :: cfg.stk t₁ := by simp [d₇, h13, d₆t1]
        have d₇t3 : d₇.stk t₃ = 1 :: cfg.stk t₃ := by simp [d₇, d₆t3]
        let d₈ : Config := { d₇ with pc := a + 10, stk := Function.update (Function.update d₇.stk t₃ (cfg.stk t₃)) t₁ ((i + 1) :: cfg.stk t₁) }
        have st9 : Steps P d₇ d₈ (1 + len i + len 1) := Steps.add h13 i9 rfl d₇t1 d₇t3
        have d₈m : d₈.stk Mem = c.stk Mem := by simp [d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, hm1, hm2, hm3]
        let d₉ : Config := { d₈ with pc := a + 11, stk := Function.update d₈.stk Mem (1 :: d₈.stk Mem) }
        have st10 : Steps P d₈ d₉ (1 + len 1) := Steps.push i10 rfl
        have d₉t1 : d₉.stk t₁ = (i + 1) :: cfg.stk t₁ := by simp [d₉, d₈, hm1.symm]
        let d₁₀ : Config := { d₉ with pc := a + 12, stk := Function.update d₉.stk Mem ((i + 1) :: d₉.stk Mem) }
        have st11 : Steps P d₉ d₁₀ (1 + len (i + 1)) := Steps.copy i11 rfl d₉t1
        let d₁₁ : Config := { d₁₀ with pc := a + 1 }
        have st12 : Steps P d₁₀ d₁₁ 1 := Steps.jmp i12 rfl
        have hd₁₁m : d₁₁.stk Mem = (i + 1) :: 1 :: c.stk Mem := by simp [d₁₁, d₁₀, d₉, d₈m]
        have hlen_ip1 : len (i + 1) ≤ n := le_trans (GI.Machine.len_le_self (i + 1)) hilt
        have hInv' : Inv d₁₁ := by
          refine ⟨rfl, fun u hu => ?_, hrs, hout,
            by simp [d₁₁, d₁₀, d₉, d₈, d₇, d₆, hm2.symm, h12.symm, h23],
            by simp [d₁₁, d₁₀, d₉, d₈, hm3.symm, h13.symm],
            i + 1, hilt, rfl, by simp [d₁₁, d₁₀, hm1.symm, d₉t1], fun k => ?_, ?_⟩
          · simp only [used, List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
            simp [d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2,
              hother u (by simp [used, hu])]
          · rw [hd₁₁m, memOf_cons_cons, hmem k]
            by_cases hk : i + 1 = k
            · subst hk
              have hget : cfg.inp.getD i false = true := by rw [hb_getD, hb]
              have h1k : 1 ≤ i + 1 ∧ i + 1 ≤ i + 1 := by omega
              simp only [↓reduceIte, Nat.add_sub_cancel, hget, h1k, and_self]
            · simp only [hk, ↓reduceIte]
              have hiff : (1 ≤ k ∧ k ≤ i ∧ cfg.inp.getD (k - 1) false = true) ↔
                  (1 ≤ k ∧ k ≤ i + 1 ∧ cfg.inp.getD (k - 1) false = true) :=
                ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩⟩
              simp only [hiff]
          · rw [hd₁₁m, listSize_cons, listSize_cons]
            simp only [GI.Machine.len_one]
            rw [Nat.add_one_mul]
            omega
        have hμ_lt : μ d₁₁ < μ c := by
          simp only [μ, d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, hinp_cons, List.length_cons]
          omega
        refine Or.inr ⟨d₁₁, _,
          (((((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st8).trans st9).trans st10).trans st11).trans st12,
          hInv', hμ_lt, ?_⟩
        simp only [hbv1, GI.Machine.len_one]
        omega
    · -- End of input: i = n, read pushes 2, push (0, n) on Mem and finish.
      have hin : i = n := by omega
      subst hin
      have hinp_nil : c.inp = [] := by rw [hinp]; simp [n]
      let d₁ : Config := { c with pc := a + 2, stk := Function.update c.stk t₂ (2 :: c.stk t₂) }
      have st1 : Steps P c d₁ 1 := Steps.read_nil i1 hpc_c hinp_nil
      have d₁t2 : d₁.stk t₂ = 2 :: cfg.stk t₂ := by simp [d₁, hct2]
      have d₁t3 : d₁.stk t₃ = cfg.stk t₃ := by simp [d₁, h23.symm, hct3]
      let d₂ : Config := { d₁ with pc := a + 3, stk := Function.update d₁.stk t₃ (2 :: d₁.stk t₃) }
      have st2 : Steps P d₁ d₂ (1 + len 2) := Steps.copy i2 rfl d₁t2
      have d₂t3 : d₂.stk t₃ = 2 :: cfg.stk t₃ := by simp [d₂, d₁t3]
      let d₃ : Config := { d₂ with pc := a + 4, stk := Function.update d₂.stk t₃ (cfg.stk t₃) }
      have st3 : Steps P d₂ d₃ (1 + len 2) := Steps.jz_ne_zero i3 rfl d₂t3 (by omega)
      have d₃t2 : d₃.stk t₂ = 2 :: cfg.stk t₂ := by simp [d₃, d₂, h23, d₁t2]
      let d₄ : Config := { d₃ with pc := a + 5, stk := Function.update d₃.stk t₃ (1 :: d₃.stk t₃) }
      have st4 : Steps P d₃ d₄ (1 + len 1) := Steps.push i4 rfl
      have d₄t2 : d₄.stk t₂ = 2 :: cfg.stk t₂ := by simp [d₄, h23, d₃t2]
      have d₄t3 : d₄.stk t₃ = 1 :: cfg.stk t₃ := by simp [d₄, d₃]
      let d₅ : Config := { d₄ with pc := a + 6, stk := Function.update (Function.update d₄.stk t₃ (cfg.stk t₃)) t₂ ((2 - 1) :: cfg.stk t₂) }
      have st5 : Steps P d₄ d₅ (1 + len 2 + len 1) := Steps.sub h23 i5 rfl d₄t2 d₄t3
      have d₅t2 : d₅.stk t₂ = 1 :: cfg.stk t₂ := by simp [d₅]
      let d₆ : Config := { d₅ with pc := a + 7, stk := Function.update d₅.stk t₂ (cfg.stk t₂) }
      have st6 : Steps P d₅ d₆ (1 + len 1) := Steps.jz_ne_zero i6 rfl d₅t2 (by omega)
      let d₇ : Config := { d₆ with pc := a + 17 }
      have st7 : Steps P d₆ d₇ 1 := Steps.jmp i7 rfl
      have d₇t1 : d₇.stk t₁ = n :: cfg.stk t₁ := by simp [d₇, d₆, d₅, d₄, d₃, d₂, d₁, h12, h13, hct1]
      have d₇m : d₇.stk Mem = c.stk Mem := by simp [d₇, d₆, d₅, d₄, d₃, d₂, d₁, hm2, hm3]
      let d₈ : Config := { d₇ with pc := a + 18, stk := Function.update (Function.update d₇.stk t₁ (cfg.stk t₁)) Mem (n :: d₇.stk Mem) }
      have st17 : Steps P d₇ d₈ (1 + len n) := Steps.move_ne hm1.symm i17 rfl d₇t1
      let d₉ : Config := { d₈ with pc := a + 19, stk := Function.update d₈.stk Mem (0 :: d₈.stk Mem) }
      have st18 : Steps P d₈ d₉ (1 + len 0) := Steps.push i18 rfl
      have hd₉m : d₉.stk Mem = 0 :: n :: c.stk Mem := by simp [d₉, d₈, d₇m]
      have hlen2 : len 2 = 2 := by rw [GI.Machine.len_eq_log_add_one (by omega)]; decide
      refine Or.inl ⟨d₉, _,
        (((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans st17).trans st18,
        ⟨rfl, ?_, ?_, fun u hu => ?_, hrs, hout⟩, ?_⟩
      · funext k
        rw [hd₉m, memOf_cons_cons, rawInput]
        by_cases hk0 : k = 0
        · subst hk0; simp [n]
        · have hk0' : (0 : ℕ) ≠ k := Ne.symm hk0
          simp only [hk0, hk0', ↓reduceIte, hmem k]
          by_cases hkn : k ≤ n
          · have h1k : 1 ≤ k := by omega
            simp [h1k, hkn]
          · have hge : cfg.inp.length ≤ k - 1 := by omega
            have hget : cfg.inp.getD (k - 1) false = false := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge]; rfl
            simp only [hkn, hget, Bool.false_eq_true, and_false, ↓reduceIte]
      · rw [hd₉m, listSize_cons, listSize_cons]
        simp only [GI.Machine.len_zero]
        nlinarith
      · by_cases hu1 : u = t₁
        · subst hu1; simp [d₉, d₈, hm1.symm]
        · by_cases hu2 : u = t₂
          · subst hu2; simp [d₉, d₈, d₇, d₆, hm2.symm, h12.symm]
          · by_cases hu3 : u = t₃
            · subst hu3; simp [d₉, d₈, d₇, d₆, d₅, hm3.symm, h13.symm, h23.symm]
            · simp [d₉, d₈, d₇, d₆, d₅, d₄, d₃, d₂, d₁, hu, hu1, hu2, hu3,
                hother u (by simp [used, hu, hu1, hu2, hu3])]
      · simp only [hlen2, GI.Machine.len_one, GI.Machine.len_zero]
        omega
  have hInv0 : Inv c₁ := by
    refine ⟨rfl, fun u hu => ?_, rfl, rfl, by simp [c₁, h12.symm], by simp [c₁, h13.symm],
      0, Nat.zero_le n, by simp [c₁], by simp [c₁], fun k => ?_, by simp [c₁, hm1, hmem0]⟩
    · simp only [used, List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
      simp [c₁, hu.2.1]
    · simp only [c₁, Function.update_of_ne hm1, hmem0, memOf_nil]
      split_ifs with h
      · omega
      · rfl
  obtain ⟨c', S_loop, hst_loop, ⟨hpc', hmem', hsz', hother', hrs', hout'⟩, hS_loop⟩ := hloop c₁ hInv0
  have hμ0 : μ c₁ = n := rfl
  rw [hμ0] at hS_loop
  refine ⟨c', _, s0.trans hst_loop, ?_, hmem', hsz', hother', hrs', hout', ?_⟩
  · simp [hpc', frontEndCode]
  · simp only [GI.Machine.len_zero]
    nlinarith

/-- `FrontEnd`: reads the input bits into `Mem` in quadratic cost and size. -/
theorem frontEnd : FrontEnd :=
  ⟨frontEndCode, 25, frontEnd_spec⟩

end GI.Turing
