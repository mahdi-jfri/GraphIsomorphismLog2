/-
Stack machine code for memory lookup (`GI.Turing.LookupBlock`).

Given stacks `s ≠ m` with address `x` on top of `s`, `lookupCode s m a` scans the address-value
pairs on `m`, moving scanned elements onto a backup stack `t₁` and pushing a unary marker `1` onto
`t₂` above a sentinel `0` for each moved element. On the first pair whose address equals `x` it
replaces `x` on `s` by the paired value; if it reaches the end of `m` (or a trailing unpaired
address) it replaces `x` by `0`. Finally it moves all saved elements back from `t₁` to `m` using
the unary markers on `t₂`, restoring every stack other than `s`.
-/
module

public import Workspace.Turing.Lib.Logic

@[expose] public section

namespace GI.Turing

open GI.Machine (len)
open GI.Turing.SM

/-- Memory lookup block for `s ≠ m`. Replaces the top `x` of `s` by `memOf (stk m) x` and
restores `m` and all scratch stacks. -/
def lookupCode (s m : Stk) (a : ℕ) : List Instr :=
  let t₁ := scratch2 s m 0
  let t₂ := scratch2 s m 1
  let t₃ := scratch2 s m 2
  let t₄ := scratch2 s m 3
  let t₅ := scratch2 s m 4
  [ .push t₂ 0,
    .jnil m (a + 19),
    .move m t₁, .push t₂ 1, .jnil m (a + 19),
    .copy t₁ t₃, .copy s t₄, .sub t₃ t₄,
    .copy s t₄, .copy t₁ t₅, .sub t₄ t₅,
    .add t₃ t₄, .jz t₃ (a + 16),
    .move m t₁, .push t₂ 1, .jmp (a + 1),
    .pop s, .copy m s, .jmp (a + 21),
    .pop s, .push s 0,
    .jz t₂ (a + 24), .move t₁ m, .jmp (a + 21) ]

theorem lookupBlock_spec (s m : Stk) (hsm : s ≠ m)
    (P : Program) (a : ℕ) (cfg : Config) (x : ℕ) (rest : List ℕ)
    (hcode : CodeAt P a (lookupCode s m a)) (hpc : cfg.pc = a) (hs : cfg.stk s = x :: rest) :
    ∃ cfg' S, Steps P cfg cfg' S ∧ cfg'.pc = a + (lookupCode s m a).length ∧
      cfg'.stk s = memOf (cfg.stk m) x :: rest ∧ Keeps [s] cfg cfg' ∧
      S ≤ 26 * (listSize (cfg.stk m) + 1) * (len x + 1) := by
  let t₁ := scratch2 s m 0
  let t₂ := scratch2 s m 1
  let t₃ := scratch2 s m 2
  let t₄ := scratch2 s m 3
  let t₅ := scratch2 s m 4
  have hs1 : s ≠ t₁ := (scratch2_ne_left s m hsm 0).symm
  have hs2 : s ≠ t₂ := (scratch2_ne_left s m hsm 1).symm
  have hs3 : s ≠ t₃ := (scratch2_ne_left s m hsm 2).symm
  have hs4 : s ≠ t₄ := (scratch2_ne_left s m hsm 3).symm
  have hs5 : s ≠ t₅ := (scratch2_ne_left s m hsm 4).symm
  have hm1 : m ≠ t₁ := (scratch2_ne_right s m hsm 0).symm
  have hm2 : m ≠ t₂ := (scratch2_ne_right s m hsm 1).symm
  have hm3 : m ≠ t₃ := (scratch2_ne_right s m hsm 2).symm
  have hm4 : m ≠ t₄ := (scratch2_ne_right s m hsm 3).symm
  have hm5 : m ≠ t₅ := (scratch2_ne_right s m hsm 4).symm
  have h12 : t₁ ≠ t₂ := scratch2_ne s m hsm (by decide)
  have h13 : t₁ ≠ t₃ := scratch2_ne s m hsm (by decide)
  have h14 : t₁ ≠ t₄ := scratch2_ne s m hsm (by decide)
  have h15 : t₁ ≠ t₅ := scratch2_ne s m hsm (by decide)
  have h23 : t₂ ≠ t₃ := scratch2_ne s m hsm (by decide)
  have h24 : t₂ ≠ t₄ := scratch2_ne s m hsm (by decide)
  have h25 : t₂ ≠ t₅ := scratch2_ne s m hsm (by decide)
  have h34 : t₃ ≠ t₄ := scratch2_ne s m hsm (by decide)
  have h35 : t₃ ≠ t₅ := scratch2_ne s m hsm (by decide)
  have h45 : t₄ ≠ t₅ := scratch2_ne s m hsm (by decide)
  let used : List Stk := [s, m, t₁, t₂, t₃, t₄, t₅]
  have ms : s ∈ used := by simp [used]
  have mm : m ∈ used := by simp [used]
  have m1 : t₁ ∈ used := by simp [used]
  have m2 : t₂ ∈ used := by simp [used]
  have m3 : t₃ ∈ used := by simp [used]
  have m4 : t₄ ∈ used := by simp [used]
  have m5 : t₅ ∈ used := by simp [used]
  have i0 : CodeAt P a [.push t₂ 0] := by simpa [lookupCode] using hcode.at_offset 0 (by simp [lookupCode])
  have i1 : CodeAt P (a + 1) [.jnil m (a + 19)] := by simpa [lookupCode] using hcode.at_offset 1 (by simp [lookupCode])
  have i2 : CodeAt P (a + 2) [.move m t₁] := by simpa [lookupCode] using hcode.at_offset 2 (by simp [lookupCode])
  have i3 : CodeAt P (a + 3) [.push t₂ 1] := by simpa [lookupCode] using hcode.at_offset 3 (by simp [lookupCode])
  have i4 : CodeAt P (a + 4) [.jnil m (a + 19)] := by simpa [lookupCode] using hcode.at_offset 4 (by simp [lookupCode])
  have i5 : CodeAt P (a + 5) [.copy t₁ t₃] := by simpa [lookupCode] using hcode.at_offset 5 (by simp [lookupCode])
  have i6 : CodeAt P (a + 6) [.copy s t₄] := by simpa [lookupCode] using hcode.at_offset 6 (by simp [lookupCode])
  have i7 : CodeAt P (a + 7) [.sub t₃ t₄] := by simpa [lookupCode] using hcode.at_offset 7 (by simp [lookupCode])
  have i8 : CodeAt P (a + 8) [.copy s t₄] := by simpa [lookupCode] using hcode.at_offset 8 (by simp [lookupCode])
  have i9 : CodeAt P (a + 9) [.copy t₁ t₅] := by simpa [lookupCode] using hcode.at_offset 9 (by simp [lookupCode])
  have i10 : CodeAt P (a + 10) [.sub t₄ t₅] := by simpa [lookupCode] using hcode.at_offset 10 (by simp [lookupCode])
  have i11 : CodeAt P (a + 11) [.add t₃ t₄] := by simpa [lookupCode] using hcode.at_offset 11 (by simp [lookupCode])
  have i12 : CodeAt P (a + 12) [.jz t₃ (a + 16)] := by simpa [lookupCode] using hcode.at_offset 12 (by simp [lookupCode])
  have i13 : CodeAt P (a + 13) [.move m t₁] := by simpa [lookupCode] using hcode.at_offset 13 (by simp [lookupCode])
  have i14 : CodeAt P (a + 14) [.push t₂ 1] := by simpa [lookupCode] using hcode.at_offset 14 (by simp [lookupCode])
  have i15 : CodeAt P (a + 15) [.jmp (a + 1)] := by simpa [lookupCode] using hcode.at_offset 15 (by simp [lookupCode])
  have i16 : CodeAt P (a + 16) [.pop s] := by simpa [lookupCode] using hcode.at_offset 16 (by simp [lookupCode])
  have i17 : CodeAt P (a + 17) [.copy m s] := by simpa [lookupCode] using hcode.at_offset 17 (by simp [lookupCode])
  have i18 : CodeAt P (a + 18) [.jmp (a + 21)] := by simpa [lookupCode] using hcode.at_offset 18 (by simp [lookupCode])
  have i19 : CodeAt P (a + 19) [.pop s] := by simpa [lookupCode] using hcode.at_offset 19 (by simp [lookupCode])
  have i20 : CodeAt P (a + 20) [.push s 0] := by simpa [lookupCode] using hcode.at_offset 20 (by simp [lookupCode])
  have i21 : CodeAt P (a + 21) [.jz t₂ (a + 24)] := by simpa [lookupCode] using hcode.at_offset 21 (by simp [lookupCode])
  have i22 : CodeAt P (a + 22) [.move t₁ m] := by simpa [lookupCode] using hcode.at_offset 22 (by simp [lookupCode])
  have i23 : CodeAt P (a + 23) [.jmp (a + 21)] := by simpa [lookupCode] using hcode.at_offset 23 (by simp [lookupCode])
  -- Setup: push sentinel 0 onto t₂.
  let c₁ : Config := { cfg with pc := a + 1, stk := Function.update cfg.stk t₂ (0 :: cfg.stk t₂) }
  have s0 : Steps P cfg c₁ (1 + len 0) := Steps.push i0 hpc
  have hk0 : Keeps used cfg c₁ := Keeps.update_stk_mem cfg (a + 1) m2 _
  -- Scan loop invariant, postcondition, measure and potential.
  let InvS : Config → Prop := fun c =>
    c.pc = a + 1 ∧ Keeps used cfg c ∧
    c.stk s = x :: rest ∧ c.stk t₃ = cfg.stk t₃ ∧ c.stk t₄ = cfg.stk t₄ ∧ c.stk t₅ = cfg.stk t₅ ∧
    ∃ moved, c.stk t₁ = moved ++ cfg.stk t₁ ∧
      c.stk t₂ = List.replicate moved.length 1 ++ (0 :: cfg.stk t₂) ∧
      moved.reverse ++ c.stk m = cfg.stk m ∧
      memOf (c.stk m) x = memOf (cfg.stk m) x
  let DoneS : Config → Prop := fun c =>
    c.pc = a + 21 ∧ Keeps used cfg c ∧
    c.stk s = memOf (cfg.stk m) x :: rest ∧
    c.stk t₃ = cfg.stk t₃ ∧ c.stk t₄ = cfg.stk t₄ ∧ c.stk t₅ = cfg.stk t₅ ∧
    ∃ moved, c.stk t₁ = moved ++ cfg.stk t₁ ∧
      c.stk t₂ = List.replicate moved.length 1 ++ (0 :: cfg.stk t₂) ∧
      moved.reverse ++ c.stk m = cfg.stk m
  let μS : Config → ℕ := fun c => (c.stk m).length
  let ΦS : Config → ℕ := fun c => 20 * (listSize (c.stk m) + 1) * (len x + 1)
  have hscan : ∀ c, InvS c → ∃ c' S, Steps P c c' S ∧ DoneS c' ∧ S ≤ ΦS c := by
    refine Steps.loop_potential InvS DoneS μS ΦS (fun c hI => ?_)
    obtain ⟨hpc_c, hk_c, hcs, hct3, hct4, hct5, moved, hct1, hct2, hrev, hmem⟩ := hI
    cases hcm : c.stk m with
    | nil =>
      -- Empty m: jump to a + 19, pop x, push 0.
      have hval0 : memOf (cfg.stk m) x = 0 := by rw [← hmem, hcm]; rfl
      let d₁ : Config := { c with pc := a + 19 }
      have st1 : Steps P c d₁ 1 := Steps.jnil_nil i1 hpc_c hcm
      let d₂ : Config := { d₁ with pc := a + 20, stk := Function.update d₁.stk s rest }
      have st19 : Steps P d₁ d₂ (1 + len x) := Steps.pop i19 rfl (by simp [d₁, hcs])
      let d₃ : Config := { d₂ with pc := a + 21, stk := Function.update d₂.stk s (0 :: d₂.stk s) }
      have st20 : Steps P d₂ d₃ (1 + len 0) := Steps.push i20 rfl
      have hk_st : Keeps used c d₃ :=
        ((Keeps.with_pc_mem used c (a + 19)).trans (Keeps.update_stk_mem d₁ (a + 20) ms _)).trans
          (Keeps.update_stk_mem d₂ (a + 21) ms _)
      refine Or.inl ⟨d₃, _, (st1.trans st19).trans st20, ⟨rfl, hk_c.trans hk_st,
        by simp [d₃, d₂, hval0], by simp [d₃, d₂, d₁, hs3.symm, hct3],
        by simp [d₃, d₂, d₁, hs4.symm, hct4], by simp [d₃, d₂, d₁, hs5.symm, hct5],
        moved, by simp [d₃, d₂, d₁, hs1.symm, hct1], by simp [d₃, d₂, d₁, hs2.symm, hct2],
        by simpa [d₃, d₂, d₁, hsm.symm, hcm] using hrev⟩, ?_⟩
      simp only [ΦS, hcm, listSize_nil, GI.Machine.len_zero]
      nlinarith
    | cons a₀ cur₁ =>
      -- Non-empty m: move a₀ to t₁, push 1 on t₂, check if cur₁ is empty.
      let d₁ : Config := { c with pc := a + 2 }
      have st1 : Steps P c d₁ 1 := Steps.jnil_cons i1 hpc_c hcm
      let d₂ : Config := { d₁ with pc := a + 3, stk := Function.update (Function.update d₁.stk m cur₁) t₁ (a₀ :: d₁.stk t₁) }
      have st2 : Steps P d₁ d₂ (1 + len a₀) := Steps.move_ne hm1 i2 rfl (by simp [d₁, hcm])
      have d₂t1 : d₂.stk t₁ = (a₀ :: moved) ++ cfg.stk t₁ := by simp [d₂, d₁, hct1]
      have d₂t2 : d₂.stk t₂ = List.replicate moved.length 1 ++ (0 :: cfg.stk t₂) := by
        simp [d₂, d₁, h12.symm, hm2.symm, hct2]
      have d₂m : d₂.stk m = cur₁ := by simp [d₂, hm1]
      let d₃ : Config := { d₂ with pc := a + 4, stk := Function.update d₂.stk t₂ (1 :: d₂.stk t₂) }
      have st3 : Steps P d₂ d₃ (1 + len 1) := Steps.push i3 rfl
      have d₃s : d₃.stk s = x :: rest := by simp [d₃, d₂, d₁, hs2, hs1, hsm, hcs]
      have d₃m : d₃.stk m = cur₁ := by simp [d₃, hm2, d₂m]
      have d₃t1 : d₃.stk t₁ = (a₀ :: moved) ++ cfg.stk t₁ := by simp [d₃, h12, d₂t1]
      have d₃t2 : d₃.stk t₂ = List.replicate (a₀ :: moved).length 1 ++ (0 :: cfg.stk t₂) := by
        simp [d₃, d₂t2, List.replicate_succ]
      have d₃t3 : d₃.stk t₃ = cfg.stk t₃ := by simp [d₃, d₂, d₁, h23.symm, h13.symm, hm3.symm, hct3]
      have d₃t4 : d₃.stk t₄ = cfg.stk t₄ := by simp [d₃, d₂, d₁, h24.symm, h14.symm, hm4.symm, hct4]
      have d₃t5 : d₃.stk t₅ = cfg.stk t₅ := by simp [d₃, d₂, d₁, h25.symm, h15.symm, hm5.symm, hct5]
      have hk03 : Keeps used c d₃ :=
        ((Keeps.with_pc_mem used c (a + 2)).trans (Keeps.update_stk₂_mem d₁ (a + 3) m1 mm _ _)).trans
          (Keeps.update_stk_mem d₂ (a + 4) m2 _)
      cases cur₁ with
      | nil =>
        -- Unpaired trailing address a₀: memOf [a₀] x = 0.
        have hval0 : memOf (cfg.stk m) x = 0 := by rw [← hmem, hcm]; rfl
        let d₄ : Config := { d₃ with pc := a + 19 }
        have st4 : Steps P d₃ d₄ 1 := Steps.jnil_nil i4 rfl d₃m
        let d₅ : Config := { d₄ with pc := a + 20, stk := Function.update d₄.stk s rest }
        have st19 : Steps P d₄ d₅ (1 + len x) := Steps.pop i19 rfl (by simp [d₄, d₃s])
        let d₆ : Config := { d₅ with pc := a + 21, stk := Function.update d₅.stk s (0 :: d₅.stk s) }
        have st20 : Steps P d₅ d₆ (1 + len 0) := Steps.push i20 rfl
        have hk_st : Keeps used d₃ d₆ :=
          ((Keeps.with_pc_mem used d₃ (a + 19)).trans (Keeps.update_stk_mem d₄ (a + 20) ms _)).trans
            (Keeps.update_stk_mem d₅ (a + 21) ms _)
        refine Or.inl ⟨d₆, _, ((((st1.trans st2).trans st3).trans st4).trans st19).trans st20,
          ⟨rfl, (hk_c.trans hk03).trans hk_st, by simp [d₆, d₅, hval0],
            by simp [d₆, d₅, d₄, hs3.symm, d₃t3], by simp [d₆, d₅, d₄, hs4.symm, d₃t4],
            by simp [d₆, d₅, d₄, hs5.symm, d₃t5], a₀ :: moved,
            by simp [d₆, d₅, d₄, hs1.symm, d₃t1], by simp [d₆, d₅, d₄, hs2.symm, d₃t2], ?_⟩, ?_⟩
        · simp only [d₆, d₅, d₄, Function.update_of_ne hsm.symm, d₃m, List.reverse_cons, List.append_nil]
          simpa [hcm] using hrev
        · simp only [ΦS, hcm, listSize_cons, listSize_nil, GI.Machine.len_one, GI.Machine.len_zero]
          nlinarith
      | cons v₀ cur₂ =>
        -- Pair (a₀, v₀): test equality a₀ = x using t₃, t₄, t₅.
        let d₄ : Config := { d₃ with pc := a + 5 }
        have st4 : Steps P d₃ d₄ 1 := Steps.jnil_cons i4 rfl d₃m
        have d₄t1 : d₄.stk t₁ = a₀ :: (moved ++ cfg.stk t₁) := by simpa [d₄] using d₃t1
        let d₅ : Config := { d₄ with pc := a + 6, stk := Function.update d₄.stk t₃ (a₀ :: d₄.stk t₃) }
        have st5 : Steps P d₄ d₅ (1 + len a₀) := Steps.copy i5 rfl d₄t1
        have d₅s : d₅.stk s = x :: rest := by simp [d₅, d₄, hs3, d₃s]
        have d₅t3 : d₅.stk t₃ = a₀ :: cfg.stk t₃ := by simp [d₅, d₄, d₃t3]
        have d₅t4 : d₅.stk t₄ = cfg.stk t₄ := by simp [d₅, d₄, h34.symm, d₃t4]
        let d₆ : Config := { d₅ with pc := a + 7, stk := Function.update d₅.stk t₄ (x :: d₅.stk t₄) }
        have st6 : Steps P d₅ d₆ (1 + len x) := Steps.copy i6 rfl d₅s
        have d₆t3 : d₆.stk t₃ = a₀ :: cfg.stk t₃ := by simp [d₆, h34, d₅t3]
        have d₆t4 : d₆.stk t₄ = x :: cfg.stk t₄ := by simp [d₆, d₅t4]
        let d₇ : Config := { d₆ with pc := a + 8, stk := Function.update (Function.update d₆.stk t₄ (cfg.stk t₄)) t₃ ((a₀ - x) :: cfg.stk t₃) }
        have st7 : Steps P d₆ d₇ (1 + len a₀ + len x) := Steps.sub h34 i7 rfl d₆t3 d₆t4
        have d₇s : d₇.stk s = x :: rest := by simp [d₇, d₆, hs3, hs4, d₅s]
        have d₇t1 : d₇.stk t₁ = a₀ :: (moved ++ cfg.stk t₁) := by simp [d₇, d₆, d₅, h13, h14, d₄t1]
        have d₇t3 : d₇.stk t₃ = (a₀ - x) :: cfg.stk t₃ := by simp [d₇]
        have d₇t4 : d₇.stk t₄ = cfg.stk t₄ := by simp [d₇, h34.symm]
        have d₇t5 : d₇.stk t₅ = cfg.stk t₅ := by simp [d₇, d₆, d₅, d₄, h35.symm, h45.symm, d₃t5]
        let d₈ : Config := { d₇ with pc := a + 9, stk := Function.update d₇.stk t₄ (x :: d₇.stk t₄) }
        have st8 : Steps P d₇ d₈ (1 + len x) := Steps.copy i8 rfl d₇s
        have d₈t1 : d₈.stk t₁ = a₀ :: (moved ++ cfg.stk t₁) := by simp [d₈, h14, d₇t1]
        have d₈t4 : d₈.stk t₄ = x :: cfg.stk t₄ := by simp [d₈, d₇t4]
        have d₈t5 : d₈.stk t₅ = cfg.stk t₅ := by simp [d₈, h45.symm, d₇t5]
        let d₉ : Config := { d₈ with pc := a + 10, stk := Function.update d₈.stk t₅ (a₀ :: d₈.stk t₅) }
        have st9 : Steps P d₈ d₉ (1 + len a₀) := Steps.copy i9 rfl d₈t1
        have d₉t4 : d₉.stk t₄ = x :: cfg.stk t₄ := by simp [d₉, h45, d₈t4]
        have d₉t5 : d₉.stk t₅ = a₀ :: cfg.stk t₅ := by simp [d₉, d₈t5]
        let d₁₀ : Config := { d₉ with pc := a + 11, stk := Function.update (Function.update d₉.stk t₅ (cfg.stk t₅)) t₄ ((x - a₀) :: cfg.stk t₄) }
        have st10 : Steps P d₉ d₁₀ (1 + len x + len a₀) := Steps.sub h45 i10 rfl d₉t4 d₉t5
        have d₁₀t3 : d₁₀.stk t₃ = (a₀ - x) :: cfg.stk t₃ := by simp [d₁₀, d₉, d₈, h34, h35, d₇t3]
        have d₁₀t4 : d₁₀.stk t₄ = (x - a₀) :: cfg.stk t₄ := by simp [d₁₀]
        let d₁₁ : Config := { d₁₀ with pc := a + 12, stk := Function.update (Function.update d₁₀.stk t₄ (cfg.stk t₄)) t₃ (((a₀ - x) + (x - a₀)) :: cfg.stk t₃) }
        have st11 : Steps P d₁₀ d₁₁ (1 + len (a₀ - x) + len (x - a₀)) := Steps.add h34 i11 rfl d₁₀t3 d₁₀t4
        have d₁₁s : d₁₁.stk s = x :: rest := by simp [d₁₁, d₁₀, d₉, d₈, hs3, hs4, hs5, d₇s]
        have d₁₁m : d₁₁.stk m = v₀ :: cur₂ := by simp [d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, hm3, hm4, hm5, d₃m]
        have d₁₁t1 : d₁₁.stk t₁ = (a₀ :: moved) ++ cfg.stk t₁ := by
          simp [d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, h13, h14, h15, d₃t1]
        have d₁₁t2 : d₁₁.stk t₂ = List.replicate (a₀ :: moved).length 1 ++ (0 :: cfg.stk t₂) := by
          simp [d₁₁, d₁₀, d₉, d₈, d₇, d₆, d₅, d₄, h23, h24, h25, d₃t2]
        have d₁₁t3 : d₁₁.stk t₃ = ((a₀ - x) + (x - a₀)) :: cfg.stk t₃ := by simp [d₁₁]
        have d₁₁t4 : d₁₁.stk t₄ = cfg.stk t₄ := by simp [d₁₁, h34.symm]
        have d₁₁t5 : d₁₁.stk t₅ = cfg.stk t₅ := by simp [d₁₁, d₁₀, h35.symm, h45.symm]
        have hk311 : Keeps used d₃ d₁₁ :=
          (((((((Keeps.with_pc_mem used d₃ (a + 5)).trans (Keeps.update_stk_mem d₄ (a + 6) m3 _)).trans
            (Keeps.update_stk_mem d₅ (a + 7) m4 _)).trans
            (Keeps.update_stk₂_mem d₆ (a + 8) m3 m4 _ _)).trans
            (Keeps.update_stk_mem d₇ (a + 9) m4 _)).trans
            (Keeps.update_stk_mem d₈ (a + 10) m5 _)).trans
            (Keeps.update_stk₂_mem d₉ (a + 11) m4 m5 _ _)).trans
            (Keeps.update_stk₂_mem d₁₀ (a + 12) m3 m4 _ _)
        have st_pre := (((((((((st1.trans st2).trans st3).trans st4).trans st5).trans st6).trans st7).trans st8).trans st9).trans st10).trans st11
        have hlen_ax : len (a₀ - x) ≤ len a₀ := GI.Machine.len_sub_le a₀ x
        have hlen_xa : len (x - a₀) ≤ len x := GI.Machine.len_sub_le x a₀
        by_cases heq : a₀ = x
        · -- Match: jump to a + 16, pop x, copy v₀ from m to s, jump to restore.
          have hval : memOf (cfg.stk m) x = v₀ := by rw [← hmem, hcm]; simp [heq]
          have hzero : (a₀ - x) + (x - a₀) = 0 := by omega
          let e₁ : Config := { d₁₁ with pc := a + 16, stk := Function.update d₁₁.stk t₃ (cfg.stk t₃) }
          have st12 : Steps P d₁₁ e₁ 1 := Steps.jz_zero i12 rfl (by rw [d₁₁t3, hzero])
          have e₁s : e₁.stk s = x :: rest := by simp [e₁, hs3, d₁₁s]
          have e₁m : e₁.stk m = v₀ :: cur₂ := by simp [e₁, hm3, d₁₁m]
          let e₂ : Config := { e₁ with pc := a + 17, stk := Function.update e₁.stk s rest }
          have st16 : Steps P e₁ e₂ (1 + len x) := Steps.pop i16 rfl e₁s
          have e₂m : e₂.stk m = v₀ :: cur₂ := by simp [e₂, hsm.symm, e₁m]
          let e₃ : Config := { e₂ with pc := a + 18, stk := Function.update e₂.stk s (v₀ :: e₂.stk s) }
          have st17 : Steps P e₂ e₃ (1 + len v₀) := Steps.copy i17 rfl e₂m
          let e₄ : Config := { e₃ with pc := a + 21 }
          have st18 : Steps P e₃ e₄ 1 := Steps.jmp i18 rfl
          have hk_end : Keeps used d₁₁ e₄ :=
            (((Keeps.update_stk_mem d₁₁ (a + 16) m3 _).trans (Keeps.update_stk_mem e₁ (a + 17) ms _)).trans
              (Keeps.update_stk_mem e₂ (a + 18) ms _)).trans
              (Keeps.with_pc_mem used e₃ (a + 21))
          refine Or.inl ⟨e₄, _, st_pre.trans (((st12.trans st16).trans st17).trans st18),
            ⟨rfl, ((hk_c.trans hk03).trans hk311).trans hk_end,
              by simp [e₄, e₃, e₂, hval],
              by simp [e₄, e₃, e₂, e₁, hs3.symm],
              by simp [e₄, e₃, e₂, e₁, hs4.symm, h34.symm, d₁₁t4],
              by simp [e₄, e₃, e₂, e₁, hs5.symm, h35.symm, d₁₁t5],
              a₀ :: moved,
              by simp [e₄, e₃, e₂, e₁, hs1.symm, h13, d₁₁t1],
              by simp [e₄, e₃, e₂, e₁, hs2.symm, h23, d₁₁t2], ?_⟩, ?_⟩
          · simp only [e₄, e₃, e₂, e₁, Function.update_of_ne hsm.symm, Function.update_of_ne hm3, d₁₁m,
              List.reverse_cons, List.append_assoc, List.singleton_append]
            simpa [hcm] using hrev
          · simp only [ΦS, hcm, listSize_cons, GI.Machine.len_one]
            nlinarith
        · -- Mismatch: move v₀ to t₁, push 1 on t₂, jump back to a + 1.
          have hne : (a₀ - x) + (x - a₀) ≠ 0 := by omega
          have hlen_sum : len ((a₀ - x) + (x - a₀)) ≤ len a₀ + len x + 1 := by
            have := GI.Machine.len_add_le_add (a₀ - x) (x - a₀)
            omega
          let e₁ : Config := { d₁₁ with pc := a + 13, stk := Function.update d₁₁.stk t₃ (cfg.stk t₃) }
          have st12 : Steps P d₁₁ e₁ (1 + len ((a₀ - x) + (x - a₀))) := Steps.jz_ne_zero i12 rfl d₁₁t3 hne
          have e₁m : e₁.stk m = v₀ :: cur₂ := by simp [e₁, hm3, d₁₁m]
          have e₁t1 : e₁.stk t₁ = (a₀ :: moved) ++ cfg.stk t₁ := by simp [e₁, h13, d₁₁t1]
          let e₂ : Config := { e₁ with pc := a + 14, stk := Function.update (Function.update e₁.stk m cur₂) t₁ (v₀ :: e₁.stk t₁) }
          have st13 : Steps P e₁ e₂ (1 + len v₀) := Steps.move_ne hm1 i13 rfl e₁m
          have e₂t2 : e₂.stk t₂ = List.replicate (a₀ :: moved).length 1 ++ (0 :: cfg.stk t₂) := by
            simp [e₂, e₁, h12.symm, hm2.symm, h23, d₁₁t2]
          let e₃ : Config := { e₂ with pc := a + 15, stk := Function.update e₂.stk t₂ (1 :: e₂.stk t₂) }
          have st14 : Steps P e₂ e₃ (1 + len 1) := Steps.push i14 rfl
          let e₄ : Config := { e₃ with pc := a + 1 }
          have st15 : Steps P e₃ e₄ 1 := Steps.jmp i15 rfl
          have hk_end : Keeps used d₁₁ e₄ :=
            (((Keeps.update_stk_mem d₁₁ (a + 13) m3 _).trans (Keeps.update_stk₂_mem e₁ (a + 14) m1 mm _ _)).trans
              (Keeps.update_stk_mem e₂ (a + 15) m2 _)).trans
              (Keeps.with_pc_mem used e₃ (a + 1))
          have he₄m : e₄.stk m = cur₂ := by simp [e₄, e₃, e₂, hm2, hm1]
          have hInvS' : InvS e₄ := by
            refine ⟨rfl, ((hk_c.trans hk03).trans hk311).trans hk_end,
              by simp [e₄, e₃, e₂, e₁, hs2, hs1, hsm, hs3, d₁₁s],
              by simp [e₄, e₃, e₂, e₁, h23.symm, h13.symm, hm3.symm],
              by simp [e₄, e₃, e₂, e₁, h24.symm, h14.symm, hm4.symm, h34.symm, d₁₁t4],
              by simp [e₄, e₃, e₂, e₁, h25.symm, h15.symm, hm5.symm, h35.symm, d₁₁t5],
              v₀ :: a₀ :: moved,
              by simp [e₄, e₃, e₂, h12, e₁t1],
              by simp [e₄, e₃, e₂t2, List.replicate_succ], ?_, ?_⟩
            · rw [he₄m]
              simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
              simpa [hcm] using hrev
            · rw [he₄m, ← hmem, hcm]
              simp [heq]
          have hμ_lt : μS e₄ < μS c := by
            simp only [μS, he₄m, hcm, List.length_cons]
            omega
          refine Or.inr ⟨e₄, _, st_pre.trans (((st12.trans st13).trans st14).trans st15), hInvS', hμ_lt, ?_⟩
          simp only [ΦS, he₄m, hcm, listSize_cons, GI.Machine.len_one]
          nlinarith
  have hInvS0 : InvS c₁ :=
    ⟨rfl, hk0, by simp [c₁, hs2, hs], by simp [c₁, h23.symm], by simp [c₁, h24.symm],
      by simp [c₁, h25.symm], [], by simp [c₁, h12], by simp [c₁], by simp [c₁, hm2],
      by simp [c₁, hm2]⟩
  obtain ⟨c₂, S_scan, hst_scan, hDoneS, hS_scan⟩ := hscan c₁ hInvS0
  have hΦS0 : ΦS c₁ = 20 * (listSize (cfg.stk m) + 1) * (len x + 1) := by
    simp [ΦS, c₁, hm2]
  rw [hΦS0] at hS_scan
  -- Restore loop: move elements back from t₁ to m using unary markers on t₂.
  let InvR : Config → Prop := fun c =>
    c.pc = a + 21 ∧ Keeps used cfg c ∧
    c.stk s = memOf (cfg.stk m) x :: rest ∧
    c.stk t₃ = cfg.stk t₃ ∧ c.stk t₄ = cfg.stk t₄ ∧ c.stk t₅ = cfg.stk t₅ ∧
    ∃ moved, c.stk t₁ = moved ++ cfg.stk t₁ ∧
      c.stk t₂ = List.replicate moved.length 1 ++ (0 :: cfg.stk t₂) ∧
      moved.reverse ++ c.stk m = cfg.stk m
  let DoneR : Config → Prop := fun c =>
    c.pc = a + 24 ∧ c.stk s = memOf (cfg.stk m) x :: rest ∧ Keeps [s] cfg c
  let μR : Config → ℕ := fun c => (c.stk t₁).length - (cfg.stk t₁).length
  let ΦR : Config → ℕ := fun c => 4 * listSize (c.stk t₁) - 4 * listSize (cfg.stk t₁) + 1
  have hrest : ∀ c, InvR c → ∃ c' S, Steps P c c' S ∧ DoneR c' ∧ S ≤ ΦR c := by
    refine Steps.loop_potential InvR DoneR μR ΦR (fun c hI => ?_)
    obtain ⟨hpc_c, hk_c, hcs, hct3, hct4, hct5, moved, hct1, hct2, hrev⟩ := hI
    cases moved with
    | nil =>
      simp only [List.nil_append, List.length_nil, List.replicate_zero, List.reverse_nil] at hct1 hct2 hrev
      let d₁ : Config := { c with pc := a + 24, stk := Function.update c.stk t₂ (cfg.stk t₂) }
      have st21 : Steps P c d₁ 1 := Steps.jz_zero i21 hpc_c hct2
      have hk_fin : Keeps used cfg d₁ := hk_c.trans (Keeps.update_stk_mem c (a + 24) m2 _)
      have hkeeps : Keeps [s] cfg d₁ := hk_fin.of_subset_eq fun w hw hnot => by
        simp only [used, List.mem_cons, List.not_mem_nil, or_false] at hw hnot
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact absurd rfl hnot
        · simp [d₁, hm2, hrev]
        · simp [d₁, h12, hct1]
        · simp [d₁]
        · simp [d₁, h23.symm, hct3]
        · simp [d₁, h24.symm, hct4]
        · simp [d₁, h25.symm, hct5]
      refine Or.inl ⟨d₁, 1, st21, ⟨rfl, by simp [d₁, hs2, hcs], hkeeps⟩, by simp only [ΦR]; omega⟩
    | cons w moved' =>
      simp only [List.cons_append, List.length_cons, List.replicate_succ] at hct1 hct2
      let d₁ : Config := { c with pc := a + 22, stk := Function.update c.stk t₂ (List.replicate moved'.length 1 ++ (0 :: cfg.stk t₂)) }
      have st21 : Steps P c d₁ (1 + len 1) := Steps.jz_ne_zero i21 hpc_c hct2 (by omega)
      have d₁t1 : d₁.stk t₁ = w :: (moved' ++ cfg.stk t₁) := by simp [d₁, h12, hct1]
      let d₂ : Config := { d₁ with pc := a + 23, stk := Function.update (Function.update d₁.stk t₁ (moved' ++ cfg.stk t₁)) m (w :: d₁.stk m) }
      have st22 : Steps P d₁ d₂ (1 + len w) := Steps.move_ne hm1.symm i22 rfl d₁t1
      let d₃ : Config := { d₂ with pc := a + 21 }
      have st23 : Steps P d₂ d₃ 1 := Steps.jmp i23 rfl
      have hk_st : Keeps used c d₃ :=
        ((Keeps.update_stk_mem c (a + 22) m2 _).trans (Keeps.update_stk₂_mem d₁ (a + 23) mm m1 _ _)).trans
          (Keeps.with_pc_mem used d₂ (a + 21))
      have hd₃t1 : d₃.stk t₁ = moved' ++ cfg.stk t₁ := by simp [d₃, d₂, hm1.symm]
      have hInvR' : InvR d₃ := by
        refine ⟨rfl, hk_c.trans hk_st,
          by simp [d₃, d₂, d₁, hsm, hs1, hs2, hcs],
          by simp [d₃, d₂, d₁, hm3.symm, h13.symm, h23.symm, hct3],
          by simp [d₃, d₂, d₁, hm4.symm, h14.symm, h24.symm, hct4],
          by simp [d₃, d₂, d₁, hm5.symm, h15.symm, h25.symm, hct5],
          moved', hd₃t1, by simp [d₃, d₂, d₁, hm2.symm, h12.symm], ?_⟩
        simp only [d₃, d₂, d₁, Function.update_self, Function.update_of_ne hm2]
        simpa [List.reverse_cons, List.append_assoc] using hrev
      have hμ_lt : μR d₃ < μR c := by
        simp only [μR, hd₃t1, hct1, List.length_cons, List.length_append]
        omega
      refine Or.inr ⟨d₃, _, (st21.trans st22).trans st23, hInvR', hμ_lt, ?_⟩
      simp only [ΦR, hd₃t1, hct1, listSize_cons, listSize_append, GI.Machine.len_one]
      omega
  obtain ⟨c₃, S_rest, hst_rest, ⟨hpc₃, hs₃, hk₃⟩, hS_rest⟩ := hrest c₂ hDoneS
  obtain ⟨_, _, _, _, _, _, moved_end, hc₂t1, _, hrev_end⟩ := hDoneS
  have hΦR0 : ΦR c₂ ≤ 4 * listSize (cfg.stk m) + 1 := by
    have hsz : listSize moved_end ≤ listSize (cfg.stk m) := by
      have h1 : listSize moved_end + listSize (c₂.stk m) = listSize (cfg.stk m) := by
        rw [← listSize_reverse moved_end, ← listSize_append, hrev_end]
      omega
    simp only [ΦR, hc₂t1, listSize_append]
    omega
  refine ⟨c₃, _, (s0.trans hst_scan).trans hst_rest, ?_, hs₃, hk₃, ?_⟩
  · simp [hpc₃, lookupCode]
  · simp only [GI.Machine.len_zero]
    nlinarith

/-- `LookupBlock`: memory lookup in `O((listSize m + 1) * (len x + 1))` cost. -/
theorem lookupBlock : LookupBlock :=
  ⟨lookupCode, 26, lookupBlock_spec⟩

end GI.Turing
