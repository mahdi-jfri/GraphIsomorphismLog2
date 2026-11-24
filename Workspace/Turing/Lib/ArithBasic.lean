/-
Stack machine code blocks for addition, subtraction, less-than, equality and multiplication.

Each block implements `GI.Turing.BinBlock` for its operation in `GI.Machine.BinOp`: starting with
`y :: x :: rest` on stack `s`, it ends with `f x y :: rest` on `s`, restores every scratch stack
it uses, and runs at cost quadratic in `len x + len y + 1`.
-/
module

public import Workspace.Turing.Lib.Logic

@[expose] public section

namespace GI.Turing

open GI.Machine (len)
open GI.Turing.SM

/-! ### Addition -/

/-- Code for `x + y`: moves `y` to `s + 1` and adds it to `x`. -/
def addCode (s : Stk) (_a : ℕ) : List Instr :=
  let t := scratch s 1
  [.move s t, .add s t]

theorem addBlock : BinBlock (· + ·) addCode 4 := by
  intro s P a cfg x y rest hcode hpc hs
  let t := scratch s 1
  have hst : s ≠ t := (scratch_ne_self s (by decide)).symm
  have hts : t ≠ s := hst.symm
  have h0 : CodeAt P a [.move s t] := hcode.head_singleton
  have h1 : CodeAt P (a + 1) [.add s t] := hcode.tail.head_singleton
  let c₁ : Config :=
    { cfg with pc := a + 1, stk := Function.update (Function.update cfg.stk s (x :: rest)) t (y :: cfg.stk t) }
  have s0 : Steps P cfg c₁ (1 + len y) := Steps.move_ne hst h0 hpc hs
  have hc₁s : c₁.stk s = x :: rest := by simp [c₁, hst]
  have hc₁t : c₁.stk t = y :: cfg.stk t := by simp [c₁]
  let c₂ : Config :=
    { c₁ with pc := a + 1 + 1, stk := Function.update (Function.update c₁.stk t (cfg.stk t)) s ((x + y) :: rest) }
  have s1 : Steps P c₁ c₂ (1 + len x + len y) := Steps.add hst h1 rfl hc₁s hc₁t
  have hk0 : Keeps [s, t] cfg c₁ := Keeps.update_stk₂_mem cfg (a + 1) (by simp) (by simp) _ _
  have hk1 : Keeps [s, t] c₁ c₂ := Keeps.update_stk₂_mem c₁ (a + 1 + 1) (by simp) (by simp) _ _
  have hc₂t : c₂.stk t = cfg.stk t := by simp [c₂, hts]
  have hc₂s : c₂.stk s = (x + y) :: rest := by simp [c₂]
  have hkeeps : Keeps [s] cfg c₂ := (hk0.trans hk1).of_subset_eq fun u hu hnot => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hnot
    rcases hu with rfl | rfl
    · exact absurd rfl hnot
    · exact hc₂t
  refine ⟨c₂, (1 + len y) + (1 + len x + len y), s0.trans s1, ?_, hc₂s, hkeeps, ?_⟩
  · simp [c₂, addCode]
  · nlinarith

/-! ### Subtraction -/

/-- Code for `x - y`: moves `y` to `s + 1` and subtracts it from `x`. -/
def subCode (s : Stk) (_a : ℕ) : List Instr :=
  let t := scratch s 1
  [.move s t, .sub s t]

theorem subBlock : BinBlock (· - ·) subCode 4 := by
  intro s P a cfg x y rest hcode hpc hs
  let t := scratch s 1
  have hst : s ≠ t := (scratch_ne_self s (by decide)).symm
  have hts : t ≠ s := hst.symm
  have h0 : CodeAt P a [.move s t] := hcode.head_singleton
  have h1 : CodeAt P (a + 1) [.sub s t] := hcode.tail.head_singleton
  let c₁ : Config :=
    { cfg with pc := a + 1, stk := Function.update (Function.update cfg.stk s (x :: rest)) t (y :: cfg.stk t) }
  have s0 : Steps P cfg c₁ (1 + len y) := Steps.move_ne hst h0 hpc hs
  have hc₁s : c₁.stk s = x :: rest := by simp [c₁, hst]
  have hc₁t : c₁.stk t = y :: cfg.stk t := by simp [c₁]
  let c₂ : Config :=
    { c₁ with pc := a + 1 + 1, stk := Function.update (Function.update c₁.stk t (cfg.stk t)) s ((x - y) :: rest) }
  have s1 : Steps P c₁ c₂ (1 + len x + len y) := Steps.sub hst h1 rfl hc₁s hc₁t
  have hk0 : Keeps [s, t] cfg c₁ := Keeps.update_stk₂_mem cfg (a + 1) (by simp) (by simp) _ _
  have hk1 : Keeps [s, t] c₁ c₂ := Keeps.update_stk₂_mem c₁ (a + 1 + 1) (by simp) (by simp) _ _
  have hc₂t : c₂.stk t = cfg.stk t := by simp [c₂, hts]
  have hc₂s : c₂.stk s = (x - y) :: rest := by simp [c₂]
  have hkeeps : Keeps [s] cfg c₂ := (hk0.trans hk1).of_subset_eq fun u hu hnot => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hnot
    rcases hu with rfl | rfl
    · exact absurd rfl hnot
    · exact hc₂t
  refine ⟨c₂, (1 + len y) + (1 + len x + len y), s0.trans s1, ?_, hc₂s, hkeeps, ?_⟩
  · simp [c₂, subCode]
  · nlinarith

/-! ### Less-than -/

/-- Code for `x < y`: computes `y - x` on `s + 1` and pushes 1 if it is nonzero, 0 otherwise. -/
def ltCode (s : Stk) (a : ℕ) : List Instr :=
  let t := scratch s 1
  [.move s t, .sub t s, .jz t (a + 5), .push s 1, .jmp (a + 6), .push s 0]

theorem ltBlock : BinBlock (fun x y => if x < y then 1 else 0) ltCode 8 := by
  intro s P a cfg x y rest hcode hpc hs
  let t := scratch s 1
  have hst : s ≠ t := (scratch_ne_self s (by decide)).symm
  have hts : t ≠ s := hst.symm
  have h0 : CodeAt P a [.move s t] := by simpa [ltCode] using hcode.at_offset 0 (by simp [ltCode])
  have h1 : CodeAt P (a + 1) [.sub t s] := by simpa [ltCode] using hcode.at_offset 1 (by simp [ltCode])
  have h2 : CodeAt P (a + 2) [.jz t (a + 5)] := by simpa [ltCode] using hcode.at_offset 2 (by simp [ltCode])
  have h3 : CodeAt P (a + 3) [.push s 1] := by simpa [ltCode] using hcode.at_offset 3 (by simp [ltCode])
  have h4 : CodeAt P (a + 4) [.jmp (a + 6)] := by simpa [ltCode] using hcode.at_offset 4 (by simp [ltCode])
  have h5 : CodeAt P (a + 5) [.push s 0] := by simpa [ltCode] using hcode.at_offset 5 (by simp [ltCode])
  let c₁ : Config :=
    { cfg with pc := a + 1, stk := Function.update (Function.update cfg.stk s (x :: rest)) t (y :: cfg.stk t) }
  have s0 : Steps P cfg c₁ (1 + len y) := Steps.move_ne hst h0 hpc hs
  have hc₁s : c₁.stk s = x :: rest := by simp [c₁, hst]
  have hc₁t : c₁.stk t = y :: cfg.stk t := by simp [c₁]
  let c₂ : Config :=
    { c₁ with pc := a + 2, stk := Function.update (Function.update c₁.stk s rest) t ((y - x) :: cfg.stk t) }
  have s1 : Steps P c₁ c₂ (1 + len y + len x) := Steps.sub hts h1 rfl hc₁t hc₁s
  have hc₂s : c₂.stk s = rest := by simp [c₂, hst]
  have hc₂t : c₂.stk t = (y - x) :: cfg.stk t := by simp [c₂]
  have hk01 : Keeps [s, t] cfg c₂ :=
    (Keeps.update_stk₂_mem cfg (a + 1) (by simp) (by simp) _ _).trans
      (Keeps.update_stk₂_mem c₁ (a + 2) (by simp) (by simp) _ _)
  have hlen_sub : len (y - x) ≤ len y := GI.Machine.len_sub_le y x
  by_cases hlt : x < y
  · have hne : y - x ≠ 0 := by omega
    let c₃ : Config := { c₂ with pc := a + 3, stk := Function.update c₂.stk t (cfg.stk t) }
    have s2 : Steps P c₂ c₃ (1 + len (y - x)) := Steps.jz_ne_zero h2 rfl hc₂t hne
    have hc₃s : c₃.stk s = rest := by simp [c₃, hst, hc₂s]
    have hc₃t : c₃.stk t = cfg.stk t := by simp [c₃]
    let c₄ : Config := { c₃ with pc := a + 4, stk := Function.update c₃.stk s (1 :: c₃.stk s) }
    have s3 : Steps P c₃ c₄ (1 + len 1) := Steps.push h3 rfl
    let c₅ : Config := { c₄ with pc := a + 6 }
    have s4 : Steps P c₄ c₅ 1 := Steps.jmp h4 rfl
    have hk234 : Keeps [s, t] c₂ c₅ :=
      ((Keeps.update_stk_mem c₂ (a + 3) (by simp) _).trans
        (Keeps.update_stk_mem c₃ (a + 4) (by simp) _)).trans
        (Keeps.with_pc_mem [s, t] c₄ (a + 6))
    have hc₅s : c₅.stk s = (if x < y then 1 else 0) :: rest := by simp [c₅, c₄, hc₃s, hlt]
    have hc₅t : c₅.stk t = cfg.stk t := by simp [c₅, c₄, hts, hc₃t]
    have hkeeps : Keeps [s] cfg c₅ := (hk01.trans hk234).of_subset_eq fun u hu hnot => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hnot
      rcases hu with rfl | rfl
      · exact absurd rfl hnot
      · exact hc₅t
    refine ⟨c₅, _, (((s0.trans s1).trans s2).trans s3).trans s4, ?_, hc₅s, hkeeps, ?_⟩
    · simp [c₅, ltCode]
    · simp only [GI.Machine.len_one]
      nlinarith
  · have hzero : y - x = 0 := by omega
    let c₃ : Config := { c₂ with pc := a + 5, stk := Function.update c₂.stk t (cfg.stk t) }
    have s2 : Steps P c₂ c₃ 1 := Steps.jz_zero h2 rfl (by rw [hc₂t, hzero])
    have hc₃s : c₃.stk s = rest := by simp [c₃, hst, hc₂s]
    have hc₃t : c₃.stk t = cfg.stk t := by simp [c₃]
    let c₄ : Config := { c₃ with pc := a + 6, stk := Function.update c₃.stk s (0 :: c₃.stk s) }
    have s3 : Steps P c₃ c₄ (1 + len 0) := Steps.push h5 rfl
    have hk23 : Keeps [s, t] c₂ c₄ :=
      (Keeps.update_stk_mem c₂ (a + 5) (by simp) _).trans
        (Keeps.update_stk_mem c₃ (a + 6) (by simp) _)
    have hc₄s : c₄.stk s = (if x < y then 1 else 0) :: rest := by simp [c₄, hc₃s, hlt]
    have hc₄t : c₄.stk t = cfg.stk t := by simp [c₄, hts, hc₃t]
    have hkeeps : Keeps [s] cfg c₄ := (hk01.trans hk23).of_subset_eq fun u hu hnot => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hnot
      rcases hu with rfl | rfl
      · exact absurd rfl hnot
      · exact hc₄t
    refine ⟨c₄, _, ((s0.trans s1).trans s2).trans s3, ?_, hc₄s, hkeeps, ?_⟩
    · simp [c₄, ltCode]
    · simp only [GI.Machine.len_zero]
      nlinarith

/-! ### Equality -/

/-- Code for `x = y`: computes `(x - y) + (y - x)` and pushes 1 if it is 0, 0 otherwise. -/
def eqCode (s : Stk) (a : ℕ) : List Instr :=
  let t := scratch s 1
  let u := scratch s 2
  [ .move s t, .copy s u, .copy t s, .sub s u, .move s u, .sub s t, .add s u,
    .jz s (a + 10), .push s 0, .jmp (a + 11), .push s 1 ]

theorem eqBlock : BinBlock (fun x y => if x = y then 1 else 0) eqCode 16 := by
  intro s P a cfg x y rest hcode hpc hs
  let t := scratch s 1
  let u := scratch s 2
  have hst : s ≠ t := (scratch_ne_self s (by decide)).symm
  have hsu : s ≠ u := (scratch_ne_self s (by decide)).symm
  have htu : t ≠ u := scratch_ne (by decide)
  have h0 : CodeAt P a [.move s t] := by simpa [eqCode] using hcode.at_offset 0 (by simp [eqCode])
  have h1 : CodeAt P (a + 1) [.copy s u] := by simpa [eqCode] using hcode.at_offset 1 (by simp [eqCode])
  have h2 : CodeAt P (a + 2) [.copy t s] := by simpa [eqCode] using hcode.at_offset 2 (by simp [eqCode])
  have h3 : CodeAt P (a + 3) [.sub s u] := by simpa [eqCode] using hcode.at_offset 3 (by simp [eqCode])
  have h4 : CodeAt P (a + 4) [.move s u] := by simpa [eqCode] using hcode.at_offset 4 (by simp [eqCode])
  have h5 : CodeAt P (a + 5) [.sub s t] := by simpa [eqCode] using hcode.at_offset 5 (by simp [eqCode])
  have h6 : CodeAt P (a + 6) [.add s u] := by simpa [eqCode] using hcode.at_offset 6 (by simp [eqCode])
  have h7 : CodeAt P (a + 7) [.jz s (a + 10)] := by simpa [eqCode] using hcode.at_offset 7 (by simp [eqCode])
  have h8 : CodeAt P (a + 8) [.push s 0] := by simpa [eqCode] using hcode.at_offset 8 (by simp [eqCode])
  have h9 : CodeAt P (a + 9) [.jmp (a + 11)] := by simpa [eqCode] using hcode.at_offset 9 (by simp [eqCode])
  have h10 : CodeAt P (a + 10) [.push s 1] := by simpa [eqCode] using hcode.at_offset 10 (by simp [eqCode])
  let c₁ : Config :=
    { cfg with pc := a + 1, stk := Function.update (Function.update cfg.stk s (x :: rest)) t (y :: cfg.stk t) }
  have s0 : Steps P cfg c₁ (1 + len y) := Steps.move_ne hst h0 hpc hs
  have c₁s : c₁.stk s = x :: rest := by simp [c₁, hst]
  have c₁t : c₁.stk t = y :: cfg.stk t := by simp [c₁]
  have c₁u : c₁.stk u = cfg.stk u := by simp [c₁, htu.symm, hsu.symm]
  let c₂ : Config := { c₁ with pc := a + 2, stk := Function.update c₁.stk u (x :: c₁.stk u) }
  have s1 : Steps P c₁ c₂ (1 + len x) := Steps.copy h1 rfl c₁s
  have c₂s : c₂.stk s = x :: rest := by simp [c₂, hsu, c₁s]
  have c₂t : c₂.stk t = y :: cfg.stk t := by simp [c₂, htu, c₁t]
  have c₂u : c₂.stk u = x :: cfg.stk u := by simp [c₂, c₁u]
  let c₃ : Config := { c₂ with pc := a + 3, stk := Function.update c₂.stk s (y :: c₂.stk s) }
  have s2 : Steps P c₂ c₃ (1 + len y) := Steps.copy h2 rfl c₂t
  have c₃s : c₃.stk s = y :: x :: rest := by simp [c₃, c₂s]
  have c₃t : c₃.stk t = y :: cfg.stk t := by simp [c₃, hst.symm, c₂t]
  have c₃u : c₃.stk u = x :: cfg.stk u := by simp [c₃, hsu.symm, c₂u]
  let c₄ : Config :=
    { c₃ with pc := a + 4, stk := Function.update (Function.update c₃.stk u (cfg.stk u)) s ((y - x) :: x :: rest) }
  have s3 : Steps P c₃ c₄ (1 + len y + len x) := Steps.sub hsu h3 rfl c₃s c₃u
  have c₄s : c₄.stk s = (y - x) :: x :: rest := by simp [c₄]
  have c₄t : c₄.stk t = y :: cfg.stk t := by simp [c₄, hst.symm, htu, c₃t]
  have c₄u : c₄.stk u = cfg.stk u := by simp [c₄, hsu.symm]
  let c₅ : Config :=
    { c₄ with pc := a + 5, stk := Function.update (Function.update c₄.stk s (x :: rest)) u ((y - x) :: c₄.stk u) }
  have s4 : Steps P c₄ c₅ (1 + len (y - x)) := Steps.move_ne hsu h4 rfl c₄s
  have c₅s : c₅.stk s = x :: rest := by simp [c₅, hsu]
  have c₅t : c₅.stk t = y :: cfg.stk t := by simp [c₅, htu, hst.symm, c₄t]
  have c₅u : c₅.stk u = (y - x) :: cfg.stk u := by simp [c₅, c₄u]
  let c₆ : Config :=
    { c₅ with pc := a + 6, stk := Function.update (Function.update c₅.stk t (cfg.stk t)) s ((x - y) :: rest) }
  have s5 : Steps P c₅ c₆ (1 + len x + len y) := Steps.sub hst h5 rfl c₅s c₅t
  have c₆s : c₆.stk s = (x - y) :: rest := by simp [c₆]
  have c₆t : c₆.stk t = cfg.stk t := by simp [c₆, hst.symm]
  have c₆u : c₆.stk u = (y - x) :: cfg.stk u := by simp [c₆, hsu.symm, htu.symm, c₅u]
  let c₇ : Config :=
    { c₆ with pc := a + 7, stk := Function.update (Function.update c₆.stk u (cfg.stk u)) s (((x - y) + (y - x)) :: rest) }
  have s6 : Steps P c₆ c₇ (1 + len (x - y) + len (y - x)) := Steps.add hsu h6 rfl c₆s c₆u
  have c₇s : c₇.stk s = ((x - y) + (y - x)) :: rest := by simp [c₇]
  have c₇t : c₇.stk t = cfg.stk t := by simp [c₇, hst.symm, htu, c₆t]
  have c₇u : c₇.stk u = cfg.stk u := by simp [c₇, hsu.symm]
  have hk_mid : Keeps [s, t, u] cfg c₇ := by
    have k0 : Keeps [s, t, u] cfg c₁ := Keeps.update_stk₂_mem cfg (a + 1) (by simp) (by simp) _ _
    have k1 : Keeps [s, t, u] c₁ c₂ := Keeps.update_stk_mem c₁ (a + 2) (by simp) _
    have k2 : Keeps [s, t, u] c₂ c₃ := Keeps.update_stk_mem c₂ (a + 3) (by simp) _
    have k3 : Keeps [s, t, u] c₃ c₄ := Keeps.update_stk₂_mem c₃ (a + 4) (by simp) (by simp) _ _
    have k4 : Keeps [s, t, u] c₄ c₅ := Keeps.update_stk₂_mem c₄ (a + 5) (by simp) (by simp) _ _
    have k5 : Keeps [s, t, u] c₅ c₆ := Keeps.update_stk₂_mem c₅ (a + 6) (by simp) (by simp) _ _
    have k6 : Keeps [s, t, u] c₆ c₇ := Keeps.update_stk₂_mem c₆ (a + 7) (by simp) (by simp) _ _
    exact (((((k0.trans k1).trans k2).trans k3).trans k4).trans k5).trans k6
  have hlen_xy : len (x - y) ≤ len x := GI.Machine.len_sub_le x y
  have hlen_yx : len (y - x) ≤ len y := GI.Machine.len_sub_le y x
  have hlen_sum : len ((x - y) + (y - x)) ≤ len x + len y + 1 := by
    have := GI.Machine.len_add_le_add (x - y) (y - x)
    omega
  have s_mid := (((((s0.trans s1).trans s2).trans s3).trans s4).trans s5).trans s6
  by_cases heq : x = y
  · have hzero : (x - y) + (y - x) = 0 := by omega
    let c₈ : Config := { c₇ with pc := a + 10, stk := Function.update c₇.stk s rest }
    have s7 : Steps P c₇ c₈ 1 := Steps.jz_zero h7 rfl (by rw [c₇s, hzero])
    have c₈s : c₈.stk s = rest := by simp [c₈]
    let c₉ : Config := { c₈ with pc := a + 11, stk := Function.update c₈.stk s (1 :: c₈.stk s) }
    have s8 : Steps P c₈ c₉ (1 + len 1) := Steps.push h10 rfl
    have hk_end : Keeps [s, t, u] c₇ c₉ :=
      (Keeps.update_stk_mem c₇ (a + 10) (by simp) _).trans
        (Keeps.update_stk_mem c₈ (a + 11) (by simp) _)
    have c₉s : c₉.stk s = (if x = y then 1 else 0) :: rest := by simp [c₉, c₈s, heq]
    have c₉t : c₉.stk t = cfg.stk t := by simp [c₉, c₈, hst.symm, c₇t]
    have c₉u : c₉.stk u = cfg.stk u := by simp [c₉, c₈, hsu.symm, c₇u]
    have hkeeps : Keeps [s] cfg c₉ := (hk_mid.trans hk_end).of_subset_eq fun w hw hnot => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hnot
      rcases hw with rfl | rfl | rfl
      · exact absurd rfl hnot
      · exact c₉t
      · exact c₉u
    refine ⟨c₉, _, (s_mid.trans s7).trans s8, ?_, c₉s, hkeeps, ?_⟩
    · simp [c₉, eqCode]
    · simp only [GI.Machine.len_one]
      nlinarith
  · have hne : (x - y) + (y - x) ≠ 0 := by omega
    let c₈ : Config := { c₇ with pc := a + 8, stk := Function.update c₇.stk s rest }
    have s7 : Steps P c₇ c₈ (1 + len ((x - y) + (y - x))) := Steps.jz_ne_zero h7 rfl c₇s hne
    have c₈s : c₈.stk s = rest := by simp [c₈]
    let c₉ : Config := { c₈ with pc := a + 9, stk := Function.update c₈.stk s (0 :: c₈.stk s) }
    have s8 : Steps P c₈ c₉ (1 + len 0) := Steps.push h8 rfl
    let c₁₀ : Config := { c₉ with pc := a + 11 }
    have s9 : Steps P c₉ c₁₀ 1 := Steps.jmp h9 rfl
    have hk_end : Keeps [s, t, u] c₇ c₁₀ :=
      ((Keeps.update_stk_mem c₇ (a + 8) (by simp) _).trans
        (Keeps.update_stk_mem c₈ (a + 9) (by simp) _)).trans
        (Keeps.with_pc_mem [s, t, u] c₉ (a + 11))
    have c₁₀s : c₁₀.stk s = (if x = y then 1 else 0) :: rest := by simp [c₁₀, c₉, c₈s, heq]
    have c₁₀t : c₁₀.stk t = cfg.stk t := by simp [c₁₀, c₉, c₈, hst.symm, c₇t]
    have c₁₀u : c₁₀.stk u = cfg.stk u := by simp [c₁₀, c₉, c₈, hsu.symm, c₇u]
    have hkeeps : Keeps [s] cfg c₁₀ := (hk_mid.trans hk_end).of_subset_eq fun w hw hnot => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hnot
      rcases hw with rfl | rfl | rfl
      · exact absurd rfl hnot
      · exact c₁₀t
      · exact c₁₀u
    refine ⟨c₁₀, _, ((s_mid.trans s7).trans s8).trans s9, ?_, c₁₀s, hkeeps, ?_⟩
    · simp [c₁₀, eqCode]
    · simp only [GI.Machine.len_zero]
      nlinarith

/-! ### Multiplication -/

/-- Shift-and-add multiplication for `x * y`. Stack `s + 1` holds the shifted multiplicand `b`,
stack `s + 2` holds the shrinking multiplier `n`, and stack `s + 3` is temporary scratch. -/
def mulCode (s : Stk) (a : ℕ) : List Instr :=
  let t₁ := scratch s 1
  let t₂ := scratch s 2
  let t₃ := scratch s 3
  [ .move s t₁, .move s t₂, .push s 0,
    .copy t₂ t₃, .jz t₃ (a + 13),
    .copy t₂ t₃, .parity t₃, .jz t₃ (a + 10),
    .copy t₁ t₃, .add s t₃,
    .double t₁, .half t₂, .jmp (a + 3),
    .pop t₁, .pop t₂ ]

theorem mulBlock : BinBlock (· * ·) mulCode 20 := by
  intro s P a cfg x y rest hcode hpc hs
  let t₁ := scratch s 1
  let t₂ := scratch s 2
  let t₃ := scratch s 3
  have hs1 : s ≠ t₁ := (scratch_ne_self s (by decide)).symm
  have hs2 : s ≠ t₂ := (scratch_ne_self s (by decide)).symm
  have hs3 : s ≠ t₃ := (scratch_ne_self s (by decide)).symm
  have h12 : t₁ ≠ t₂ := scratch_ne (by decide)
  have h13 : t₁ ≠ t₃ := scratch_ne (by decide)
  have h23 : t₂ ≠ t₃ := scratch_ne (by decide)
  have i0 : CodeAt P a [.move s t₁] := by simpa [mulCode] using hcode.at_offset 0 (by simp [mulCode])
  have i1 : CodeAt P (a + 1) [.move s t₂] := by simpa [mulCode] using hcode.at_offset 1 (by simp [mulCode])
  have i2 : CodeAt P (a + 2) [.push s 0] := by simpa [mulCode] using hcode.at_offset 2 (by simp [mulCode])
  have i3 : CodeAt P (a + 3) [.copy t₂ t₃] := by simpa [mulCode] using hcode.at_offset 3 (by simp [mulCode])
  have i4 : CodeAt P (a + 4) [.jz t₃ (a + 13)] := by simpa [mulCode] using hcode.at_offset 4 (by simp [mulCode])
  have i5 : CodeAt P (a + 5) [.copy t₂ t₃] := by simpa [mulCode] using hcode.at_offset 5 (by simp [mulCode])
  have i6 : CodeAt P (a + 6) [.parity t₃] := by simpa [mulCode] using hcode.at_offset 6 (by simp [mulCode])
  have i7 : CodeAt P (a + 7) [.jz t₃ (a + 10)] := by simpa [mulCode] using hcode.at_offset 7 (by simp [mulCode])
  have i8 : CodeAt P (a + 8) [.copy t₁ t₃] := by simpa [mulCode] using hcode.at_offset 8 (by simp [mulCode])
  have i9 : CodeAt P (a + 9) [.add s t₃] := by simpa [mulCode] using hcode.at_offset 9 (by simp [mulCode])
  have i10 : CodeAt P (a + 10) [.double t₁] := by simpa [mulCode] using hcode.at_offset 10 (by simp [mulCode])
  have i11 : CodeAt P (a + 11) [.half t₂] := by simpa [mulCode] using hcode.at_offset 11 (by simp [mulCode])
  have i12 : CodeAt P (a + 12) [.jmp (a + 3)] := by simpa [mulCode] using hcode.at_offset 12 (by simp [mulCode])
  have i13 : CodeAt P (a + 13) [.pop t₁] := by simpa [mulCode] using hcode.at_offset 13 (by simp [mulCode])
  have i14 : CodeAt P (a + 14) [.pop t₂] := by simpa [mulCode] using hcode.at_offset 14 (by simp [mulCode])
  -- Setup: move y to t₁, x to t₂, push 0 on s.
  let c₁ : Config :=
    { cfg with pc := a + 1, stk := Function.update (Function.update cfg.stk s (x :: rest)) t₁ (y :: cfg.stk t₁) }
  have s0 : Steps P cfg c₁ (1 + len y) := Steps.move_ne hs1 i0 hpc hs
  have c₁s : c₁.stk s = x :: rest := by simp [c₁, hs1]
  have c₁t1 : c₁.stk t₁ = y :: cfg.stk t₁ := by simp [c₁]
  have c₁t2 : c₁.stk t₂ = cfg.stk t₂ := by simp [c₁, h12.symm, hs2.symm]
  have c₁t3 : c₁.stk t₃ = cfg.stk t₃ := by simp [c₁, h13.symm, hs3.symm]
  let c₂ : Config :=
    { c₁ with pc := a + 2, stk := Function.update (Function.update c₁.stk s rest) t₂ (x :: c₁.stk t₂) }
  have s1 : Steps P c₁ c₂ (1 + len x) := Steps.move_ne hs2 i1 rfl c₁s
  have c₂s : c₂.stk s = rest := by simp [c₂, hs2]
  have c₂t1 : c₂.stk t₁ = y :: cfg.stk t₁ := by simp [c₂, h12, hs1.symm, c₁t1]
  have c₂t2 : c₂.stk t₂ = x :: cfg.stk t₂ := by simp [c₂, c₁t2]
  have c₂t3 : c₂.stk t₃ = cfg.stk t₃ := by simp [c₂, h23.symm, hs3.symm, c₁t3]
  let c₃ : Config := { c₂ with pc := a + 3, stk := Function.update c₂.stk s (0 :: c₂.stk s) }
  have s2 : Steps P c₂ c₃ (1 + len 0) := Steps.push i2 rfl
  have c₃s : c₃.stk s = 0 :: rest := by simp [c₃, c₂s]
  have c₃t1 : c₃.stk t₁ = y :: cfg.stk t₁ := by simp [c₃, hs1.symm, c₂t1]
  have c₃t2 : c₃.stk t₂ = x :: cfg.stk t₂ := by simp [c₃, hs2.symm, c₂t2]
  have c₃t3 : c₃.stk t₃ = cfg.stk t₃ := by simp [c₃, hs3.symm, c₂t3]
  have hk_init : Keeps [s, t₁, t₂, t₃] cfg c₃ :=
    ((Keeps.update_stk₂_mem cfg (a + 1) (by simp) (by simp) _ _).trans
      (Keeps.update_stk₂_mem c₁ (a + 2) (by simp) (by simp) _ _)).trans
      (Keeps.update_stk_mem c₂ (a + 3) (by simp) _)
  -- Loop invariant and measure.
  let L := len x + len y
  let Inv : Config → Prop := fun c =>
    c.pc = a + 3 ∧ Keeps [s, t₁, t₂, t₃] cfg c ∧ c.stk t₃ = cfg.stk t₃ ∧
    ∃ acc b n, c.stk s = acc :: rest ∧ c.stk t₁ = b :: cfg.stk t₁ ∧ c.stk t₂ = n :: cfg.stk t₂ ∧
      acc + n * b = x * y ∧ len b + len n ≤ L
  let Done : Config → Prop := fun c =>
    c.pc = a + 15 ∧ c.stk s = (x * y) :: rest ∧ Keeps [s] cfg c
  let μ : Config → ℕ := fun c => len (c.stk t₂).head!
  have hloop : ∀ c, Inv c → ∃ c' S, Steps P c c' S ∧ Done c' ∧ S ≤ μ c * (14 + 9 * L) + (4 + L) := by
    refine Steps.loop Inv Done μ (14 + 9 * L) (4 + L) (fun c hInv => ?_)
    obtain ⟨hpc_c, hk_c, hct3, acc, b, n, hcs, hct1, hct2, heq, hlen⟩ := hInv
    have hacc_len : len acc ≤ L := by
      have h1 : acc ≤ x * y := by omega
      exact le_trans (GI.Machine.len_mono h1) (GI.Machine.len_mul_le x y)
    let d₁ : Config := { c with pc := a + 4, stk := Function.update c.stk t₃ (n :: c.stk t₃) }
    have st3 : Steps P c d₁ (1 + len n) := Steps.copy i3 hpc_c hct2
    have d₁s : d₁.stk s = acc :: rest := by simp [d₁, hs3, hcs]
    have d₁t1 : d₁.stk t₁ = b :: cfg.stk t₁ := by simp [d₁, h13, hct1]
    have d₁t2 : d₁.stk t₂ = n :: cfg.stk t₂ := by simp [d₁, h23, hct2]
    have d₁t3 : d₁.stk t₃ = n :: cfg.stk t₃ := by simp [d₁, hct3]
    by_cases hn : n = 0
    · -- Exit loop and clean up t₁, t₂.
      subst hn
      have hacc_eq : acc = x * y := by simpa using heq
      let d₂ : Config := { d₁ with pc := a + 13, stk := Function.update d₁.stk t₃ (cfg.stk t₃) }
      have st4 : Steps P d₁ d₂ 1 := Steps.jz_zero i4 rfl d₁t3
      have d₂t1 : d₂.stk t₁ = b :: cfg.stk t₁ := by simp [d₂, h13, d₁t1]
      have d₂t2 : d₂.stk t₂ = 0 :: cfg.stk t₂ := by simp [d₂, h23, d₁t2]
      let d₃ : Config := { d₂ with pc := a + 14, stk := Function.update d₂.stk t₁ (cfg.stk t₁) }
      have st13 : Steps P d₂ d₃ (1 + len b) := Steps.pop i13 rfl d₂t1
      have d₃t2 : d₃.stk t₂ = 0 :: cfg.stk t₂ := by simp [d₃, h12.symm, d₂t2]
      let d₄ : Config := { d₃ with pc := a + 15, stk := Function.update d₃.stk t₂ (cfg.stk t₂) }
      have st14 : Steps P d₃ d₄ (1 + len 0) := Steps.pop i14 rfl d₃t2
      have hk_step : Keeps [s, t₁, t₂, t₃] c d₄ :=
        (((Keeps.update_stk_mem c (a + 4) (by simp) _).trans
          (Keeps.update_stk_mem d₁ (a + 13) (by simp) _)).trans
          (Keeps.update_stk_mem d₂ (a + 14) (by simp) _)).trans
          (Keeps.update_stk_mem d₃ (a + 15) (by simp) _)
      have hd₄s : d₄.stk s = (x * y) :: rest := by simp [d₄, d₃, d₂, hs2, hs1, hs3, d₁s, hacc_eq]
      have hd₄t1 : d₄.stk t₁ = cfg.stk t₁ := by simp [d₄, d₃, h12]
      have hd₄t2 : d₄.stk t₂ = cfg.stk t₂ := by simp [d₄]
      have hd₄t3 : d₄.stk t₃ = cfg.stk t₃ := by simp [d₄, d₃, d₂, h23.symm, h13.symm]
      have hkeeps : Keeps [s] cfg d₄ := (hk_c.trans hk_step).of_subset_eq fun w hw hnot => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hnot
        rcases hw with rfl | rfl | rfl | rfl
        · exact absurd rfl hnot
        · exact hd₄t1
        · exact hd₄t2
        · exact hd₄t3
      refine Or.inl ⟨d₄, _, ((st3.trans st4).trans st13).trans st14, ⟨rfl, hd₄s, hkeeps⟩, ?_⟩
      simp only [GI.Machine.len_zero] at hlen ⊢
      omega
    · -- Loop body: n ≠ 0.
      let d₂ : Config := { d₁ with pc := a + 5, stk := Function.update d₁.stk t₃ (cfg.stk t₃) }
      have st4 : Steps P d₁ d₂ (1 + len n) := Steps.jz_ne_zero i4 rfl d₁t3 hn
      have d₂s : d₂.stk s = acc :: rest := by simp [d₂, hs3, d₁s]
      have d₂t1 : d₂.stk t₁ = b :: cfg.stk t₁ := by simp [d₂, h13, d₁t1]
      have d₂t2 : d₂.stk t₂ = n :: cfg.stk t₂ := by simp [d₂, h23, d₁t2]
      have d₂t3 : d₂.stk t₃ = cfg.stk t₃ := by simp [d₂]
      let d₃ : Config := { d₂ with pc := a + 6, stk := Function.update d₂.stk t₃ (n :: d₂.stk t₃) }
      have st5 : Steps P d₂ d₃ (1 + len n) := Steps.copy i5 rfl d₂t2
      have d₃t3 : d₃.stk t₃ = n :: cfg.stk t₃ := by simp [d₃, d₂t3]
      let d₄ : Config := { d₃ with pc := a + 7, stk := Function.update d₃.stk t₃ ((n % 2) :: cfg.stk t₃) }
      have st6 : Steps P d₃ d₄ (1 + len n) := Steps.parity i6 rfl d₃t3
      have d₄s : d₄.stk s = acc :: rest := by simp [d₄, d₃, hs3, d₂s]
      have d₄t1 : d₄.stk t₁ = b :: cfg.stk t₁ := by simp [d₄, d₃, h13, d₂t1]
      have d₄t2 : d₄.stk t₂ = n :: cfg.stk t₂ := by simp [d₄, d₃, h23, d₂t2]
      have d₄t3 : d₄.stk t₃ = (n % 2) :: cfg.stk t₃ := by simp [d₄]
      have hk_pre : Keeps [s, t₁, t₂, t₃] c d₄ :=
        (((Keeps.update_stk_mem c (a + 4) (by simp) _).trans
          (Keeps.update_stk_mem d₁ (a + 5) (by simp) _)).trans
          (Keeps.update_stk_mem d₂ (a + 6) (by simp) _)).trans
          (Keeps.update_stk_mem d₃ (a + 7) (by simp) _)
      -- Run the parity branch to reach pc = a + 10 with acc' = acc + (n % 2) * b.
      have hbranch : ∃ d₇ S_br, Steps P d₄ d₇ S_br ∧ d₇.pc = a + 10 ∧
          Keeps [s, t₁, t₂, t₃] d₄ d₇ ∧
          d₇.stk s = (acc + (n % 2) * b) :: rest ∧
          d₇.stk t₁ = b :: cfg.stk t₁ ∧
          d₇.stk t₂ = n :: cfg.stk t₂ ∧
          d₇.stk t₃ = cfg.stk t₃ ∧
          S_br ≤ 4 + 3 * L := by
        by_cases hpar : n % 2 = 0
        · let d₅ : Config := { d₄ with pc := a + 10, stk := Function.update d₄.stk t₃ (cfg.stk t₃) }
          have st7 : Steps P d₄ d₅ 1 := Steps.jz_zero i7 rfl (by rw [d₄t3, hpar])
          refine ⟨d₅, 1, st7, rfl, Keeps.update_stk_mem d₄ (a + 10) (by simp) _,
            by simp [d₅, hs3, d₄s, hpar], by simp [d₅, h13, d₄t1], by simp [d₅, h23, d₄t2],
            by simp [d₅], by omega⟩
        · have hpar1 : n % 2 = 1 := by omega
          let d₅ : Config := { d₄ with pc := a + 8, stk := Function.update d₄.stk t₃ (cfg.stk t₃) }
          have st7 : Steps P d₄ d₅ (1 + len (n % 2)) := Steps.jz_ne_zero i7 rfl d₄t3 hpar
          have d₅s : d₅.stk s = acc :: rest := by simp [d₅, hs3, d₄s]
          have d₅t1 : d₅.stk t₁ = b :: cfg.stk t₁ := by simp [d₅, h13, d₄t1]
          have d₅t2 : d₅.stk t₂ = n :: cfg.stk t₂ := by simp [d₅, h23, d₄t2]
          have d₅t3 : d₅.stk t₃ = cfg.stk t₃ := by simp [d₅]
          let d₆ : Config := { d₅ with pc := a + 9, stk := Function.update d₅.stk t₃ (b :: d₅.stk t₃) }
          have st8 : Steps P d₅ d₆ (1 + len b) := Steps.copy i8 rfl d₅t1
          have d₆s : d₆.stk s = acc :: rest := by simp [d₆, hs3, d₅s]
          have d₆t3 : d₆.stk t₃ = b :: cfg.stk t₃ := by simp [d₆, d₅t3]
          let d₇ : Config :=
            { d₆ with pc := a + 10, stk := Function.update (Function.update d₆.stk t₃ (cfg.stk t₃)) s ((acc + b) :: rest) }
          have st9 : Steps P d₆ d₇ (1 + len acc + len b) := Steps.add hs3 i9 rfl d₆s d₆t3
          have hk_b : Keeps [s, t₁, t₂, t₃] d₄ d₇ :=
            ((Keeps.update_stk_mem d₄ (a + 8) (by simp) _).trans
              (Keeps.update_stk_mem d₅ (a + 9) (by simp) _)).trans
              (Keeps.update_stk₂_mem d₆ (a + 10) (by simp) (by simp) _ _)
          refine ⟨d₇, _, (st7.trans st8).trans st9, rfl, hk_b,
            by simp [d₇, hpar1], by simp [d₇, d₆, hs1.symm, h13, d₅t1],
            by simp [d₇, d₆, hs2.symm, h23, d₅t2], by simp [d₇, hs3.symm], ?_⟩
          have : len (n % 2) ≤ 1 := len_mod_two_le n
          omega
      obtain ⟨d₇, S_br, st_br, hd₇pc, hk_br, hd₇s, hd₇t1, hd₇t2, hd₇t3, hS_br⟩ := hbranch
      let d₈ : Config := { d₇ with pc := a + 11, stk := Function.update d₇.stk t₁ ((2 * b) :: cfg.stk t₁) }
      have st10 : Steps P d₇ d₈ (1 + len b) := Steps.double i10 hd₇pc hd₇t1
      have d₈t2 : d₈.stk t₂ = n :: cfg.stk t₂ := by simp [d₈, h12.symm, hd₇t2]
      let d₉ : Config := { d₈ with pc := a + 12, stk := Function.update d₈.stk t₂ ((n / 2) :: cfg.stk t₂) }
      have st11 : Steps P d₈ d₉ (1 + len n) := Steps.half i11 rfl d₈t2
      let d₁₀ : Config := { d₉ with pc := a + 3 }
      have st12 : Steps P d₉ d₁₀ 1 := Steps.jmp i12 rfl
      have hk_post : Keeps [s, t₁, t₂, t₃] d₇ d₁₀ :=
        ((Keeps.update_stk_mem d₇ (a + 11) (by simp) _).trans
          (Keeps.update_stk_mem d₈ (a + 12) (by simp) _)).trans
          (Keeps.with_pc_mem [s, t₁, t₂, t₃] d₉ (a + 3))
      have hlen_new : len (2 * b) + len (n / 2) ≤ L := by
        have h1 := len_two_mul_le b
        have h2 := len_div_two_add_one hn
        omega
      have heq_new : acc + n % 2 * b + n / 2 * (2 * b) = x * y := by
        have hdiv : 2 * (n / 2) + n % 2 = n := Nat.div_add_mod n 2
        calc acc + n % 2 * b + n / 2 * (2 * b)
            = acc + (2 * (n / 2) + n % 2) * b := by ring
          _ = acc + n * b := by rw [hdiv]
          _ = x * y := heq
      have hInv_new : Inv d₁₀ := by
        refine ⟨rfl, ((hk_c.trans hk_pre).trans hk_br).trans hk_post,
          by simp [d₁₀, d₉, d₈, h23.symm, h13.symm, hd₇t3],
          acc + n % 2 * b, 2 * b, n / 2,
          by simp [d₁₀, d₉, d₈, hs2, hs1, hd₇s],
          by simp [d₁₀, d₉, d₈, h12],
          by simp [d₁₀, d₉], heq_new, hlen_new⟩
      have hμ_lt : μ d₁₀ < μ c := by
        simp only [μ, d₁₀, d₉, Function.update_self, hct2, List.head!_cons]
        exact len_div_two_lt hn
      refine Or.inr ⟨d₁₀, _, (((((st3.trans st4).trans st5).trans st6).trans st_br).trans st10).trans (st11.trans st12),
        hInv_new, hμ_lt, ?_⟩
      omega
  have hInv0 : Inv c₃ :=
    ⟨rfl, hk_init, c₃t3, 0, y, x, c₃s, c₃t1, c₃t2, by simp, by simp [L]; omega⟩
  obtain ⟨c', S_loop, hsteps_loop, ⟨hpc', hs', hk'⟩, hS_loop⟩ := hloop c₃ hInv0
  have hμ0 : μ c₃ = len x := by simp [μ, c₃t2]
  rw [hμ0] at hS_loop
  refine ⟨c', _, ((s0.trans s1).trans s2).trans hsteps_loop, ?_, hs', hk', ?_⟩
  · simp [hpc', mulCode]
  · simp only [GI.Machine.len_zero]
    have hLdef : L = len x + len y := rfl
    have hL : len x ≤ L := Nat.le_add_right _ _
    have h1 : len x * (14 + 9 * L) ≤ L * (14 + 9 * L) := Nat.mul_le_mul_right _ hL
    nlinarith

end GI.Turing
