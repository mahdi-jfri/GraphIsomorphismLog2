/-
General lemmas for reasoning about runs of the stack machine of `Workspace.Turing.SM`.

This file provides:
* one step lemma for each instruction of `GI.Turing.SM.Instr`, under `CodeAt P a [i]`,
* sequencing lemmas for composing runs of appended code blocks,
* two loop rules (`Steps.loop_potential` and `Steps.loop`) proved by strong induction on a
  termination measure,
* algebraic facts about `GI.Turing.Keeps`, including composition and restoring scratch stacks,
* basic lemmas about `GI.Turing.listSize`, `GI.Turing.memOf`, `GI.Machine.len`, and picking
  distinct scratch stacks in `Fin 8`.
-/
module

public import Workspace.Turing.Interface
public import Workspace.Machine.Len

@[expose] public section

namespace GI.Turing

open GI.Machine (len)
open GI.Turing.SM

/-! ### `CodeAt` helpers -/

namespace SM.CodeAt

variable {P : Program} {a : ℕ}

/-- `CodeAt P a [i]` is the same as `P[a]? = some i`. -/
theorem singleton_iff {i : Instr} : CodeAt P a [i] ↔ P[a]? = some i := by
  constructor
  · intro h
    exact h.cons
  · intro h j hj
    have hj0 : j = 0 := by simp at hj; omega
    subst hj0
    simpa using h

/-- Extract the single instruction at offset `k` from a `CodeAt` block. -/
theorem at_offset {code : List Instr} (h : CodeAt P a code) (k : ℕ) (hk : k < code.length) :
    CodeAt P (a + k) [code[k]] :=
  singleton_iff.mpr (h k hk)

/-- Extract the first instruction as a singleton `CodeAt`. -/
theorem head_singleton {i : Instr} {code : List Instr} (h : CodeAt P a (i :: code)) :
    CodeAt P a [i] :=
  singleton_iff.mpr h.cons

end SM.CodeAt

/-! ### `Keeps` lemmas -/

namespace Keeps

theorem refl (ss : List Stk) (c : Config) : Keeps ss c c :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem symm {ss : List Stk} {c c' : Config} (h : Keeps ss c c') : Keeps ss c' c :=
  ⟨fun t ht => (h.1 t ht).symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩

theorem trans {ss : List Stk} {c₁ c₂ c₃ : Config} (h₁ : Keeps ss c₁ c₂) (h₂ : Keeps ss c₂ c₃) :
    Keeps ss c₁ c₃ :=
  ⟨fun t ht => (h₂.1 t ht).trans (h₁.1 t ht), h₂.2.1.trans h₁.2.1,
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem stk_eq {ss : List Stk} {c c' : Config} (h : Keeps ss c c') {t : Stk} (ht : t ∉ ss) :
    c'.stk t = c.stk t :=
  h.1 t ht

theorem rs_eq {ss : List Stk} {c c' : Config} (h : Keeps ss c c') : c'.rs = c.rs := h.2.1
theorem inp_eq {ss : List Stk} {c c' : Config} (h : Keeps ss c c') : c'.inp = c.inp := h.2.2.1
theorem out_eq {ss : List Stk} {c c' : Config} (h : Keeps ss c c') : c'.out = c.out := h.2.2.2

theorem mono {s₁ s₂ : List Stk} {c c' : Config} (hsub : ∀ t, t ∈ s₁ → t ∈ s₂)
    (h : Keeps s₁ c c') : Keeps s₂ c c' :=
  ⟨fun t ht => h.1 t fun hmem => ht (hsub t hmem), h.2.1, h.2.2.1, h.2.2.2⟩

theorem trans_union {s₁ s₂ : List Stk} {c₁ c₂ c₃ : Config}
    (h₁ : Keeps s₁ c₁ c₂) (h₂ : Keeps s₂ c₂ c₃) : Keeps (s₁ ++ s₂) c₁ c₃ :=
  (h₁.mono fun _ ht => List.mem_append_left s₂ ht).trans
    (h₂.mono fun _ ht => List.mem_append_right s₁ ht)

/-- Narrow the set of modified stacks when every dropped stack has returned to its original
contents. -/
theorem of_subset_eq {s₁ s₂ : List Stk} {c c' : Config} (h : Keeps s₁ c c')
    (heq : ∀ t, t ∈ s₁ → t ∉ s₂ → c'.stk t = c.stk t) : Keeps s₂ c c' := by
  refine ⟨fun t ht => ?_, h.2.1, h.2.2.1, h.2.2.2⟩
  by_cases hmem : t ∈ s₁
  · exact heq t hmem ht
  · exact h.1 t hmem

/-- Remove a stack from the head of the modified list once it is restored. -/
theorem shrink {s : Stk} {ss : List Stk} {c c' : Config} (h : Keeps (s :: ss) c c')
    (hs : c'.stk s = c.stk s) : Keeps ss c c' :=
  h.of_subset_eq fun t ht hnot => by
    simp only [List.mem_cons] at ht
    rcases ht with rfl | hmem
    · exact hs
    · exact absurd hmem hnot

/-- Pushing a value onto a scratch stack `t`, running code that leaves `t` with that value on top,
and popping `t` restores `t` and keeps all stacks outside `ss`. -/
theorem push_pop {t : Stk} {ss : List Stk} {c c₁ c₂ c₃ : Config} {v : ℕ}
    (h₁ : Keeps (t :: ss) c c₁)
    (h₂ : Keeps (t :: ss) c₁ c₂)
    (h₃ : Keeps (t :: ss) c₂ c₃)
    (ht₂ : c₂.stk t = v :: c.stk t)
    (ht₃ : c₃.stk t = (c₂.stk t).tail) :
    Keeps ss c c₃ := by
  have hall : Keeps (t :: ss) c c₃ := (h₁.trans h₂).trans h₃
  refine hall.shrink ?_
  rw [ht₃, ht₂]
  rfl

/-- Changing only `pc` keeps every stack, the return stack, the input and the output. -/
theorem with_pc (c : Config) (p : ℕ) : Keeps [] c { c with pc := p } :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- Changing only `pc` satisfies `Keeps ss` for any list `ss`. -/
theorem with_pc_mem (ss : List Stk) (c : Config) (p : ℕ) : Keeps ss c { c with pc := p } :=
  ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

/-- Changing `pc` and updating one stack `s` keeps all stacks outside `[s]`. -/
theorem update_stk (c : Config) (p : ℕ) (s : Stk) (l : List ℕ) :
    Keeps [s] c { c with pc := p, stk := Function.update c.stk s l } := by
  refine ⟨fun t ht => ?_, rfl, rfl, rfl⟩
  have hne : t ≠ s := by simpa using ht
  exact Function.update_of_ne hne l c.stk

/-- Changing `pc` and updating one stack `s ∈ ss` keeps all stacks outside `ss`. -/
theorem update_stk_mem {ss : List Stk} (c : Config) (p : ℕ) {s : Stk} (hs : s ∈ ss) (l : List ℕ) :
    Keeps ss c { c with pc := p, stk := Function.update c.stk s l } :=
  (update_stk c p s l).mono fun _ h => by simp only [List.mem_singleton] at h; exact h ▸ hs

/-- Changing `pc` and updating two stacks `s` and `t` keeps all stacks outside `[s, t]`. -/
theorem update_stk₂ (c : Config) (p : ℕ) (s t : Stk) (l₁ l₂ : List ℕ) :
    Keeps [s, t] c
      { c with pc := p, stk := Function.update (Function.update c.stk t l₂) s l₁ } := by
  refine ⟨fun u hu => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hu
  dsimp only
  rw [Function.update_of_ne hu.1, Function.update_of_ne hu.2]

/-- Changing `pc` and updating two stacks `s, t ∈ ss` keeps all stacks outside `ss`. -/
theorem update_stk₂_mem {ss : List Stk} (c : Config) (p : ℕ) {s t : Stk}
    (hs : s ∈ ss) (ht : t ∈ ss) (l₁ l₂ : List ℕ) :
    Keeps ss c
      { c with pc := p, stk := Function.update (Function.update c.stk t l₂) s l₁ } :=
  (update_stk₂ c p s t l₁ l₂).mono fun _ h => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> assumption

end Keeps

/-! ### Single-instruction step lemmas -/

namespace SM.Steps

variable {P : Program} {a : ℕ} {c : Config}

theorem push {s : Stk} {k : ℕ} (hP : CodeAt P a [.push s k]) (hpc : c.pc = a) :
    Steps P c { c with pc := a + 1, stk := Function.update c.stk s (k :: c.stk s) } (1 + len k) := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc]

theorem pop {s : Stk} {v : ℕ} {r : List ℕ} (hP : CodeAt P a [.pop s]) (hpc : c.pc = a)
    (hs : c.stk s = v :: r) :
    Steps P c { c with pc := a + 1, stk := Function.update c.stk s r } (1 + len v) := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc, hs]

theorem copy {s t : Stk} {v : ℕ} {r : List ℕ} (hP : CodeAt P a [.copy s t]) (hpc : c.pc = a)
    (hs : c.stk s = v :: r) :
    Steps P c { c with pc := a + 1, stk := Function.update c.stk t (v :: c.stk t) } (1 + len v) := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc, hs]

theorem move {s t : Stk} {v : ℕ} {r : List ℕ} (hP : CodeAt P a [.move s t]) (hpc : c.pc = a)
    (hs : c.stk s = v :: r) :
    Steps P c
      { c with
        pc := a + 1
        stk :=
          let st := Function.update c.stk s r
          Function.update st t (v :: st t) }
      (1 + len v) := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc, hs]

theorem move_ne {s t : Stk} (hne : s ≠ t) {v : ℕ} {r : List ℕ}
    (hP : CodeAt P a [.move s t]) (hpc : c.pc = a) (hs : c.stk s = v :: r) :
    Steps P c
      { c with
        pc := a + 1
        stk := Function.update (Function.update c.stk s r) t (v :: c.stk t) }
      (1 + len v) := by
  have h := Steps.move hP hpc hs
  simpa [Function.update_of_ne hne.symm] using h

theorem add {s t : Stk} (hne : s ≠ t) {x y : ℕ} {r r' : List ℕ}
    (hP : CodeAt P a [.add s t]) (hpc : c.pc = a)
    (hs : c.stk s = x :: r) (ht : c.stk t = y :: r') :
    Steps P c
      { c with
        pc := a + 1
        stk := Function.update (Function.update c.stk t r') s ((x + y) :: r) }
      (1 + len x + len y) := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc, hne, hs, ht]

theorem sub {s t : Stk} (hne : s ≠ t) {x y : ℕ} {r r' : List ℕ}
    (hP : CodeAt P a [.sub s t]) (hpc : c.pc = a)
    (hs : c.stk s = x :: r) (ht : c.stk t = y :: r') :
    Steps P c
      { c with
        pc := a + 1
        stk := Function.update (Function.update c.stk t r') s ((x - y) :: r) }
      (1 + len x + len y) := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc, hne, hs, ht]

theorem double {s : Stk} {v : ℕ} {r : List ℕ} (hP : CodeAt P a [.double s]) (hpc : c.pc = a)
    (hs : c.stk s = v :: r) :
    Steps P c { c with pc := a + 1, stk := Function.update c.stk s (2 * v :: r) } (1 + len v) := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc, hs]

theorem half {s : Stk} {v : ℕ} {r : List ℕ} (hP : CodeAt P a [.half s]) (hpc : c.pc = a)
    (hs : c.stk s = v :: r) :
    Steps P c { c with pc := a + 1, stk := Function.update c.stk s (v / 2 :: r) } (1 + len v) := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc, hs]

theorem parity {s : Stk} {v : ℕ} {r : List ℕ} (hP : CodeAt P a [.parity s]) (hpc : c.pc = a)
    (hs : c.stk s = v :: r) :
    Steps P c { c with pc := a + 1, stk := Function.update c.stk s (v % 2 :: r) } (1 + len v) := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc, hs]

theorem jz {s : Stk} {l v : ℕ} {r : List ℕ} (hP : CodeAt P a [.jz s l]) (hpc : c.pc = a)
    (hs : c.stk s = v :: r) :
    Steps P c
      { c with pc := if v = 0 then l else a + 1, stk := Function.update c.stk s r }
      (1 + len v) := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc, hs]

theorem jz_zero {s : Stk} {l : ℕ} {r : List ℕ} (hP : CodeAt P a [.jz s l]) (hpc : c.pc = a)
    (hs : c.stk s = 0 :: r) :
    Steps P c { c with pc := l, stk := Function.update c.stk s r } 1 := by
  simpa [GI.Machine.len_zero] using Steps.jz hP hpc hs

theorem jz_ne_zero {s : Stk} {l v : ℕ} {r : List ℕ} (hP : CodeAt P a [.jz s l]) (hpc : c.pc = a)
    (hs : c.stk s = v :: r) (hv : v ≠ 0) :
    Steps P c { c with pc := a + 1, stk := Function.update c.stk s r } (1 + len v) := by
  simpa [hv] using Steps.jz hP hpc hs

theorem jmp {l : ℕ} (hP : CodeAt P a [.jmp l]) (hpc : c.pc = a) :
    Steps P c { c with pc := l } 1 := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1]

theorem jnil {s : Stk} {l : ℕ} (hP : CodeAt P a [.jnil s l]) (hpc : c.pc = a) :
    Steps P c { c with pc := if c.stk s = [] then l else a + 1 } 1 := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc]

theorem jnil_nil {s : Stk} {l : ℕ} (hP : CodeAt P a [.jnil s l]) (hpc : c.pc = a)
    (hs : c.stk s = []) :
    Steps P c { c with pc := l } 1 := by
  simpa [hs] using Steps.jnil hP hpc

theorem jnil_cons {s : Stk} {l v : ℕ} {r : List ℕ} (hP : CodeAt P a [.jnil s l]) (hpc : c.pc = a)
    (hs : c.stk s = v :: r) :
    Steps P c { c with pc := a + 1 } 1 := by
  simpa [hs] using Steps.jnil hP hpc

theorem call {l : ℕ} (hP : CodeAt P a [.call l]) (hpc : c.pc = a) :
    Steps P c { c with pc := l, rs := (a + 1) :: c.rs } 1 := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc]

theorem ret {r : ℕ} {rs : List ℕ} (hP : CodeAt P a [.ret]) (hpc : c.pc = a)
    (hrs : c.rs = r :: rs) :
    Steps P c { c with pc := r, rs := rs } 1 := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hrs]

theorem read_cons {s : Stk} {b : Bool} {x : List Bool} (hP : CodeAt P a [.read s]) (hpc : c.pc = a)
    (hinp : c.inp = b :: x) :
    Steps P c
      { c with
        pc := a + 1
        stk := Function.update c.stk s ((if b then 1 else 0) :: c.stk s)
        inp := x }
      1 := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc, hinp]

theorem read_nil {s : Stk} (hP : CodeAt P a [.read s]) (hpc : c.pc = a) (hinp : c.inp = []) :
    Steps P c { c with pc := a + 1, stk := Function.update c.stk s (2 :: c.stk s) } 1 := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc, hinp]

theorem write {s : Stk} {v : ℕ} {r : List ℕ} (hP : CodeAt P a [.write s]) (hpc : c.pc = a)
    (hs : c.stk s = v :: r) :
    Steps P c
      { c with
        pc := a + 1
        stk := Function.update c.stk s r
        out := c.out ++ [decide (v ≠ 0)] }
      (1 + len v) := by
  apply Steps.single
  rw [step_eq (hpc ▸ hP.cons)]
  simp [exec1, hpc, hs]

/-! ### Sequencing and loop rules -/

/-- Run two consecutive pieces of code `c₁` and `c₂`, adding their cost bounds. -/
theorem seq_code {a : ℕ} {c₁ c₂ : List Instr} {cfg : Config}
    {Q₁ Q₂ : Config → Prop} {B₁ B₂ : ℕ}
    (hcode : CodeAt P a (c₁ ++ c₂))
    (h₁ : CodeAt P a c₁ →
      ∃ cfg₁ S₁, Steps P cfg cfg₁ S₁ ∧ cfg₁.pc = a + c₁.length ∧ Q₁ cfg₁ ∧ S₁ ≤ B₁)
    (h₂ : ∀ cfg₁, cfg₁.pc = a + c₁.length → Q₁ cfg₁ → CodeAt P (a + c₁.length) c₂ →
      ∃ cfg₂ S₂, Steps P cfg₁ cfg₂ S₂ ∧ cfg₂.pc = a + c₁.length + c₂.length ∧ Q₂ cfg₂ ∧ S₂ ≤ B₂) :
    ∃ cfg₂ S, Steps P cfg cfg₂ S ∧ cfg₂.pc = a + (c₁ ++ c₂).length ∧ Q₂ cfg₂ ∧ S ≤ B₁ + B₂ := by
  obtain ⟨cfg₁, S₁, hs₁, hpc₁, hq₁, hle₁⟩ := h₁ hcode.append_left
  obtain ⟨cfg₂, S₂, hs₂, hpc₂, hq₂, hle₂⟩ := h₂ cfg₁ hpc₁ hq₁ hcode.append_right
  refine ⟨cfg₂, S₁ + S₂, hs₁.trans hs₂, ?_, hq₂, Nat.add_le_add hle₁ hle₂⟩
  simp only [List.length_append]
  omega

/-- Chain two existential runs with cost bounds. -/
theorem bind {c₁ : Config} {Q₁ Q₂ : Config → Prop} {B₁ B₂ : ℕ}
    (h₁ : ∃ c₂ S₁, Steps P c₁ c₂ S₁ ∧ Q₁ c₂ ∧ S₁ ≤ B₁)
    (h₂ : ∀ c₂, Q₁ c₂ → ∃ c₃ S₂, Steps P c₂ c₃ S₂ ∧ Q₂ c₃ ∧ S₂ ≤ B₂) :
    ∃ c₃ S, Steps P c₁ c₃ S ∧ Q₂ c₃ ∧ S ≤ B₁ + B₂ := by
  obtain ⟨c₂, S₁, hs₁, hq₁, hle₁⟩ := h₁
  obtain ⟨c₃, S₂, hs₂, hq₂, hle₂⟩ := h₂ c₂ hq₁
  exact ⟨c₃, S₁ + S₂, hs₁.trans hs₂, hq₂, Nat.add_le_add hle₁ hle₂⟩

/-- General loop rule with a termination measure `μ` and a remaining-cost potential `Φ`.
At every state satisfying `Inv`, the loop either reaches `Done` at cost at most `Φ c`, or steps to
another state satisfying `Inv` with strictly smaller `μ` and total cost plus new potential at most
`Φ c`. -/
theorem loop_potential (Inv Done : Config → Prop) (μ Φ : Config → ℕ)
    (hstep : ∀ c, Inv c →
      (∃ c' S, Steps P c c' S ∧ Done c' ∧ S ≤ Φ c) ∨
      (∃ c' S, Steps P c c' S ∧ Inv c' ∧ μ c' < μ c ∧ S + Φ c' ≤ Φ c)) :
    ∀ c, Inv c → ∃ c' S, Steps P c c' S ∧ Done c' ∧ S ≤ Φ c := by
  suffices h : ∀ n c, μ c = n → Inv c → ∃ c' S, Steps P c c' S ∧ Done c' ∧ S ≤ Φ c from
    fun c hc => h (μ c) c rfl hc
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro c hμ hInv
    rcases hstep c hInv with hexit | ⟨c₁, S₁, hs₁, hInv₁, hlt, hΦ⟩
    · exact hexit
    · obtain ⟨c₂, S₂, hs₂, hDone, hle₂⟩ := ih (μ c₁) (hμ ▸ hlt) c₁ rfl hInv₁
      exact ⟨c₂, S₁ + S₂, hs₁.trans hs₂, hDone, by omega⟩

/-- Loop rule with a uniform cost bound `stepCost` per iteration and `exitCost` on exit. -/
theorem loop (Inv Done : Config → Prop) (μ : Config → ℕ) (stepCost exitCost : ℕ)
    (hstep : ∀ c, Inv c →
      (∃ c' S, Steps P c c' S ∧ Done c' ∧ S ≤ exitCost) ∨
      (∃ c' S, Steps P c c' S ∧ Inv c' ∧ μ c' < μ c ∧ S ≤ stepCost)) :
    ∀ c, Inv c → ∃ c' S, Steps P c c' S ∧ Done c' ∧ S ≤ μ c * stepCost + exitCost := by
  refine loop_potential Inv Done μ (fun c => μ c * stepCost + exitCost) (fun c hInv => ?_)
  rcases hstep c hInv with ⟨c', S, hs, hd, hle⟩ | ⟨c', S, hs, hI, hlt, hle⟩
  · exact Or.inl ⟨c', S, hs, hd, by omega⟩
  · refine Or.inr ⟨c', S, hs, hI, hlt, ?_⟩
    have hmul : (μ c' + 1) * stepCost ≤ μ c * stepCost :=
      Nat.mul_le_mul_right stepCost hlt
    rw [Nat.add_one_mul] at hmul
    omega

end SM.Steps

/-! ### `len`, `listSize` and `memOf` lemmas -/

theorem len_two_mul_le (v : ℕ) : len (2 * v) ≤ len v + 1 := by
  rw [GI.Machine.len_le_iff, pow_succ']
  have hv := GI.Machine.lt_two_pow_len v
  omega

theorem len_two_mul_add_bit_le {v b : ℕ} (hb : b ≤ 1) : len (2 * v + b) ≤ len v + 1 := by
  rw [GI.Machine.len_le_iff, pow_succ']
  have hv := GI.Machine.lt_two_pow_len v
  omega

theorem len_div_two_add_one {v : ℕ} (hv : v ≠ 0) : len (v / 2) + 1 = len v := by
  have hle : len (v / 2) + 1 ≤ len v := by
    by_contra h
    have h1 : len v ≤ len (v / 2) := by omega
    have h2 : v < 2 ^ len (v / 2) := GI.Machine.len_le_iff.mp h1
    by_cases hdv : v / 2 = 0
    · rw [hdv, GI.Machine.len_zero] at h2; omega
    · have h3 : 2 ^ (len (v / 2) - 1) ≤ v / 2 := GI.Machine.two_pow_len_sub_one_le hdv
      have h4 : 2 * 2 ^ (len (v / 2) - 1) = 2 ^ len (v / 2) := by
        have hpos : 1 ≤ len (v / 2) := Nat.succ_le_of_lt (GI.Machine.len_pos.mpr (Nat.pos_of_ne_zero hdv))
        calc 2 * 2 ^ (len (v / 2) - 1) = 2 ^ (len (v / 2) - 1 + 1) := by rw [pow_succ']
          _ = 2 ^ len (v / 2) := by rw [Nat.sub_add_cancel hpos]
      omega
  have hge : len v ≤ len (v / 2) + 1 := by
    rw [GI.Machine.len_le_iff, pow_succ']
    have hdv := GI.Machine.lt_two_pow_len (v / 2)
    omega
  omega

theorem len_div_two_lt {v : ℕ} (hv : v ≠ 0) : len (v / 2) < len v := by
  have := len_div_two_add_one hv; omega

theorem len_mod_two_le (v : ℕ) : len (v % 2) ≤ 1 :=
  GI.Machine.len_le_one_iff.mpr (by omega)

@[simp] theorem listSize_nil : listSize [] = 0 := rfl

@[simp] theorem listSize_cons (v : ℕ) (l : List ℕ) :
    listSize (v :: l) = len v + 1 + listSize l := rfl

theorem listSize_append (l₁ l₂ : List ℕ) :
    listSize (l₁ ++ l₂) = listSize l₁ + listSize l₂ := by
  simp [listSize]

theorem listSize_reverse (l : List ℕ) : listSize l.reverse = listSize l := by
  simp [listSize]

theorem length_le_listSize (l : List ℕ) : l.length ≤ listSize l := by
  induction l with
  | nil => simp
  | cons v r ih => simp only [List.length_cons, listSize_cons]; omega

theorem len_add_one_le_listSize_of_mem {v : ℕ} {l : List ℕ} (h : v ∈ l) :
    len v + 1 ≤ listSize l := by
  induction l with
  | nil => simp at h
  | cons a r ih =>
    simp only [List.mem_cons] at h
    simp only [listSize_cons]
    rcases h with rfl | hr
    · omega
    · have := ih hr; omega

@[simp] theorem memOf_nil (x : ℕ) : memOf [] x = 0 := rfl

@[simp] theorem memOf_singleton (a x : ℕ) : memOf [a] x = 0 := rfl

@[simp] theorem memOf_cons_cons (a v : ℕ) (rest : List ℕ) (x : ℕ) :
    memOf (a :: v :: rest) x = if a = x then v else memOf rest x := rfl

theorem len_memOf_le_listSize (l : List ℕ) (x : ℕ) : len (memOf l x) ≤ listSize l := by
  match l with
  | [] => simp [GI.Machine.len_zero]
  | [_] => simp [GI.Machine.len_zero]
  | a :: v :: rest =>
    simp only [memOf_cons_cons, listSize_cons]
    split_ifs
    · omega
    · have := len_memOf_le_listSize rest x; omega

/-! ### Picking distinct scratch stacks -/

/-- The `k`-th stack after `s` modulo 8. For `k ∈ {1, …, 7}`, these are all distinct from `s`
and from one another. -/
def scratch (s : Stk) (k : Stk) : Stk := s + k

theorem scratch_ne_self (s : Stk) {k : Stk} (hk : k ≠ 0) : scratch s k ≠ s := by
  intro h
  have : k = 0 := by simpa [scratch] using h
  exact hk this

theorem scratch_ne {s k₁ k₂ : Stk} (hne : k₁ ≠ k₂) : scratch s k₁ ≠ scratch s k₂ := by
  intro h
  have : k₁ = k₂ := by simpa [scratch] using h
  exact hne this

/-- The list of all eight stacks in order. -/
def allStks : List Stk := [0, 1, 2, 3, 4, 5, 6, 7]

/-- Pick the `k`-th stack (for `k < 6`) that is neither `s` nor `m`. -/
def scratch2 (s m : Stk) (k : Fin 6) : Stk :=
  (allStks.filter fun t => decide (t ≠ s ∧ t ≠ m)).getD k.val 0

theorem scratch2_ne_left (s m : Stk) (h : s ≠ m) (k : Fin 6) : scratch2 s m k ≠ s := by
  revert s m h k; decide

theorem scratch2_ne_right (s m : Stk) (h : s ≠ m) (k : Fin 6) : scratch2 s m k ≠ m := by
  revert s m h k; decide

theorem scratch2_ne (s m : Stk) (h : s ≠ m) {k₁ k₂ : Fin 6} (hk : k₁ ≠ k₂) :
    scratch2 s m k₁ ≠ scratch2 s m k₂ := by
  revert s m h k₁ k₂ hk; decide

end GI.Turing
