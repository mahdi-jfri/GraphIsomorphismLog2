/-
The Turing machine (`Turing.FinTM2`) that simulates a stack machine program `P`.

Every stack has alphabet `Bool`, which makes `inputAlphabet` and `outputAlphabet` trivial and
avoids dependent-alphabet rewrites on `Function.update`. There are 14 stacks: input, output,
output buffer (reversed), return stack, two scratch stacks, and the eight number stacks.

This file defines the stack index type `K`, the micro-step labels `Micro`, the internal state
`State N`, the compiled machine `tm P`, the step-counting reachability relation `ReachesIn`,
and a general bound (`reachesIn_totalLen_le`) showing that total stack length grows by at most
a constant per Turing machine step.
-/
module

public import Workspace.Turing.TM.Bits
public import Workspace.Turing.Interface

@[expose] public section

namespace GI.Turing.TM

open _root_.Turing (FinTM2 TM2ComputableAux initList haltList)
open _root_.Turing.TM2 (Stmt)
open Function (update)

/-- The 14 stacks of the simulating Turing machine. -/
inductive K
  | inp
  | out
  | outBuf
  | ret
  | scr0
  | scr1
  | num (s : SM.Stk)
  deriving DecidableEq

/-- Equivalence between `K` and `Fin 6 ⊕ Fin 8`, used to build `Fintype K`. -/
def kEquiv : K ≃ Fin 6 ⊕ Fin 8 where
  toFun
    | .inp => Sum.inl 0
    | .out => Sum.inl 1
    | .outBuf => Sum.inl 2
    | .ret => Sum.inl 3
    | .scr0 => Sum.inl 4
    | .scr1 => Sum.inl 5
    | .num s => Sum.inr s
  invFun
    | Sum.inl ⟨0, _⟩ => .inp
    | Sum.inl ⟨1, _⟩ => .out
    | Sum.inl ⟨2, _⟩ => .outBuf
    | Sum.inl ⟨3, _⟩ => .ret
    | Sum.inl ⟨4, _⟩ => .scr0
    | Sum.inl ⟨5, _⟩ => .scr1
    | Sum.inr s => .num s
  left_inv k := by cases k <;> rfl
  right_inv x := by
    rcases x with ⟨i, hi⟩ | s
    · match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ => rfl
    · rfl

instance : Fintype K := Fintype.ofEquiv _ kEquiv.symm

/-- The ten stacks drained during the halting phase (every stack except `out`, `outBuf`, and the
already-empty scratch stacks `scr0` and `scr1`). -/
def drainOrder : Fin 10 → K
  | ⟨0, _⟩ => .inp
  | ⟨1, _⟩ => .ret
  | ⟨2, _⟩ => .num 0
  | ⟨3, _⟩ => .num 1
  | ⟨4, _⟩ => .num 2
  | ⟨5, _⟩ => .num 3
  | ⟨6, _⟩ => .num 4
  | ⟨7, _⟩ => .num 5
  | ⟨8, _⟩ => .num 6
  | ⟨9, _⟩ => .num 7

/-- Micro-step labels attached to each instruction index (and to the halting index `N`). -/
inductive Micro
  | start
  | popLoop
  | parityLoop
  | movePop
  | moveRestore
  | copyPop
  | copyRestore0
  | copyRestore1
  | addLoop
  | subLoop
  | drainScr0
  | stripZeros
  | retLoop
  | flushOut
  | drain (i : Fin 10)
  deriving DecidableEq

/-- Equivalence between `Micro` and `Fin 14 ⊕ Fin 10`, used to build `Fintype Micro`. -/
def microEquiv : Micro ≃ Fin 14 ⊕ Fin 10 where
  toFun
    | .start => Sum.inl 0
    | .popLoop => Sum.inl 1
    | .parityLoop => Sum.inl 2
    | .movePop => Sum.inl 3
    | .moveRestore => Sum.inl 4
    | .copyPop => Sum.inl 5
    | .copyRestore0 => Sum.inl 6
    | .copyRestore1 => Sum.inl 7
    | .addLoop => Sum.inl 8
    | .subLoop => Sum.inl 9
    | .drainScr0 => Sum.inl 10
    | .stripZeros => Sum.inl 11
    | .retLoop => Sum.inl 12
    | .flushOut => Sum.inl 13
    | .drain i => Sum.inr i
  invFun
    | Sum.inl ⟨0, _⟩ => .start
    | Sum.inl ⟨1, _⟩ => .popLoop
    | Sum.inl ⟨2, _⟩ => .parityLoop
    | Sum.inl ⟨3, _⟩ => .movePop
    | Sum.inl ⟨4, _⟩ => .moveRestore
    | Sum.inl ⟨5, _⟩ => .copyPop
    | Sum.inl ⟨6, _⟩ => .copyRestore0
    | Sum.inl ⟨7, _⟩ => .copyRestore1
    | Sum.inl ⟨8, _⟩ => .addLoop
    | Sum.inl ⟨9, _⟩ => .subLoop
    | Sum.inl ⟨10, _⟩ => .drainScr0
    | Sum.inl ⟨11, _⟩ => .stripZeros
    | Sum.inl ⟨12, _⟩ => .retLoop
    | Sum.inl ⟨13, _⟩ => .flushOut
    | Sum.inr i => .drain i
  left_inv m := by cases m <;> rfl
  right_inv x := by
    rcases x with ⟨i, hi⟩ | j
    · match i, hi with
      | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _
      | 10, _ | 11, _ | 12, _ | 13, _ => rfl
    · rfl

instance : Fintype Micro := Fintype.ofEquiv _ microEquiv.symm

/-- Labels for a program of length `N`. Index `N` hosts the halting cleanup phase. -/
abbrev Lab (N : ℕ) : Type := Fin (N + 1) × Micro

/-- Finite internal state of the Turing machine for a program of length `N`. -/
structure State (N : ℕ) where
  bit : Bool
  bit2 : Bool
  flag : Bool
  flag2 : Bool
  carry : Bool
  addr : Fin (N + 1)
  deriving DecidableEq

/-- Equivalence between `State N` and a product of finite types. -/
def stateEquiv (N : ℕ) :
    State N ≃ Bool × Bool × Bool × Bool × Bool × Fin (N + 1) where
  toFun s := (s.bit, s.bit2, s.flag, s.flag2, s.carry, s.addr)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv s := by cases s; rfl
  right_inv t := by rcases t with ⟨_, _, _, _, _, _⟩; rfl

instance (N : ℕ) : Fintype (State N) := Fintype.ofEquiv _ (stateEquiv N).symm

/-- Initial internal state: all booleans `false` and return address `0`. -/
def initState (N : ℕ) : State N :=
  ⟨false, false, false, false, false, ⟨0, Nat.zero_lt_succ N⟩⟩

/-- Clamp a program counter `n` into `Fin (N + 1)`. -/
def clampPc (N n : ℕ) : Fin (N + 1) :=
  ⟨min n N, Nat.lt_succ_of_le (Nat.min_le_right n N)⟩

theorem clampPc_of_le {N n : ℕ} (h : n ≤ N) :
    clampPc N n = ⟨n, Nat.lt_succ_of_le h⟩ := by
  ext; exact Nat.min_eq_left h

/-- Shorthand for TM2 statements with uniform `Bool` alphabet on all stacks. -/
abbrev MStmt (N : ℕ) : Type := Stmt (fun _ : K => Bool) (Lab N) (State N)

/-- Push a constant list `bs` onto stack `k` so `bs` sits at the top, then continue with `q`. -/
def pushList {N : ℕ} (k : K) : List Bool → MStmt N → MStmt N
  | [], q => q
  | b :: bs, q => pushList k bs (.push k (fun _ => b) q)

theorem stepAux_pushList {N : ℕ} (k : K) (bs : List Bool) (q : MStmt N)
    (v : State N) (S : K → List Bool) :
    Turing.TM2.stepAux (pushList k bs q) v S =
      Turing.TM2.stepAux q v (update S k (bs ++ S k)) := by
  induction bs generalizing q with
  | nil => simp [pushList]
  | cons b bs ih =>
    simp only [pushList, ih, Turing.TM2.stepAux, Function.update_idem, Function.update_self,
      List.cons_append]

/-- Pop a single encoded number from `s`, looping at `self`, then run `exitStmt`. -/
def popLoopStmt {N : ℕ} (s : K) (self : Lab N) (exitStmt : MStmt N) : MStmt N :=
  .pop s (fun v ob => { v with flag := ob == some true })
    (.branch (fun v => v.flag)
      (.pop s (fun v _ => v) (.goto (fun _ => self)))
      exitStmt)

/-- Pop raw bits from `scr` and push them as encoded digits `[true, b]` onto `tgt`, looping at
`self`, then run `exitStmt` once `scr` is empty. -/
def restoreLoopStmt {N : ℕ} (scr tgt : K) (self : Lab N) (exitStmt : MStmt N) : MStmt N :=
  .pop scr (fun v ob => match ob with
    | none => { v with flag := false }
    | some b => { v with flag := true, bit := b })
    (.branch (fun v => v.flag)
      (.push tgt (fun v => v.bit) (.push tgt (fun _ => true) (.goto (fun _ => self))))
      exitStmt)

/-- Pop encoded digits from `s` onto `scr0` (as raw bits), then push separator `false` onto `t`
and jump to `next`. -/
def movePopStmt {N : ℕ} (s t : K) (self next : Lab N) : MStmt N :=
  .pop s (fun v ob => { v with flag := ob == some true })
    (.branch (fun v => v.flag)
      (.pop s (fun v ob => { v with bit := ob.getD false })
        (.push .scr0 (fun v => v.bit) (.goto (fun _ => self))))
      (.push t (fun _ => false) (.goto (fun _ => next))))

/-- Pop encoded digits from `s` onto both `scr0` and `scr1`, then push separator `false` onto `s`
and jump to `next`. -/
def copyPopStmt {N : ℕ} (s : K) (self next : Lab N) : MStmt N :=
  .pop s (fun v ob => { v with flag := ob == some true })
    (.branch (fun v => v.flag)
      (.pop s (fun v ob => { v with bit := ob.getD false })
        (.push .scr0 (fun v => v.bit)
          (.push .scr1 (fun v => v.bit) (.goto (fun _ => self)))))
      (.push s (fun _ => false) (.goto (fun _ => next))))

/-- One loop step of `add s t`: read next digits of `s` and `t` (leaving separators intact until
both numbers end), push the sum digit to `scr0`, and at the end pop `t`'s separator, flush the
final carry if any, and jump to `next`. -/
def addLoopStmt {N : ℕ} (s t : K) (self next : Lab N) : MStmt N :=
  let body : MStmt N :=
    .branch (fun v => v.flag || v.flag2)
      (.push .scr0 (fun v => xor (xor v.bit v.bit2) v.carry)
        (.load (fun v =>
            { v with carry := (v.bit && v.bit2) || (v.bit && v.carry) || (v.bit2 && v.carry) })
          (.goto (fun _ => self))))
      (.pop t (fun v _ => v)
        (.branch (fun v => v.carry)
          (.push .scr0 (fun _ => true) (.goto (fun _ => next)))
          (.goto (fun _ => next))))
  let checkT : MStmt N :=
    .peek t (fun v ob => { v with flag2 := ob == some true })
      (.branch (fun v => v.flag2)
        (.pop t (fun v _ => v) (.pop t (fun v ob => { v with bit2 := ob.getD false }) body))
        (.load (fun v => { v with bit2 := false }) body))
  .peek s (fun v ob => { v with flag := ob == some true })
    (.branch (fun v => v.flag)
      (.pop s (fun v _ => v) (.pop s (fun v ob => { v with bit := ob.getD false }) checkT))
      (.load (fun v => { v with bit := false }) checkT))

/-- One loop step of `sub s t`: read next digits of `s` and `t`, push the difference digit to
`scr0`, and at the end pop `t`'s separator and jump to `onBorrow` if underflow occurred or
`onNoBorrow` otherwise. -/
def subLoopStmt {N : ℕ} (s t : K) (self onBorrow onNoBorrow : Lab N) : MStmt N :=
  let body : MStmt N :=
    .branch (fun v => v.flag || v.flag2)
      (.push .scr0 (fun v => xor (xor v.bit v.bit2) v.carry)
        (.load (fun v =>
            { v with carry := (!v.bit && (v.bit2 || v.carry)) || (v.bit2 && v.carry) })
          (.goto (fun _ => self))))
      (.pop t (fun v _ => v)
        (.branch (fun v => v.carry)
          (.goto (fun _ => onBorrow))
          (.goto (fun _ => onNoBorrow))))
  let checkT : MStmt N :=
    .peek t (fun v ob => { v with flag2 := ob == some true })
      (.branch (fun v => v.flag2)
        (.pop t (fun v _ => v) (.pop t (fun v ob => { v with bit2 := ob.getD false }) body))
        (.load (fun v => { v with bit2 := false }) body))
  .peek s (fun v ob => { v with flag := ob == some true })
    (.branch (fun v => v.flag)
      (.pop s (fun v _ => v) (.pop s (fun v ob => { v with bit := ob.getD false }) checkT))
      (.load (fun v => { v with bit := false }) checkT))

/-- Empty stack `k`, looping at `self`, then run `exitStmt`. -/
def drainLoopStmt {N : ℕ} (k : K) (self : Lab N) (exitStmt : MStmt N) : MStmt N :=
  .pop k (fun v ob => { v with flag := ob.isSome })
    (.branch (fun v => v.flag)
      (.goto (fun _ => self))
      exitStmt)

/-- Pop leading `false` bits from `scr0`, looping at `self`, then jump to `next`. -/
def stripZerosStmt {N : ℕ} (self next : Lab N) : MStmt N :=
  .peek .scr0 (fun v ob => { v with flag := ob == some false })
    (.branch (fun v => v.flag)
      (.pop .scr0 (fun v _ => v) (.goto (fun _ => self)))
      (.goto (fun _ => next)))

/-- Pop unary return address from `ret` into `v.addr`, looping at `self`, then jump to
`(v.addr, .start)`. -/
def retLoopStmt {N : ℕ} (self : Lab N) : MStmt N :=
  .pop .ret (fun v ob => { v with flag := ob == some true })
    (.branch (fun v => v.flag)
      (.load (fun v => { v with addr := clampPc N (v.addr.val + 1) }) (.goto (fun _ => self)))
      (.goto (fun v => (v.addr, .start))))

/-- Move all bits from `outBuf` onto `out` (reversing them), then reset state and halt. -/
def flushOutStmt {N : ℕ} (self : Lab N) : MStmt N :=
  .pop .outBuf (fun v ob => match ob with
    | none => { v with flag := false }
    | some b => { v with flag := true, bit := b })
    (.branch (fun v => v.flag)
      (.push .out (fun v => v.bit) (.goto (fun _ => self)))
      (.load (fun _ => initState N) .halt))

/-- Statement for a single stack-machine instruction at index `pc < N`. -/
def instrStmt (N : ℕ) (pc : Fin (N + 1)) (i : SM.Instr) (μ : Micro) : MStmt N :=
  let nextPc := clampPc N (pc.val + 1)
  match i, μ with
  | .push s k, .start =>
    pushList (.num s) (encNat k) (.goto (fun _ => (nextPc, .start)))
  | .pop _, .start =>
    .goto (fun _ => (pc, .popLoop))
  | .pop s, .popLoop =>
    popLoopStmt (.num s) (pc, .popLoop) (.goto (fun _ => (nextPc, .start)))
  | .copy _ _, .start =>
    .goto (fun _ => (pc, .copyPop))
  | .copy s _, .copyPop =>
    copyPopStmt (.num s) (pc, .copyPop) (pc, .copyRestore0)
  | .copy s t, .copyRestore0 =>
    restoreLoopStmt .scr0 (.num s) (pc, .copyRestore0)
      (.push (.num t) (fun _ => false) (.goto (fun _ => (pc, .copyRestore1))))
  | .copy _ t, .copyRestore1 =>
    restoreLoopStmt .scr1 (.num t) (pc, .copyRestore1) (.goto (fun _ => (nextPc, .start)))
  | .move _ _, .start =>
    .goto (fun _ => (pc, .movePop))
  | .move s t, .movePop =>
    movePopStmt (.num s) (.num t) (pc, .movePop) (pc, .moveRestore)
  | .move _ t, .moveRestore =>
    restoreLoopStmt .scr0 (.num t) (pc, .moveRestore) (.goto (fun _ => (nextPc, .start)))
  | .add _ _, .start =>
    .load (fun v => { v with carry := false }) (.goto (fun _ => (pc, .addLoop)))
  | .add s t, .addLoop =>
    addLoopStmt (.num s) (.num t) (pc, .addLoop) (pc, .moveRestore)
  | .add s _, .moveRestore =>
    restoreLoopStmt .scr0 (.num s) (pc, .moveRestore) (.goto (fun _ => (nextPc, .start)))
  | .sub _ _, .start =>
    .load (fun v => { v with carry := false }) (.goto (fun _ => (pc, .subLoop)))
  | .sub s t, .subLoop =>
    subLoopStmt (.num s) (.num t) (pc, .subLoop) (pc, .drainScr0) (pc, .stripZeros)
  | .sub _ _, .drainScr0 =>
    drainLoopStmt .scr0 (pc, .drainScr0) (.goto (fun _ => (nextPc, .start)))
  | .sub _ _, .stripZeros =>
    stripZerosStmt (pc, .stripZeros) (pc, .moveRestore)
  | .sub s _, .moveRestore =>
    restoreLoopStmt .scr0 (.num s) (pc, .moveRestore) (.goto (fun _ => (nextPc, .start)))
  | .double s, .start =>
    .peek (.num s) (fun v ob => { v with flag := ob == some true })
      (.branch (fun v => v.flag)
        (pushList (.num s) [true, false] (.goto (fun _ => (nextPc, .start))))
        (.goto (fun _ => (nextPc, .start))))
  | .half s, .start =>
    .peek (.num s) (fun v ob => { v with flag := ob == some true })
      (.branch (fun v => v.flag)
        (.pop (.num s) (fun v _ => v)
          (.pop (.num s) (fun v _ => v) (.goto (fun _ => (nextPc, .start)))))
        (.goto (fun _ => (nextPc, .start))))
  | .parity s, .start =>
    .pop (.num s) (fun v ob => { v with flag := ob == some true })
      (.branch (fun v => v.flag)
        (.pop (.num s) (fun v ob => { v with bit := ob.getD false })
          (.goto (fun _ => (pc, .parityLoop))))
        (.push (.num s) (fun _ => false) (.goto (fun _ => (nextPc, .start)))))
  | .parity s, .parityLoop =>
    popLoopStmt (.num s) (pc, .parityLoop)
      (.branch (fun v => v.bit)
        (pushList (.num s) [true, true, false] (.goto (fun _ => (nextPc, .start))))
        (pushList (.num s) [false] (.goto (fun _ => (nextPc, .start)))))
  | .jz s l, .start =>
    .pop (.num s) (fun v ob => { v with flag := ob == some true })
      (.branch (fun v => v.flag)
        (.pop (.num s) (fun v _ => v) (.goto (fun _ => (pc, .popLoop))))
        (.goto (fun _ => (clampPc N l, .start))))
  | .jz s _, .popLoop =>
    popLoopStmt (.num s) (pc, .popLoop) (.goto (fun _ => (nextPc, .start)))
  | .jmp l, .start =>
    .goto (fun _ => (clampPc N l, .start))
  | .jnil s l, .start =>
    .peek (.num s) (fun v ob => { v with flag := ob.isNone })
      (.branch (fun v => v.flag)
        (.goto (fun _ => (clampPc N l, .start)))
        (.goto (fun _ => (nextPc, .start))))
  | .call l, .start =>
    pushList .ret (encRet (pc.val + 1)) (.goto (fun _ => (clampPc N l, .start)))
  | .ret, .start =>
    .load (fun v => { v with addr := ⟨0, Nat.zero_lt_succ N⟩ }) (.goto (fun _ => (pc, .retLoop)))
  | .ret, .retLoop =>
    retLoopStmt (pc, .retLoop)
  | .read s, .start =>
    .pop .inp (fun v ob => match ob with
      | none => { v with flag := false, bit := false }
      | some b => { v with flag := true, bit := b })
      (.branch (fun v => v.flag)
        (.branch (fun v => v.bit)
          (pushList (.num s) (encNat 1) (.goto (fun _ => (nextPc, .start))))
          (pushList (.num s) (encNat 0) (.goto (fun _ => (nextPc, .start)))))
        (pushList (.num s) (encNat 2) (.goto (fun _ => (nextPc, .start)))))
  | .write s, .start =>
    .pop (.num s) (fun v ob => { v with flag := ob == some true })
      (.branch (fun v => v.flag)
        (.pop (.num s) (fun v _ => v)
          (.push .outBuf (fun _ => true) (.goto (fun _ => (pc, .popLoop)))))
        (.push .outBuf (fun _ => false) (.goto (fun _ => (nextPc, .start)))))
  | .write s, .popLoop =>
    popLoopStmt (.num s) (pc, .popLoop) (.goto (fun _ => (nextPc, .start)))
  | .halt, .start =>
    .goto (fun _ => (⟨N, Nat.lt_succ_self N⟩, .drain 0))
  | _, _ => .halt

/-- Statement for the halting cleanup index `N`. -/
def haltStmt (N : ℕ) : Micro → MStmt N
  | .drain i =>
    let haltIdx : Fin (N + 1) := ⟨N, Nat.lt_succ_self N⟩
    let nextLab : Lab N :=
      if h : i.val + 1 < 10 then (haltIdx, .drain ⟨i.val + 1, h⟩) else (haltIdx, .flushOut)
    drainLoopStmt (drainOrder i) (haltIdx, .drain i) (.goto (fun _ => nextLab))
  | .flushOut =>
    flushOutStmt (⟨N, Nat.lt_succ_self N⟩, .flushOut)
  | _ => .halt

/-- Program map for the Turing machine simulating `P`. -/
def tmProg (P : SM.Program) : Lab P.length → MStmt P.length
  | (pc, μ) =>
    if h : pc.val < P.length then instrStmt P.length pc P[pc.val] μ else haltStmt P.length μ

/-- The `Turing.FinTM2` simulating stack-machine program `P`. -/
@[reducible] def tm (P : SM.Program) : FinTM2 where
  K := K
  k₀ := .inp
  k₁ := .out
  Γ _ := Bool
  Λ := Lab P.length
  main := (⟨0, Nat.zero_lt_succ P.length⟩, .start)
  σ := State P.length
  initialState := initState P.length
  m := tmProg P

/-- The bundled `TM2ComputableAux Bool Bool` simulating stack-machine program `P`. -/
def tmAux (P : SM.Program) : TM2ComputableAux Bool Bool where
  tm := tm P
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool

/-- `ReachesIn M a b t`: machine `M` goes from configuration `a` to `b` in exactly `t` steps. -/
def ReachesIn (M : FinTM2) (a b : M.Cfg) (t : ℕ) : Prop :=
  (flip bind M.step)^[t] (some a) = some b

namespace ReachesIn

theorem refl {M : FinTM2} (a : M.Cfg) : ReachesIn M a a 0 := rfl

theorem single {M : FinTM2} {a b : M.Cfg} (h : M.step a = some b) : ReachesIn M a b 1 := h

theorem trans {M : FinTM2} {a b c : M.Cfg} {t₁ t₂ : ℕ}
    (h₁ : ReachesIn M a b t₁) (h₂ : ReachesIn M b c t₂) : ReachesIn M a c (t₁ + t₂) := by
  unfold ReachesIn at *
  rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]

theorem step_head {M : FinTM2} {a b c : M.Cfg} {t : ℕ}
    (h₁ : M.step a = some b) (h₂ : ReachesIn M b c t) : ReachesIn M a c (t + 1) := by
  rw [Nat.add_comm]
  exact trans (single h₁) h₂

end ReachesIn

/-- Total length of all 14 stacks in a stack assignment `S : K → List Bool`. -/
def totalLen (S : K → List Bool) : ℕ :=
  ∑ k : K, (S k).length

theorem totalLen_update_cons (S : K → List Bool) (k : K) (b : Bool) :
    totalLen (update S k (b :: S k)) = totalLen S + 1 := by
  unfold totalLen
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    ← Finset.add_sum_erase _ (fun j => (S j).length) (Finset.mem_univ k)]
  have hrest : ∑ x ∈ Finset.univ.erase k, (update S k (b :: S k) x).length =
      ∑ x ∈ Finset.univ.erase k, (S x).length := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [Function.update_self, List.length_cons, hrest]
  omega

theorem totalLen_update_tail_le (S : K → List Bool) (k : K) :
    totalLen (update S k (S k).tail) ≤ totalLen S := by
  unfold totalLen
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k),
    ← Finset.add_sum_erase _ (fun j => (S j).length) (Finset.mem_univ k)]
  have hrest : ∑ x ∈ Finset.univ.erase k, (update S k (S k).tail x).length =
      ∑ x ∈ Finset.univ.erase k, (S x).length := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [Function.update_self, hrest]
  have htail : (S k).tail.length ≤ (S k).length := by cases S k <;> simp
  omega

/-- Maximum number of `push` operations along any execution path of a statement. -/
def pushCount {N : ℕ} : MStmt N → ℕ
  | .push _ _ q => 1 + pushCount q
  | .peek _ _ q => pushCount q
  | .pop _ _ q => pushCount q
  | .load _ q => pushCount q
  | .branch _ q₁ q₂ => max (pushCount q₁) (pushCount q₂)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_totalLen_le {N : ℕ} (q : MStmt N) (v : State N) (S : K → List Bool) :
    totalLen (Turing.TM2.stepAux q v S).stk ≤ totalLen S + pushCount q := by
  induction q generalizing v S with
  | push k f q ih =>
    simp only [Turing.TM2.stepAux, pushCount]
    have h := ih v (update S k (f v :: S k))
    rw [totalLen_update_cons] at h
    omega
  | peek k f q ih =>
    exact ih _ S
  | pop k f q ih =>
    simp only [Turing.TM2.stepAux, pushCount]
    have h := ih (f v (S k).head?) (update S k (S k).tail)
    have hle := totalLen_update_tail_le S k
    omega
  | load a q ih =>
    exact ih _ S
  | branch f q₁ q₂ ih₁ ih₂ =>
    simp only [Turing.TM2.stepAux, pushCount]
    cases f v
    · simp only [Bool.cond_false]
      have := ih₂ v S; omega
    · simp only [Bool.cond_true]
      have := ih₁ v S; omega
  | goto f =>
    simp [Turing.TM2.stepAux, pushCount]
  | halt =>
    simp [Turing.TM2.stepAux, pushCount]

/-- Maximum number of pushes executed in a single step of `tm P`. -/
def maxPush (P : SM.Program) : ℕ :=
  Finset.univ.sup fun l : Lab P.length => pushCount (tmProg P l)

theorem step_totalLen_le {P : SM.Program} {a b : (tm P).Cfg}
    (h : (tm P).step a = some b) :
    totalLen b.stk ≤ totalLen a.stk + maxPush P := by
  rcases a with ⟨l, v, S⟩
  cases l with
  | none => simp [FinTM2.step, Turing.TM2.step] at h
  | some lbl =>
    simp only [FinTM2.step, Turing.TM2.step] at h
    cases h
    have hle := stepAux_totalLen_le (tmProg P lbl) v S
    have hsup : pushCount (tmProg P lbl) ≤ maxPush P :=
      Finset.le_sup (f := fun l : Lab P.length => pushCount (tmProg P l)) (Finset.mem_univ lbl)
    dsimp only
    omega

theorem reachesIn_totalLen_le {P : SM.Program} {a b : (tm P).Cfg} {t : ℕ}
    (h : ReachesIn (tm P) a b t) :
    totalLen b.stk ≤ totalLen a.stk + maxPush P * t := by
  induction t generalizing a with
  | zero =>
    simp only [ReachesIn, Function.iterate_zero_apply, Option.some.injEq] at h
    subst h; simp
  | succ t ih =>
    unfold ReachesIn at h
    rw [Function.iterate_succ_apply] at h
    have hbind : flip bind (tm P).step (some a) = (tm P).step a := rfl
    rw [hbind] at h
    cases hs : (tm P).step a with
    | none =>
      rw [hs] at h
      have hnone : ∀ n, (flip bind (tm P).step)^[n] none = none := by
        intro n; induction n with
        | zero => rfl
        | succ n ihn =>
          rw [Function.iterate_succ_apply]
          exact ihn
      rw [hnone] at h
      cases h
    | some a₁ =>
      rw [hs] at h
      have h1 := step_totalLen_le hs
      have h2 := ih h
      rw [Nat.mul_succ]
      omega

theorem initList_stk (P : SM.Program) (x : List Bool) (k : K) :
    (initList (tm P) x).stk k = if k = .inp then x else [] := by
  simp only [initList, tm]
  split_ifs with h
  · subst h; rfl
  · simp

theorem haltList_stk (P : SM.Program) (y : List Bool) (k : K) :
    (haltList (tm P) y).stk k = if k = .out then y else [] := by
  simp only [haltList, tm]
  split_ifs with h
  · subst h; rfl
  · simp

theorem totalLen_initList (P : SM.Program) (x : List Bool) :
    totalLen (initList (tm P) x).stk = x.length := by
  unfold totalLen
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ K.inp)]
  have h0 : ∑ k ∈ Finset.univ.erase K.inp, ((initList (tm P) x).stk k).length = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [initList_stk, ite_eq_right_iff.mpr (fun h => absurd h (Finset.ne_of_mem_erase hk))]
    rfl
  rw [h0, Nat.add_zero, initList_stk]
  simp

theorem totalLen_eq (S : K → List Bool) :
    totalLen S =
      (S .inp).length + (S .out).length + (S .outBuf).length + (S .ret).length +
      (S .scr0).length + (S .scr1).length +
      (S (.num 0)).length + (S (.num 1)).length + (S (.num 2)).length + (S (.num 3)).length +
      (S (.num 4)).length + (S (.num 5)).length + (S (.num 6)).length + (S (.num 7)).length := by
  unfold totalLen
  have hsum : ∑ k : K, (S k).length = ∑ x : Fin 6 ⊕ Fin 8, (S (kEquiv.symm x)).length :=
    (Equiv.sum_comp kEquiv.symm (fun k => (S k).length)).symm
  rw [hsum, Fintype.sum_sum_type, Fin.sum_univ_six, Fin.sum_univ_eight]
  simp only [kEquiv, Equiv.coe_fn_symm_mk]
  omega

end GI.Turing.TM
