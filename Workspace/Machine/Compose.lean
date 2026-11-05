/-
Proving `GI.Cited.PolyTimeAt` for our own programs, and running two tasks in sequence.

Our procedures follow the convention of `GI.Cited.PolyTimeAt`: the input lies at a base address
`b`, passed in register 0; the procedure may use the memory at and above `b` freely; it keeps
every cell below `b`; and it returns the address of its output.

* `GI.Machine.PolyTimeWith.of_body` proves `PolyTimeWith` from a `WP` fact about procedure 0.
* `GI.Machine.PolyTimeAt.andThen` runs a program for one task and then a program for a second
  task on its output (`GI.Machine.Program.andThen`), and proves the result is polynomial.
-/
module

public import Workspace.Machine.Link

@[expose] public section

namespace GI.Machine

open GI.Cited

/-- The registers of a procedure called with the single argument `b`. -/
theorem getD_singleton (b i : ℕ) : [b].getD i 0 = if i = 0 then b else 0 := by
  cases i <;> simp

/-- Prove `PolyTimeWith` from the body of procedure 0. The body starts with `b` in register 0
and 0 in the other registers. The cost of the body plus `len b + 2` (the cost of the call
`call 0 0 [.reg 0]` in `PolyTimeAt`) must be within the bound. -/
theorem PolyTimeWith.of_body {α : Type} {t : GI.Cited.Task α} {p : Program} {body : Stmt}
    (hb : p.procs[0]? = some body) {c d : ℕ}
    (h : ∀ x b mem, t.Input x b mem →
      WP p body { mem := mem, regs := fun i => [b].getD i 0 } (fun o st' cost =>
        (∀ a < b, st'.mem a = mem a) ∧ b ≤ o.retVal ∧ t.Output x st'.mem o.retVal ∧
        cost + len b + 2 ≤ c * (t.size x + len b + 2) ^ d)) :
    PolyTimeWith t p c d := by
  intro x b mem hx
  obtain ⟨o, st', cost, hr, hbelow, hge, hout, hcost⟩ := h x b mem hx
  obtain ⟨fuel, hrun⟩ := Runs.call (r := 0) (args := [.reg 0])
    (st := { mem := mem, regs := fun _ => b }) hb hr
  refine ⟨fuel, _, _, _, hrun, hbelow, ?_, ?_, ?_⟩
  · simpa using hge
  · simpa using hout
  · simp only [evalArgs_cons, evalArgs_nil, evalExpr_reg]; omega

/-- A whole run of a program, from a `WP` fact about procedure 0. `run` calls procedure 0 with no
arguments, so its registers start at 0; the run costs one more than the body. -/
theorem exists_run_of_wp {p : Program} {body : Stmt} {mem : ℕ → ℕ}
    {Q : (ℕ → ℕ) → ℕ → ℕ → Prop} (hb : p.procs[0]? = some body)
    (h : WP p body { mem := mem, regs := fun _ => 0 } (fun o st' c => Q st'.mem o.retVal (c + 1))) :
    ∃ fuel mem' r cost, run p mem fuel = some (mem', r, cost) ∧ Q mem' r cost := by
  obtain ⟨o, st', c, hr, hq⟩ := h
  obtain ⟨fuel, hrun⟩ := Runs.call (r := 0) (args := [])
    (st := { mem := mem, regs := fun _ => 0 }) hb (by simpa using hr)
  refine ⟨fuel, _, _, _, ?_, hq⟩
  unfold run
  rw [hrun]
  simp

/-- A program that solves a task, run as a whole program (by `GI.Machine.run`) on a memory
holding an instance at address 0. `run` calls procedure 0 with no arguments, which gives the
same registers as the argument 0, and saves the cost of that argument. -/
theorem PolyTimeWith.exists_run {α : Type} {t : GI.Cited.Task α} {p : Program} {c d : ℕ}
    (hp : PolyTimeWith t p c d) {x : α} {mem : ℕ → ℕ} (hx : t.Input x 0 mem) :
    ∃ fuel mem' r cost, run p mem fuel = some (mem', r, cost) ∧ t.Output x mem' r ∧
      cost ≤ c * (t.size x + 2) ^ d := by
  obtain ⟨fuel, o, st, cost, hrun, -, -, hout, hc⟩ := hp x 0 mem hx
  obtain ⟨body, o', st'', c', hb, hr, rfl, rfl, rfl⟩ := Runs.call_inv ⟨fuel, hrun⟩
  have hregs : (fun i => (evalArgs { mem := mem, regs := fun _ => 0 } [.reg 0]).1.getD i 0) =
      fun _ => 0 := by
    funext i; cases i <;> simp
  rw [hregs] at hr
  refine exists_run_of_wp (Q := fun mem' r cost => t.Output x mem' r ∧
    cost ≤ c * (t.size x + 2) ^ d) hb ⟨o', st'', c', hr, ?_⟩
  refine ⟨by simpa using hout, ?_⟩
  simp only [evalArgs_cons, evalArgs_nil, evalExpr_reg, len_zero, Nat.add_zero] at hc
  omega

/-! ### Two tasks in sequence -/

/-- Run `p₁` on the instance at register 0, then `p₂` on the output of `p₁`, and return the
output of `p₂`. Procedure 0 is the driver, `p₁` sits at offset 1 and `p₂` after it. -/
def Program.andThen (p₁ p₂ : Program) : Program :=
  ⟨[.call 1 1 [.reg 0] ;; .call 1 (1 + p₁.procs.length) [.reg 1] ;; .ret (.reg 1)] ++
    p₁.shifted 1 ++ p₂.shifted (1 + p₁.procs.length)⟩

theorem Program.andThen_embeds_left (p₁ p₂ : Program) : Embeds (p₁.andThen p₂) p₁ 1 :=
  Embeds.of_append (A := [_]) (B := p₂.shifted (1 + p₁.procs.length)) rfl

theorem Program.andThen_embeds_right (p₁ p₂ : Program) :
    Embeds (p₁.andThen p₂) p₂ (1 + p₁.procs.length) := by
  have := Embeds.of_append (q := p₁.andThen p₂) (p := p₂)
    (A := [.call 1 1 [.reg 0] ;; .call 1 (1 + p₁.procs.length) [.reg 1] ;; .ret (.reg 1)] ++
      p₁.shifted 1) (B := []) (by simp [Program.andThen, Program.shifted, Nat.add_comm])
  have hlen : ([.call 1 1 [.reg 0] ;; .call 1 (1 + p₁.procs.length) [.reg 1] ;; .ret (.reg 1)] ++
      p₁.shifted 1).length = 1 + p₁.procs.length := by
    simp [Program.shifted, Nat.add_comm]
  rwa [hlen] at this

/-- Monotonicity of powers with a base at least one. -/
theorem pow_le_pow_of_one_le {Y : ℕ} (hY : 1 ≤ Y) {a b : ℕ} (h : a ≤ b) : Y ^ a ≤ Y ^ b :=
  Nat.pow_le_pow_right hY h

theorem one_le_pow_of_one_le {Y : ℕ} (hY : 1 ≤ Y) (a : ℕ) : 1 ≤ Y ^ a := Nat.one_le_pow _ _ hY

/-- **Two tasks in sequence.** Let `p₁` solve `t₁` and `p₂` solve `t₂` in polynomial time. Let
`t` be a task whose instances are those of `t₁`, such that a correct output of `t₁` for `x` is
an instance `f x` of `t₂`, and a correct output of `t₂` for `f x` is a correct output of `t` for
`x`. If the sizes of `x` for `t₁` and of `f x` are polynomial in the size of `x` for `t`, then
`p₁.andThen p₂` solves `t` in polynomial time. -/
theorem PolyTimeAt.andThen {α β : Type} {t₁ t : GI.Cited.Task α} {t₂ : GI.Cited.Task β}
    {p₁ p₂ : Program} (h₁ : PolyTimeAt t₁ p₁) (h₂ : PolyTimeAt t₂ p₂) (f : α → β)
    (hin : ∀ x b mem, t.Input x b mem → t₁.Input x b mem)
    (hmid : ∀ x mem r, t₁.Output x mem r → t₂.Input (f x) r mem)
    (hout : ∀ x mem r, t₂.Output (f x) mem r → t.Output x mem r)
    (A E : ℕ) (hs₁ : ∀ x, t₁.size x ≤ A * (t.size x + 2) ^ E)
    (hs₂ : ∀ x, t₂.size (f x) ≤ A * (t.size x + 2) ^ E) :
    PolyTimeAt t (p₁.andThen p₂) := by
  obtain ⟨c₁, d₁, h₁⟩ := h₁
  obtain ⟨c₂, d₂, h₂⟩ := h₂
  set K₁ := c₁ * (A + 1) ^ d₁ + 1
  set K₂ := A + K₁ + 1
  set K₃ := c₂ * K₂ ^ d₂ + 1 + K₁
  refine ⟨K₁ + 2 * K₃ + 8, (E + 1) * (d₁ + 1) * (d₂ + 1), ?_⟩
  apply PolyTimeWith.of_body (body := _) rfl
  intro x b mem hx
  -- The first call.
  refine WP.seq' (fun st₁ c₁' => CallPost t₁ c₁ d₁ x b 1 (1 + len b)
      { mem := mem, regs := fun i => [b].getD i 0 } .normal st₁ c₁') ?_ ?_
  · have := PolyTimeWith.wp_call h₁ (Program.andThen_embeds_left p₁ p₂) (r := 1) (e := .reg 0)
      (st := { mem := mem, regs := fun i => [b].getD i 0 }) (x := x) (by simpa using hin _ _ _ hx)
    simp only [evalExpr_reg, List.getD_cons_zero] at this
    exact this.mono fun o st' c hp => ⟨hp.normal, hp.normal ▸ hp⟩
  rintro st₁ c₁' hp₁
  set r := st₁.regs 1
  -- The second call.
  refine WP.seq' (fun st₂ c₂' => CallPost t₂ c₂ d₂ (f x) r 1 (1 + len r) st₁ .normal st₂ c₂')
    ?_ ?_
  · have := PolyTimeWith.wp_call h₂ (Program.andThen_embeds_right p₁ p₂) (r := 1)
      (e := .reg 1) (st := st₁) (x := f x) (by simpa using hmid _ _ _ hp₁.output)
    simp only [evalExpr_reg] at this
    exact this.mono fun o st' c hp => ⟨hp.normal, hp.normal ▸ hp⟩
  rintro st₂ c₂' hp₂
  apply WP.ret
  simp only [evalExpr_reg, Outcome.retVal_returned]
  refine ⟨?_, ?_, hout _ _ _ hp₂.output, ?_⟩
  · intro a ha
    rw [hp₂.below a (lt_of_lt_of_le ha hp₁.ge), hp₁.below a ha]
  · exact le_trans hp₁.ge hp₂.ge
  -- The cost.
  set X := t.size x + len b + 2
  set Y := X ^ (E + 1)
  set Z := Y ^ (d₁ + 1)
  set W := Z ^ (d₂ + 1)
  have hX1 : 1 ≤ X := by omega
  have hXY : X ≤ Y := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ Y := pow_le_pow_of_one_le hX1 (by omega)
  have hY1 : 1 ≤ Y := le_trans hX1 hXY
  have hYZ : Y ≤ Z := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Z := pow_le_pow_of_one_le hY1 (by omega)
  have hZ1 : 1 ≤ Z := le_trans hY1 hYZ
  have hZW : Z ≤ W := by
    calc Z = Z ^ 1 := (pow_one Z).symm
      _ ≤ W := pow_le_pow_of_one_le hZ1 (by omega)
  have hsY : ∀ s, s ≤ A * (t.size x + 2) ^ E → s ≤ A * Y := by
    intro s hs
    refine le_trans hs (Nat.mul_le_mul_left _ ?_)
    calc (t.size x + 2) ^ E ≤ X ^ E := Nat.pow_le_pow_left (by omega) _
      _ ≤ Y := pow_le_pow_of_one_le hX1 (by omega)
  have hs1 := hsY _ (hs₁ x)
  have hs2 := hsY _ (hs₂ x)
  -- Cost of the first call.
  have hc1 : c₁' ≤ K₁ * Z := by
    have h := hp₁.cost_le
    have hb1 : t₁.size x + len b + 2 ≤ (A + 1) * Y := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    have hpow : (t₁.size x + len b + 2) ^ d₁ ≤ (A + 1) ^ d₁ * Z := by
      calc (t₁.size x + len b + 2) ^ d₁ ≤ ((A + 1) * Y) ^ d₁ := Nat.pow_le_pow_left hb1 _
        _ = (A + 1) ^ d₁ * Y ^ d₁ := Nat.mul_pow _ _ _
        _ ≤ (A + 1) ^ d₁ * Z := Nat.mul_le_mul_left _ (pow_le_pow_of_one_le hY1 (by omega))
    have : c₁ * (t₁.size x + len b + 2) ^ d₁ ≤ c₁ * (A + 1) ^ d₁ * Z := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hpow
    have hK : K₁ * Z = c₁ * (A + 1) ^ d₁ * Z + Z := by simp only [K₁, Nat.add_mul, Nat.one_mul]
    rw [hK]; omega
  have hr : len r ≤ K₁ * Z := le_trans hp₁.len_le hc1
  -- Cost of the second call.
  have hc2 : c₂' ≤ K₃ * W := by
    have h := hp₂.cost_le
    have hb2 : t₂.size (f x) + len r + 2 ≤ K₂ * Z := by
      have : A * Y ≤ A * Z := Nat.mul_le_mul_left _ hYZ
      simp only [K₂, Nat.add_mul, Nat.one_mul]; omega
    have hpow : (t₂.size (f x) + len r + 2) ^ d₂ ≤ K₂ ^ d₂ * W := by
      calc (t₂.size (f x) + len r + 2) ^ d₂ ≤ (K₂ * Z) ^ d₂ := Nat.pow_le_pow_left hb2 _
        _ = K₂ ^ d₂ * Z ^ d₂ := Nat.mul_pow _ _ _
        _ ≤ K₂ ^ d₂ * W := Nat.mul_le_mul_left _ (pow_le_pow_of_one_le hZ1 (by omega))
    have : c₂ * (t₂.size (f x) + len r + 2) ^ d₂ ≤ c₂ * K₂ ^ d₂ * W := by
      rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hpow
    have hK1 : K₁ * Z ≤ K₁ * W := Nat.mul_le_mul_left _ hZW
    have hK : K₃ * W = c₂ * K₂ ^ d₂ * W + W + K₁ * W := by
      simp only [K₃, Nat.add_mul, Nat.one_mul]
    have hW1 : 1 ≤ W := le_trans hZ1 hZW
    rw [hK]; omega
  have hr2 : len (st₂.regs 1) ≤ K₃ * W := le_trans hp₂.len_le hc2
  have hD : X ^ ((E + 1) * (d₁ + 1) * (d₂ + 1)) = W := by
    simp only [W, Z, Y]
    rw [pow_mul, pow_mul]
  rw [hD]
  have h2K : (K₁ + 2 * K₃ + 8) * W = K₁ * W + 2 * (K₃ * W) + 8 * W := by ring
  rw [h2K]
  have hK1 : K₁ * Z ≤ K₁ * W := Nat.mul_le_mul_left _ hZW
  have hXW : X ≤ W := le_trans hXY (le_trans hYZ hZW)
  omega

end GI.Machine
