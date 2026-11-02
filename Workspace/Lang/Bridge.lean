/-
From a `GI.Lang` program back to a cited-style statement `∃ prog, PolyTimeAt (Task.ofVal enc
Correct) prog` (`GI.Lang.polyTimeAt_ofVal_of_lang`).

A cited algorithm enters the project as such a statement, and `Prim.ofCited` turns it into a
primitive of the language. This file goes the other way. If user function `f` of a program `P`
computes a correct output from `enc x` at a language cost polynomial in the weight of `enc x`,
then a machine program solves `Task.ofVal enc Correct` in polynomial time. The primitives of `P`
need no extra hypothesis: each `Prim` carries its own machine program and contract, and the
compiler links them in (`compile`).

The machine program is `bridgeProgram P f`. Its procedure 0, `bridgeBody f`, receives the base
address `b` of the instance in register 0. It reads the number `s` of cells of the instance
value, calls user function `f` with the argument at `b` and the heap pointer at `b + s`, and
returns `b + s`, where the compiled function leaves its result.

The language cost is measured by the weight `Val.wt` (cells plus bit lengths), while the size of
a task instance is its number of cells. So the bridge needs the numbers inside `enc x` to be
small: `polyTimeAt_ofVal_of_lang` asks that the weight be polynomial in the number of cells, and
`polyTimeAt_ofVal_of_lang_cells` asks that every cell be polynomial in the number of cells,
which is the requirement on the tasks of `GI.Cited.Task.ofVal`.
-/
import Workspace.Lang.CorrectMain
import Workspace.Lang.Lib.Basic
import Workspace.Machine.Compose

namespace GI.Lang

open GI.Machine (Stmt Outcome State WP len len_mono Embeds evalExpr evalArgs PolyTimeWith)
open GI.Cited (Val ValAt PolyTimeAt)

/-- Procedure 0 of the bridge program. Register 0 holds the base address `b`. Register 1 gets
the size `s` of the value at `b` and then the heap pointer `b + s`. User function `f` is
procedure `2 + f`; it gets the heap pointer in register 0 and the argument address in
register 2. -/
def bridgeBody (f : ℕ) : Stmt :=
  sizeInto 1 0 ;; .assign 1 (.reg 0 + .reg 1) ;; .call 2 (2 + f) [.reg 1, .const 0, .reg 0] ;;
    .ret (.reg 1)

/-- The bridge program: `bridgeBody f`, then the compiled program at offset 1. -/
def bridgeProgram (P : Program) (f : ℕ) : GI.Machine.Program :=
  ⟨bridgeBody f :: (compile P).shifted 1⟩

theorem bridge_embeds (P : Program) (f : ℕ) : Embeds (bridgeProgram P f) (compile P) 1 :=
  Embeds.of_append (A := [bridgeBody f]) (B := []) (by simp [bridgeProgram])

theorem bridge_proc {P : Program} {f : ℕ} {body : Expr} (hf : P.funs[f]? = some body) :
    (bridgeProgram P f).procs[2 + f]? = some ((funBody (primOff P) body).shift 1) := by
  have := bridge_embeds P f (1 + f) _ (compile_fun hf)
  rwa [show 1 + f + 1 = 2 + f by omega] at this

/-- **The machine part of the bridge.** If every evaluation of the body of user function `f`
on `v` satisfies `Q`, then procedure 0 of the bridge program, started with `v` at the base
address `b` in register 0, keeps the cells below `b`, and returns an address at least `b` that
holds a result `w` with `Q w lc`. Its cost is at most `403 * (lc + len (b + v.size) + 2) ^
(P.degree + 2)`, the bound of `wp_funBody_eval`, plus a term linear in `len (b + v.size)`. -/
theorem wp_bridgeBody {P : Program} {f : ℕ} {body : Expr} (hf : P.funs[f]? = some body)
    {v : Val} {Q : Val → ℕ → Prop} (h : EvalAll P [v] body Q) {b : ℕ} {mem : ℕ → ℕ}
    (hv : ValAt mem b v) :
    WP (bridgeProgram P f) (bridgeBody f) { mem := mem, regs := fun i => [b].getD i 0 }
      (fun o st' c => (∀ a < b, st'.mem a = mem a) ∧ b ≤ o.retVal ∧
        ∃ w lc, ValAt st'.mem o.retVal w ∧ Q w lc ∧
          c ≤ 403 * (lc + len (b + v.size) + 2) ^ (P.degree + 2) +
            100 * (len (b + v.size) + 1)) := by
  unfold bridgeBody
  have hv0 : ValAt ({ mem := mem, regs := fun i => [b].getD i 0 } : State).mem
      (({ mem := mem, regs := fun i => [b].getD i 0 } : State).regs 0) v := by simpa using hv
  -- The size of the instance.
  refine WP.seq' _ (wp_sizeInto (r := 1) hv0) ?_
  rintro st₁ c₁ ⟨rfl, hc₁⟩
  simp only [List.getD_cons_zero] at hc₁
  -- The heap pointer.
  apply seq_assign
  -- The call of user function `f`.
  apply WP.seq
  apply WP.call (bridge_proc hf)
  refine (WP.shift (bridge_embeds P f) (wp_funBody_eval h (hp := b + v.size) ?_ ?_ ?_)).mono ?_
  · simp [machine_simps]
  · simpa [machine_simps] using hv
  · simp [machine_simps]
  rintro o st' c ⟨w, lc, ⟨hQ, -⟩, rfl, vw, mw, hwt, kc⟩
  apply WP.ret
  simp only [machine_simps, Outcome.retVal_returned, List.getD_cons_zero,
    show (1 : ℕ) ≠ 2 by omega, show (0 : ℕ) ≠ 1 by omega, if_false, GI.Machine.len_zero]
  have l1 : len b ≤ len (b + v.size) := len_mono (by omega)
  have l2 : len v.size ≤ len (b + v.size) := len_mono (by omega)
  refine ⟨fun a ha => by simpa using mw a (by omega), by omega, w, lc, vw, hQ, by omega⟩

/-! ### The cost bound -/

/-- The cost arithmetic of the bridge. Write `Y = s + L + 2` for the size `s` of the instance
and the length `L` of the base address. The weight is at most `(A + 1) * Y ^ E`, so the language
cost `lc` is at most `K * (A + 1) ^ D * Y ^ (E * D)`, and the machine bound of
`wp_bridgeBody` is a constant times a power of `Y`. -/
theorem bridge_cost_le {K D A E g s L wt lc lb c : ℕ} (hlb : lb ≤ L + s)
    (hwt : wt ≤ A * (s + 1) ^ E) (hlc : lc ≤ K * (wt + 1) ^ D)
    (hc : c ≤ 403 * (lc + lb + 2) ^ g + 100 * (lb + 1)) (hg : 1 ≤ g) :
    c + L + 2 ≤ (403 * (K * (A + 1) ^ D + 1) ^ g + 101) * (s + L + 2) ^ ((E * D + 1) * g) := by
  obtain ⟨Y, hY⟩ : ∃ Y, s + L + 2 = Y := ⟨_, rfl⟩
  rw [hY]
  have hY1 : 1 ≤ Y := by omega
  -- The weight.
  have h1 : wt + 1 ≤ (A + 1) * Y ^ E := by
    have a1 : (s + 1) ^ E ≤ Y ^ E := Nat.pow_le_pow_left (by omega) _
    have a2 : 1 ≤ Y ^ E := Nat.one_le_pow _ _ hY1
    have a3 : A * (s + 1) ^ E ≤ A * Y ^ E := Nat.mul_le_mul_left _ a1
    rw [add_mul, one_mul]
    omega
  -- The language cost.
  have h2 : lc ≤ K * (A + 1) ^ D * Y ^ (E * D) := by
    calc lc ≤ K * (wt + 1) ^ D := hlc
      _ ≤ K * ((A + 1) * Y ^ E) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 _)
      _ = K * (A + 1) ^ D * Y ^ (E * D) := by rw [mul_pow, ← pow_mul, Nat.mul_assoc]
  -- The base of the machine bound.
  have hpow : ∀ m, 1 ≤ m → Y ≤ Y ^ m := fun m hm => by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ m := Nat.pow_le_pow_right hY1 hm
  have h3 : lc + lb + 2 ≤ (K * (A + 1) ^ D + 1) * Y ^ (E * D + 1) := by
    have a1 : Y ^ (E * D) ≤ Y ^ (E * D + 1) := Nat.pow_le_pow_right hY1 (by omega)
    have a2 := hpow (E * D + 1) (by omega)
    have a3 : K * (A + 1) ^ D * Y ^ (E * D) ≤ K * (A + 1) ^ D * Y ^ (E * D + 1) :=
      Nat.mul_le_mul_left _ a1
    rw [add_mul, one_mul]
    omega
  have h4 : (lc + lb + 2) ^ g ≤ (K * (A + 1) ^ D + 1) ^ g * Y ^ ((E * D + 1) * g) := by
    calc (lc + lb + 2) ^ g ≤ ((K * (A + 1) ^ D + 1) * Y ^ (E * D + 1)) ^ g :=
          Nat.pow_le_pow_left h3 _
      _ = (K * (A + 1) ^ D + 1) ^ g * Y ^ ((E * D + 1) * g) := by rw [mul_pow, ← pow_mul]
  have h5 := hpow ((E * D + 1) * g) (Nat.one_le_iff_ne_zero.mpr (by positivity))
  have h6 : 403 * (lc + lb + 2) ^ g ≤
      403 * ((K * (A + 1) ^ D + 1) ^ g * Y ^ ((E * D + 1) * g)) := Nat.mul_le_mul_left _ h4
  rw [add_mul, Nat.mul_assoc]
  omega

/-! ### The bridge -/

/-- **The bridge.** Let user function `f` of `P` compute, from `enc x`, a value `v` with
`Correct x v` at a language cost of at most `K * ((enc x).wt + 1) ^ D`. If the weight of `enc x`
is at most `A * ((enc x).size + 1) ^ E`, then the bridge program solves `Task.ofVal enc Correct`
in polynomial time. The primitives of `P` need nothing more: each carries its own contract. -/
theorem polyTimeAt_bridgeProgram {α : Type} {enc : α → Val} {Correct : α → Val → Prop}
    {P : Program} {f K D A E : ℕ}
    (hwt : ∀ x, (enc x).wt ≤ A * ((enc x).size + 1) ^ E)
    (h : ∀ x, FunAll P f (enc x) (fun v c => Correct x v ∧ c ≤ K * ((enc x).wt + 1) ^ D)) :
    PolyTimeAt (GI.Cited.Task.ofVal enc Correct) (bridgeProgram P f) := by
  refine ⟨403 * (K * (A + 1) ^ D + 1) ^ (P.degree + 2) + 101, (E * D + 1) * (P.degree + 2),
    PolyTimeWith.of_body (body := bridgeBody f) rfl ?_⟩
  intro x b mem hx
  obtain ⟨body, hf, hb⟩ := h x
  refine (wp_bridgeBody hf hb hx).mono ?_
  rintro o st' c ⟨hbelow, hge, w, lc, vw, ⟨hw, hlc⟩, hc⟩
  exact ⟨hbelow, hge, ⟨w, vw, hw⟩,
    bridge_cost_le (len_add_le' b _) (hwt x) hlc hc (by omega)⟩

/-- `polyTimeAt_bridgeProgram` in the form of a cited algorithm. -/
theorem polyTimeAt_ofVal_of_lang {α : Type} {enc : α → Val} {Correct : α → Val → Prop}
    (P : Program) (f K D A E : ℕ)
    (hwt : ∀ x, (enc x).wt ≤ A * ((enc x).size + 1) ^ E)
    (h : ∀ x, FunAll P f (enc x) (fun v c => Correct x v ∧ c ≤ K * ((enc x).wt + 1) ^ D)) :
    ∃ prog, PolyTimeAt (GI.Cited.Task.ofVal enc Correct) prog :=
  ⟨_, polyTimeAt_bridgeProgram hwt h⟩

/-! ### Small numbers -/

theorem cellWt_le_length_mul {l : List ℕ} {M : ℕ} (h : ∀ a ∈ l, a ≤ M) :
    cellWt l ≤ l.length * (M + 1) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have h1 := GI.Machine.len_le_self a
    have h2 := h a (by simp)
    have h3 := ih fun x hx => h x (by simp [hx])
    simp only [cellWt_cons, List.length_cons, add_mul, one_mul]
    omega

/-- A value whose cells are at most `M` has weight at most `v.size * (M + 1)`. -/
theorem wt_le_of_cells_le {v : Val} {M : ℕ} (h : ∀ a ∈ v.cells, a ≤ M) :
    v.wt ≤ v.size * (M + 1) := cellWt_le_length_mul h

/-- **The bridge, for small numbers.** The same as `polyTimeAt_ofVal_of_lang`, with the weight
condition replaced by the requirement on the tasks of `GI.Cited.Task.ofVal`: every cell of
`enc x` is at most `A * ((enc x).size + 1) ^ E`. -/
theorem polyTimeAt_ofVal_of_lang_cells {α : Type} {enc : α → Val} {Correct : α → Val → Prop}
    (P : Program) (f K D A E : ℕ)
    (hcells : ∀ x, ∀ a ∈ (enc x).cells, a ≤ A * ((enc x).size + 1) ^ E)
    (h : ∀ x, FunAll P f (enc x) (fun v c => Correct x v ∧ c ≤ K * ((enc x).wt + 1) ^ D)) :
    ∃ prog, PolyTimeAt (GI.Cited.Task.ofVal enc Correct) prog := by
  refine polyTimeAt_ofVal_of_lang P f K D (A + 1) (E + 1) (fun x => ?_) h
  obtain ⟨s, hs⟩ : ∃ s, (enc x).size = s := ⟨_, rfl⟩
  have h1 := wt_le_of_cells_le (hcells x)
  rw [hs] at h1 ⊢
  have h2 : 1 ≤ (s + 1) ^ E := Nat.one_le_pow _ _ (by omega)
  calc (enc x).wt ≤ s * (A * (s + 1) ^ E + 1) := h1
    _ ≤ (s + 1) * (A * (s + 1) ^ E + (s + 1) ^ E) :=
        Nat.mul_le_mul (by omega) (by omega)
    _ = (A + 1) * (s + 1) ^ (E + 1) := by ring

/-! ### Example -/

/-- A sanity check: negating a bit, stored as the number 0 or 1, is a task solved in polynomial
time, by the one-function program `1 - x`. -/
example : ∃ prog, PolyTimeAt
    (GI.Cited.Task.ofVal (fun b : Bool => Val.nat (if b then 1 else 0))
      (fun b v => v = Val.nat (if b then 0 else 1))) prog := by
  refine polyTimeAt_ofVal_of_lang_cells ⟨[.arith .sub (.nat 1) (.var 0)], []⟩ 0 10 1 1 0
    (fun b a ha => ?_) (fun b => ⟨_, rfl, ?_⟩)
  · cases b <;> simp at ha <;> rcases ha with rfl | rfl <;> simp
  · refine .arith (Ra := fun v c => v = .nat 1 ∧ c = (Val.nat 1).wt + 1)
      (Rb := fun v c => v = .nat (if b then 1 else 0) ∧ c = (Val.nat (if b then 1 else 0)).wt + 1)
      (.nat ⟨rfl, rfl⟩) (.var (by simp) ⟨rfl, rfl⟩) ?_
    rintro va ca vb cb ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    refine ⟨1, _, rfl, rfl, ?_⟩
    cases b <;> simp [wt_nat, GI.Machine.BinOp.eval, GI.Machine.len_zero]

end GI.Lang
