/-
The compiler theorem: the per-construct lemmas of `Workspace.Lang.Correct`, put together by
induction on `EvalAll`.

The main results are `EvalAll.spec` (any expression, in any context), `wp_funBody_main` (a
user function, run as a procedure) and `bnd_le` (the cost bound in the simple form
`K * (cost + len hp + 2) ^ (D + 2)`).
-/
module

public import Workspace.Lang.Correct

@[expose] public section

namespace GI.Lang

open GI.Machine (Stmt Outcome State WP len len_mono)
open GI.Cited (Val ValAt)

/-- The degree used for programs: one more than the sum of the degrees of the primitives. -/
def Program.degree (P : Program) : ℕ := 1 + (P.prims.map fun p => p.k).sum

theorem Program.consts (P : Program) : Consts P 400 P.degree := by
  refine ⟨le_rfl, by simp [Program.degree], fun p hp => ?_⟩
  have : p.k ≤ (P.prims.map fun p => p.k).sum :=
    List.le_sum_of_mem (List.mem_map_of_mem hp)
  simp only [Program.degree]
  omega

/-- **Compiler correctness.** If every evaluation of `e` finishes with a result satisfying `Q`,
then the compiled code of `e`, in any context `ctx` holding the environment and any first free
register `t ≥ 2` above the context, finishes with such a result, stored at the heap pointer, and
within the bound `Bnd K D`. -/
theorem EvalAll.spec {P : Program} {K D : ℕ} (hc : Consts P K D) {env : List Val} {e : Expr}
    {Q : Val → ℕ → Prop} (h : EvalAll P env e Q) :
    ∀ {ctx : List ℕ} {t : ℕ}, 2 ≤ t → CtxOK ctx t →
      Spec P K D ctx t env (compE (primOff P) ctx t e) Q := by
  induction h with
  | var hi hq => exact fun _ hctx => spec_var hc hctx hi hq
  | nat hq => exact fun _ _ => spec_nat hc _ hq
  | arith _ _ hq iha ihb =>
    exact fun ht hctx => spec_arith hc hctx ht (iha (by omega) (hctx.mono (by omega)))
      (ihb (by omega) (hctx.mono (by omega))) hq
  | nil hq => exact fun _ _ => spec_nil hc hq
  | snoc _ _ hq iha ihb =>
    exact fun ht hctx => spec_snoc hc hctx ht (iha (by omega) (hctx.mono (by omega)))
      (ihb (by omega) (hctx.mono (by omega))) hq
  | length _ hq iha =>
    exact fun ht hctx => spec_length hc hctx ht (iha (by omega) (hctx.mono (by omega))) hq
  | get _ _ hq iha ihb =>
    exact fun ht hctx => spec_get hc hctx ht (iha (by omega) (hctx.mono (by omega)))
      (ihb (by omega) (hctx.mono (by omega))) hq
  | isNat _ hq iha =>
    exact fun ht hctx => spec_isNat hc hctx ht (iha (by omega) (hctx.mono (by omega))) hq
  | ite _ hn _ ihc ihb =>
    exact fun ht hctx => spec_ite hc hctx ht (ihc (by omega) (hctx.mono (by omega))) hn
      fun x cc h => ihb x cc h (by omega) (hctx.mono (by omega))
  | @letE env e body Q Ra _ _ iha ihb =>
    refine fun {ctx t} ht hctx => spec_letE hc hctx ht (iha (by omega) (hctx.mono (by omega)))
      fun v ca h => ihb v ca h (by omega) ?_
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · have := hctx r hr; omega
    · simp at hr; omega
  | call hf _ _ iha ihb =>
    refine fun ht hctx => spec_call hc hctx ht hf (iha (by omega) (hctx.mono (by omega)))
      fun v ca h => ihb v ca h (by omega) ?_
    intro r hr; simp at hr; omega
  | prim hj _ hb iha =>
    exact fun ht hctx => spec_prim hc hctx ht hj (iha (by omega) (hctx.mono (by omega))) hb

/-- The bound `Bnd` in a simpler form. -/
theorem bnd_le (K D h c : ℕ) : Bnd K D h c ≤ K * (c + len h + 2) ^ (D + 2) := by
  unfold Bnd
  rw [pow_add, Nat.mul_assoc K, Nat.mul_comm ((c + len h + 2) ^ D)]
  refine Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _)
    (Nat.pow_le_pow_left (by omega) _))

/-- **A user function, run as a procedure.** Procedure `1 + f` of `compile P` is the code of
user function `f`. Started with its argument `v` stored at the address in register 2 and the heap
pointer `hp` in register 0, above `v`, it returns the new heap pointer `hp + w.size` for a result
`w` stored at `hp`, keeps the memory below `hp`, and costs at most
`(K + 3) * (cost + len hp + 2) ^ (D + 2)`, where `Q w cost`. The language cost pays at least for
the result: `w.wt + 1 ≤ cost`. -/
theorem wp_funBody_main {P : Program} {K D : ℕ} (hc : Consts P K D) {body : Expr} {v : Val}
    {Q : Val → ℕ → Prop} (h : EvalAll P [v] body Q) {st : State} {hp : ℕ}
    (h0 : st.regs 0 = hp) (hval : ValAt st.mem (st.regs 2) v) (hle : st.regs 2 + v.size ≤ hp) :
    WP (compile P) (funBody (primOff P) body) st (fun o st' c => ∃ w cost, Q w cost ∧
      o = .returned (hp + w.size) ∧ ValAt st'.mem hp w ∧ (∀ a < hp, st'.mem a = st.mem a) ∧
      w.wt + 1 ≤ cost ∧ c ≤ (K + 3) * (cost + len hp + 2) ^ (D + 2)) := by
  refine (wp_funBody (h.spec hc (by omega) (by intro r hr; simp at hr; omega)) h0 rfl hval
    hle).mono ?_
  rintro o st' c ⟨w, cb, c', hQ, ho, hw, hm, hc', hk, hwt⟩
  refine ⟨w, cb, hQ, ho, hw, hm, hwt, ?_⟩
  have h1 := (bnd_le K D hp cb)
  have h2 : len (hp + w.size) ≤ len hp + cb := by
    have := len_add_le' hp w.size
    have := w.size_le_wt
    omega
  have h3 : cb + len hp + 2 ≤ (cb + len hp + 2) ^ (D + 2) :=
    Nat.le_self_pow (by omega) _
  rw [hc']
  nlinarith

/-- `wp_funBody_main` with the default constants, and with an evaluation `Eval P [v] body w cost`
for the result: the machine result is a value the language can produce, at that cost. -/
theorem wp_funBody_eval {P : Program} {body : Expr} {v : Val} {Q : Val → ℕ → Prop}
    (h : EvalAll P [v] body Q) {st : State} {hp : ℕ}
    (h0 : st.regs 0 = hp) (hval : ValAt st.mem (st.regs 2) v) (hle : st.regs 2 + v.size ≤ hp) :
    WP (compile P) (funBody (primOff P) body) st (fun o st' c => ∃ w cost,
      (Q w cost ∧ Eval P [v] body w cost) ∧
      o = .returned (hp + w.size) ∧ ValAt st'.mem hp w ∧ (∀ a < hp, st'.mem a = st.mem a) ∧
      w.wt + 1 ≤ cost ∧ c ≤ 403 * (cost + len hp + 2) ^ (P.degree + 2)) :=
  wp_funBody_main P.consts h.withEval h0 hval hle

end GI.Lang
