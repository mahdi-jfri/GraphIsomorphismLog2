import Workspace.Impl.TermJHCoef

/-!
# Polynomial bounds and calls in a chain of `let`s

The top programs of the `J`-step call many functions one after the other. This file gives the
two tools for their costs.

* `TmJPoly F`: `F W ≤ K (W + 1)^D` for all `W`, with `K, D` fixed. It is closed under sums,
  products, constants and the substitution `W ↦ K (G W + 1)^D` (`TmJPoly.comp`).
* `tmJ_letCall`: a `let` whose value is a call with a specification, followed by a body with a
  specification for every possible result.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-- **A uniform polynomial bound**: `F W ≤ K (W + 1)^D` for all `W`. -/
def TmJPoly (F : ℕ → ℕ) : Prop := ∃ K D : ℕ, ∀ W, F W ≤ K * (W + 1) ^ D

namespace TmJPoly

theorem const (c : ℕ) : TmJPoly fun _ => c := ⟨c, 0, fun _ => by simp⟩

theorem id : TmJPoly fun W => W := ⟨1, 1, fun W => by simp⟩

theorem mono {F G : ℕ → ℕ} (hG : TmJPoly G) (h : ∀ W, F W ≤ G W) : TmJPoly F := by
  obtain ⟨K, D, hK⟩ := hG
  exact ⟨K, D, fun W => (h W).trans (hK W)⟩

theorem add {F G : ℕ → ℕ} (hF : TmJPoly F) (hG : TmJPoly G) : TmJPoly fun W => F W + G W := by
  obtain ⟨K, D, hK⟩ := hF
  obtain ⟨K', D', hK'⟩ := hG
  refine ⟨K + K', D + D', fun W => ?_⟩
  have h1 : (W + 1) ^ D ≤ (W + 1) ^ (D + D') := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : (W + 1) ^ D' ≤ (W + 1) ^ (D + D') := Nat.pow_le_pow_right (by omega) (by omega)
  have := hK W
  have := hK' W
  have := Nat.mul_le_mul_left K h1
  have := Nat.mul_le_mul_left K' h2
  show F W + G W ≤ (K + K') * (W + 1) ^ (D + D')
  rw [Nat.add_mul]
  omega

theorem mul {F G : ℕ → ℕ} (hF : TmJPoly F) (hG : TmJPoly G) : TmJPoly fun W => F W * G W := by
  obtain ⟨K, D, hK⟩ := hF
  obtain ⟨K', D', hK'⟩ := hG
  refine ⟨K * K', D + D', fun W => ?_⟩
  calc F W * G W ≤ (K * (W + 1) ^ D) * (K' * (W + 1) ^ D') := Nat.mul_le_mul (hK W) (hK' W)
    _ = K * K' * (W + 1) ^ (D + D') := by rw [pow_add]; ring

theorem smul {F : ℕ → ℕ} (c : ℕ) (hF : TmJPoly F) : TmJPoly fun W => c * F W :=
  mul (const c) hF

theorem pow {F : ℕ → ℕ} (hF : TmJPoly F) (n : ℕ) : TmJPoly fun W => F W ^ n := by
  induction n with
  | zero => simpa using const 1
  | succ n ih => simpa [pow_succ] using mul ih hF

/-- **Substitution in a bound `K (x + 1)^D`.** -/
theorem comp {G : ℕ → ℕ} (hG : TmJPoly G) (K D : ℕ) :
    TmJPoly fun W => K * (G W + 1) ^ D :=
  smul K (pow (add hG (const 1)) D)

/-- Substitution in any monotone function with a polynomial bound. -/
theorem comp_mono {F G : ℕ → ℕ} (hF : TmJPoly F) (_hmono : Monotone F) (hG : TmJPoly G) :
    TmJPoly fun W => F (G W) := by
  obtain ⟨K, D, hK⟩ := hF
  exact mono (comp hG K D) fun W => (hK (G W))

end TmJPoly

/-- `K (x + 1)^D` is monotone in `x`. -/
theorem tmJ_powBd_mono (K D : ℕ) : Monotone fun x : ℕ => K * (x + 1) ^ D :=
  fun _ _ h => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)

/-- **A `let` of a call with a specification.** -/
theorem tmJ_letCall {P : Program} {env : List Val} {a body : Expr} {f : ℕ} {v : Val}
    {ca B C : ℕ} {R Q : Val → Prop} (ha : Det P env a v ca)
    (hf : FunAll P f v (fun w c => R w ∧ c ≤ B))
    (hb : ∀ w, R w → w.wt < B → EvalAll P (env ++ [w]) body (fun u c => Q u ∧ c ≤ C)) :
    EvalAll P env (.letE (.call f a) body) (fun u c => Q u ∧ c ≤ ca + 2 * B + 2 * C + 2) :=
  EvalAll.letE (tmJH_callA ha hf) fun w cw hw =>
    (hb w hw.1 hw.2.1).wt_lt.mono fun u cu hu => ⟨hu.1.1, by have := hw.2.2; omega⟩

/-- **A `let` of a deterministic value.** -/
theorem tmJ_letDet {P : Program} {env : List Val} {a body : Expr} {v : Val} {ca C : ℕ}
    {Q : Val → Prop} (ha : Det P env a v ca)
    (hb : EvalAll P (env ++ [v]) body (fun u c => Q u ∧ c ≤ C)) :
    EvalAll P env (.letE a body) (fun u c => Q u ∧ c ≤ ca + 2 * C + 1) :=
  EvalAll.letE ha fun w cw hw => by
    obtain ⟨rfl, hc⟩ := hw
    exact hb.wt_lt.mono fun u cu hu => ⟨hu.1.1, by omega⟩

/-- **A final call with a specification.** -/
theorem tmJ_lastCall {P : Program} {env : List Val} {a : Expr} {f : ℕ} {v : Val}
    {ca B : ℕ} {R : Val → Prop} (ha : Det P env a v ca)
    (hf : FunAll P f v (fun w c => R w ∧ c ≤ B)) :
    EvalAll P env (.call f a) (fun u c => R u ∧ c ≤ ca + 2 * B + 1) :=
  (tmJH_callA ha hf).mono fun _ _ h => ⟨h.1, h.2.2⟩

end GI.Impl
