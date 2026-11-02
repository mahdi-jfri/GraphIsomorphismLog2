import Workspace.Impl.AggCertWt
import Workspace.Impl.AggKerRed
import Workspace.Impl.AggWinProg
import Workspace.Lang.Prims.BlockHom

/-!
# Evaluation with a weight bound and a cost budget

The move program of the certificate phase calls many modules in a row. To keep the cost proofs
short, every value that appears in one move is bounded by one weight `W`, and costs are added
up as budgets.

* `CpEB P env e W C Q`: every evaluation of `e` gives a value with `Q`, of weight at most `W`,
  at cost at most `C`. `CpFB` is the same for a call of a function.
* `CpEB.letE`, `CpEB.call`, `CpEB.ite`, `CpEB.det`: the rules; each step adds `W + 1`.
* `cpG`: one budget for every module that the move program calls, on inputs whose sizes are at
  most `W`: the cited primitives at sizes polynomial in `W`, and a polynomial `10²⁵ W²⁴`
  that dominates the own work of every module.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup encPts gens PointwiseStab Preimage Membership)

/-- Every evaluation of `e` gives a value with `Q`, of weight at most `W`, at cost at most
`C`. -/
def CpEB (P : Program) (env : List Val) (e : Expr) (W C : ℕ) (Q : Val → Prop) : Prop :=
  EvalAll P env e (fun v c => Q v ∧ v.wt ≤ W ∧ c ≤ C)

/-- Every run of `f` on `v` gives a value with `Q`, of weight at most `W`, at cost at most
`C`. -/
def CpFB (P : Program) (f : ℕ) (v : Val) (W C : ℕ) (Q : Val → Prop) : Prop :=
  FunAll P f v (fun w c => Q w ∧ w.wt ≤ W ∧ c ≤ C)

section Rules

variable {P : Program} {env : List Val} {W : ℕ}

theorem CpEB.mono {e : Expr} {C C' : ℕ} {Q Q' : Val → Prop} (h : CpEB P env e W C Q)
    (hC : C ≤ C') (hQ : ∀ v, Q v → Q' v) : CpEB P env e W C' Q' :=
  EvalAll.mono h fun _ _ h => ⟨hQ _ h.1, h.2.1, h.2.2.trans hC⟩

theorem CpFB.mono {f : ℕ} {v : Val} {C C' : ℕ} {Q Q' : Val → Prop} (h : CpFB P f v W C Q)
    (hC : C ≤ C') (hQ : ∀ v, Q v → Q' v) : CpFB P f v W C' Q' :=
  FunAll.mono h fun _ _ h => ⟨hQ _ h.1, h.2.1, h.2.2.trans hC⟩

theorem CpEB.det {e : Expr} {v : Val} {c C : ℕ} {Q : Val → Prop} (h : Det P env e v c)
    (hc : c ≤ C) (hw : v.wt ≤ W) (hq : Q v) : CpEB P env e W C Q :=
  EvalAll.mono h fun _ _ h' => by obtain ⟨rfl, h'⟩ := h'; exact ⟨hq, hw, h'.trans hc⟩

theorem CpFB.det {f : ℕ} {v w : Val} {c C : ℕ} {Q : Val → Prop} (h : FunDet P f v w c)
    (hc : c ≤ C) (hw : w.wt ≤ W) (hq : Q w) : CpFB P f v W C Q :=
  FunAll.mono h fun _ _ h' => by obtain ⟨rfl, h'⟩ := h'; exact ⟨hq, hw, h'.trans hc⟩

theorem CpFB.intro {f : ℕ} {body : Expr} (hf : P.funs[f]? = some body) {v : Val} {C : ℕ}
    {Q : Val → Prop} (h : CpEB P [v] body W C Q) : CpFB P f v W C Q :=
  FunAll.intro hf h

theorem CpEB.letE {e body : Expr} {Ca Cb : ℕ} {Qa Q : Val → Prop} (ha : CpEB P env e W Ca Qa)
    (hb : ∀ v, Qa v → v.wt ≤ W → CpEB P (env ++ [v]) body W Cb Q) :
    CpEB P env (.letE e body) W (Ca + Cb + W + 1) Q :=
  EvalAll.letE ha fun v ca h => EvalAll.mono (hb v h.1 h.2.1) fun w cb h' =>
    ⟨h'.1, h'.2.1, by have := h.2.2; have := h'.2.2; have := h'.2.1; omega⟩

theorem CpEB.call {f : ℕ} {a : Expr} {Ca Cb : ℕ} {Qa Q : Val → Prop}
    (ha : CpEB P env a W Ca Qa) (hb : ∀ v, Qa v → v.wt ≤ W → CpFB P f v W Cb Q) :
    CpEB P env (.call f a) W (Ca + Cb + W + 1) Q :=
  EvalAll.call_funAll ha fun v ca h => FunAll.mono (hb v h.1 h.2.1) fun w cb h' =>
    ⟨h'.1, h'.2.1, by have := h.2.2; have := h'.2.2; have := h'.2.1; omega⟩

theorem CpEB.ite {c t e : Expr} {x cc Ct Ce : ℕ} {Q : Val → Prop} (hc : Det P env c (.nat x) cc)
    (ht : x ≠ 0 → CpEB P env t W Ct Q) (he : x = 0 → CpEB P env e W Ce Q) :
    CpEB P env (.ite c t e) W (cc + Ct + Ce + W + 1) Q := by
  refine EvalAll.ite hc (fun _ _ h => ⟨x, h.1⟩) fun y cc' h => ?_
  obtain ⟨h1, h2⟩ := h
  have hy : y = x := by injection h1
  subst hy
  by_cases hx : y = 0
  · subst hx
    simp only [↓reduceIte]
    exact EvalAll.mono (he rfl) fun w cb h' =>
      ⟨h'.1, h'.2.1, by have := h'.2.2; have := h'.2.1; omega⟩
  · simp only [if_neg hx]
    exact EvalAll.mono (ht hx) fun w cb h' =>
      ⟨h'.1, h'.2.1, by have := h'.2.2; have := h'.2.1; omega⟩

/-- Reading entry `j` of a known list, in the uniform form `(a + 1) (W + 20)`. -/
theorem Det.rd {l : Expr} {vs : List Val} {a ca j : ℕ} {v : Val} (hl : Det P env l (.list vs) ca)
    (hca : ca ≤ a * (W + 20)) (hv : vs[j]? = some v) (hvw : v.wt ≤ W) (hj : j ≤ 15) :
    Det P env (.get l (.nat j)) v ((a + 1) * (W + 20)) :=
  (Det.get' hl (Det.nat j) hv).mono (by rw [Nat.add_mul, Nat.one_mul]; omega)

/-- Reading a variable, in the uniform form. -/
theorem Det.rv {i : ℕ} {v : Val} (h : env[i]? = some v) (hvw : v.wt ≤ W) :
    Det P env (.var i) v (1 * (W + 20)) :=
  (Det.var' h).mono (by omega)

end Rules

/-! ### The budget of one module -/

/-- **The budget of one module call** on inputs of size at most `W`. -/
noncomputable def cpG (hst : PointwiseStab) (hpre : Preimage) (hm : Membership) (W : ℕ) : ℕ :=
  (2 * W + 2) * cardCost hst (2 * W) + (pointwiseStabPrim hst).boundSize (100 * W ^ 4) +
    (preimagePrim hpre).boundSize (1000 * W ^ 4) + ckFindCost hm W + 10 ^ 25 * W ^ 24

end GI.Impl
