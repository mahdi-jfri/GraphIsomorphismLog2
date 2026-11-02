import Workspace.Assembly.Refinement
import Workspace.AutCardFromOut
import Workspace.Axioms.GMP
import Workspace.Axioms.SimpleValuationDegree

/-!
# The final reduction

`GI.Assembly.final`: a `GI.Lang` program with the three obligations of
`Workspace/Assembly/Refinement.lean` gives `GI.Statement.GraphIsomorphismInQuasipolynomialTime`.

* (a) `Implements .solve Pg fs w`: function `fs` implements `Solve` at the parameters `P₀`;
* (b) `GraphWrapper Pg fm fs`: function `fm` is Algorithm 1 around `fs`;
* (c) `WorkBound w`: the work function satisfies the work bounds of Section 7.4.

The proof follows the main function on the input value of two graphs `G, H` on `n` vertices.
Building the pair state costs a polynomial in `n` (b). `Solve` returns the value of the answer
of a run `r` on the pair state at cost `K (r.total w + …)^d` (a). Theorem 1.1 at stage 1
(`thm_main_graph_stage1''`, with (c)) bounds `r.total w` by `exp(C' (log(n+2))²)`, and every run
returns the exact answer, so the conversion gives a correct output (b). A polynomial in
`exp(C' (log(n+2))²)` and `n` is again at most `exp(C'' (log(n+2))²)` (`qp_poly`), and `glue`
(`Workspace/Lang/Glue.lean`) turns the language program into a machine program.

`final_of_axioms` discharges the cited inputs by the axioms of `Workspace/Axioms/`.
-/

namespace GI.Assembly

open GI.Algorithm GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val)

/-! ### Quasipolynomial bounds -/

theorem log_two_le_log (n : ℕ) : Real.log 2 ≤ Real.log ((n : ℝ) + 2) :=
  Real.log_le_log (by norm_num) (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)

/-- `(log 2)² ≤ (log(n+2))²`. -/
theorem log_two_sq_le (n : ℕ) : Real.log 2 ^ 2 ≤ Real.log ((n : ℝ) + 2) ^ 2 :=
  pow_le_pow_left₀ (Real.log_pos (by norm_num)).le (log_two_le_log n) 2

/-- A bound `exp(C L²)` with `C ≤ C'` is at most `exp(C' L²)`. -/
theorem exp_mono_const {C C' : ℝ} (h : C ≤ C') (n : ℕ) :
    Real.exp (C * Real.log ((n : ℝ) + 2) ^ 2) ≤ Real.exp (C' * Real.log ((n : ℝ) + 2) ^ 2) :=
  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h (sq_nonneg _))

/-- The sum of two quasipolynomial bounds is a quasipolynomial bound. -/
theorem qp_add (C₁ C₂ : ℝ) : ∃ C : ℝ, ∀ (n : ℕ) (x y : ℝ),
    x ≤ Real.exp (C₁ * Real.log ((n : ℝ) + 2) ^ 2) →
    y ≤ Real.exp (C₂ * Real.log ((n : ℝ) + 2) ^ 2) →
    x + y ≤ Real.exp (C * Real.log ((n : ℝ) + 2) ^ 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max C₁ C₂ + 1 / Real.log 2, fun n x y hx hy => ?_⟩
  set L := Real.log ((n : ℝ) + 2)
  set M := max C₁ C₂
  have hx' := hx.trans (exp_mono_const (le_max_left C₁ C₂) n)
  have hy' := hy.trans (exp_mono_const (le_max_right C₁ C₂) n)
  -- `log 2 ≤ L² / log 2`, since `(log 2)² ≤ L²`.
  have h2 : Real.log 2 ≤ 1 / Real.log 2 * L ^ 2 := by
    rw [one_div_mul_eq_div, le_div_iff₀ hl]
    nlinarith [log_two_sq_le n]
  calc x + y ≤ 2 * Real.exp (M * L ^ 2) := by linarith
    _ = Real.exp (Real.log 2 + M * L ^ 2) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ Real.exp ((M + 1 / Real.log 2) * L ^ 2) := by
        apply Real.exp_le_exp.mpr; nlinarith

/-- **A polynomial in a quasipolynomial bound and in `n` is a quasipolynomial bound.** -/
theorem qp_poly (K d : ℕ) (C : ℝ) : ∃ C' : ℝ, ∀ (n : ℕ) (x : ℝ), 0 ≤ x →
    x ≤ Real.exp (C * Real.log ((n : ℝ) + 2) ^ 2) →
    (K : ℝ) * (x + n + 1) ^ d ≤ Real.exp (C' * Real.log ((n : ℝ) + 2) ^ 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨C₀, hC₀⟩ := qp_add C (1 / Real.log 2)
  refine ⟨d * C₀ + Real.log (K + 1) / Real.log 2 ^ 2, fun n x hx0 hx => ?_⟩
  set L := Real.log ((n : ℝ) + 2)
  have hL : Real.log 2 ≤ L := log_two_le_log n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- `n + 1 ≤ n + 2 = exp L ≤ exp(L² / log 2)`.
  have hn : (n : ℝ) + 1 ≤ Real.exp (1 / Real.log 2 * L ^ 2) := by
    have e : Real.exp L = (n : ℝ) + 2 := Real.exp_log (by linarith)
    have h1 : L ≤ 1 / Real.log 2 * L ^ 2 := by
      rw [one_div_mul_eq_div, le_div_iff₀ hl]; nlinarith
    have := Real.exp_le_exp.mpr h1
    linarith
  have hs : x + n + 1 ≤ Real.exp (C₀ * L ^ 2) := by
    have := hC₀ n x ((n : ℝ) + 1) hx hn
    linarith
  have hpow : (x + n + 1) ^ d ≤ Real.exp (d * C₀ * L ^ 2) := by
    calc (x + n + 1) ^ d ≤ Real.exp (C₀ * L ^ 2) ^ d :=
          pow_le_pow_left₀ (by linarith) hs d
      _ = Real.exp (d * C₀ * L ^ 2) := by rw [← Real.exp_nat_mul]; ring_nf
  -- `K ≤ K + 1 = exp(log(K+1)) ≤ exp(log(K+1) L² / (log 2)²)`.
  have hK : (K : ℝ) ≤ Real.exp (Real.log (K + 1) / Real.log 2 ^ 2 * L ^ 2) := by
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    have hlog : 0 ≤ Real.log ((K : ℝ) + 1) := Real.log_nonneg (by linarith)
    have h1 : Real.log ((K : ℝ) + 1) ≤ Real.log (K + 1) / Real.log 2 ^ 2 * L ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left (log_two_sq_le n) hlog
    have := Real.exp_le_exp.mpr h1
    rw [Real.exp_log (by linarith)] at this
    linarith
  calc (K : ℝ) * (x + n + 1) ^ d
      ≤ Real.exp (Real.log (K + 1) / Real.log 2 ^ 2 * L ^ 2) * Real.exp (d * C₀ * L ^ 2) :=
        mul_le_mul hK hpow (pow_nonneg (by linarith) d) (Real.exp_pos _).le
    _ = Real.exp ((d * C₀ + Real.log (K + 1) / Real.log 2 ^ 2) * L ^ 2) := by
        rw [← Real.exp_add]; ring_nf

/-! ### The main function -/

/-- **The evaluation of `mainBody`.** If building, solving and converting have specifications,
then every evaluation of `mainBody fb fs fc` on `[inp]` goes through one result of each, and
costs at most `20 (wt inp + cost of the three calls + 10)`. -/
theorem mainBody_spec {Pg : Program} {fb fs fc : ℕ} {inp : Val}
    {Rb : Val → ℕ → Prop} {Rs : Val → Val → ℕ → Prop} {Rc : Val → Val → ℕ → Prop}
    (hb : FunAll Pg fb inp Rb) (hs : ∀ v cb, Rb v cb → FunAll Pg fs v (Rs v))
    (hc : ∀ v cb u cs, Rb v cb → Rs v u cs → FunAll Pg fc (.list [inp, u]) (Rc u)) :
    EvalAll Pg [inp] (mainBody fb fs fc) fun out cost =>
      ∃ v cb u cs cc, Rb v cb ∧ Rs v u cs ∧ Rc u out cc ∧
        cost ≤ 20 * (inp.wt + cb + cs + cc + 10) := by
  unfold mainBody
  refine EvalAll.letE (Ra := fun v c => ∃ cb, Rb v cb ∧ v.wt < cb ∧
      c ≤ inp.wt + 1 + cb + v.wt + 1)
    (EvalAll.call_funAll (Det.var' (P := Pg) (env := [inp]) (i := 0) rfl) fun v' ca h => ?_)
    fun v ca hv => ?_
  · obtain ⟨hv', hca⟩ := h
    rw [hv']
    exact hb.wt_lt.mono fun v cb ⟨h1, h2⟩ => ⟨cb, h1, h2, by omega⟩
  obtain ⟨cb, hv, hvb, hca⟩ := hv
  refine EvalAll.letE (Ra := fun u c => ∃ cs, Rs v u cs ∧ u.wt < cs ∧
      c ≤ v.wt + 1 + cs + u.wt + 1)
    (EvalAll.call_funAll (Det.var' (P := Pg) (env := [inp] ++ [v]) (i := 1) rfl)
      fun v' ca' h => ?_) fun u ca2 hu => ?_
  · obtain ⟨hv', hca'⟩ := h
    rw [hv']
    exact (hs v cb hv).wt_lt.mono fun u cs ⟨h1, h2⟩ => ⟨cs, h1, h2, by omega⟩
  obtain ⟨cs, hu, hus, hca2⟩ := hu
  have hm := Det.mk2 (P := Pg) (env := [inp] ++ [v] ++ [u])
    (Det.var' (i := 0) (v := inp) rfl) (Det.var' (i := 2) (v := u) rfl)
  refine EvalAll.call_funAll hm fun l cl hl => ?_
  obtain ⟨hl', hcl⟩ := hl
  rw [hl']
  refine (hc v cb u cs hv hu).wt_lt.mono fun out cc ⟨h1, h2⟩ => ⟨v, cb, u, cs, cc, hv, hu, h1, ?_⟩
  have := wt_list2_le inp u
  omega

/-! ### The reduction -/

/-- **The final reduction.** Let `Pg` be a `GI.Lang` program with

* (a) `Implements .solve Pg fs w`: function `fs` implements `Solve` at the parameters `P₀`;
* (b) `GraphWrapper Pg fm fs`: function `fm` is Algorithm 1 around `fs`;
* (c) `WorkBound w`: the work function `w` satisfies the work bounds of Section 7.4.

Assume the cited results `GMPOutBound` ([GMP, Lemma 7.7]) and `SimpleValuationDegree`. Then
graph isomorphism is in quasipolynomial time. -/
theorem final (hOut : GI.Cited.GMPOutBound) (hLie : GI.Cited.SimpleValuationDegree)
    {Pg : Program} {fm fs : ℕ} {w : Node P₀ → ℝ}
    (ha : Implements .solve Pg fs w) (hb : GraphWrapper Pg fm fs) (hc : WorkBound w) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime := by
  classical
  obtain ⟨Ka, da, hsolve⟩ := ha
  obtain ⟨fb, fc, hfm, ⟨Kb, db, hbuild⟩, ⟨Kc, dc, hconv⟩⟩ := hb
  obtain ⟨cw, hcw, hw⟩ := hc
  obtain ⟨C₁, hC₁⟩ := thm_main_graph_stage1'' (GI.autCardLeSq_of_outBound hOut) hLie hw hcw
  -- The constants of the bound, chosen before `n`.
  obtain ⟨CB, hCB⟩ := qp_poly Kb db 0
  obtain ⟨CV, hCV⟩ := qp_add C₁ CB
  obtain ⟨CS, hCS⟩ := qp_poly Ka da CV
  obtain ⟨CC, hCC⟩ := qp_poly Kc dc CS
  obtain ⟨CI, hCI⟩ := qp_poly 30 3 0
  obtain ⟨C₂, hC₂⟩ := qp_add CI CB
  obtain ⟨C₃, hC₃⟩ := qp_add C₂ CS
  obtain ⟨C₄, hC₄⟩ := qp_add C₃ CC
  obtain ⟨CF, hCF⟩ := qp_poly 200 1 C₄
  refine glue Pg fm _ hfm CF fun n G H => ?_
  have hexp0 : (0 : ℝ) ≤ Real.exp (0 * Real.log ((n : ℝ) + 2) ^ 2) := (Real.exp_pos _).le
  refine (mainBody_spec (hbuild n G H).wt_lt
    (Rs := fun v u cs => (∃ (A : Set (Perm (Fin n × Fin n)))
      (r : Run P₀ .solve (graphState G H) none A), AnswerVal (pairEnum n) u A ∧
        (cs : ℝ) ≤ Ka * (r.total w + v.wt + 1) ^ da) ∧ u.wt < cs)
    (Rc := fun u out cc => AnswerOK G H out ∧ cc ≤ Kc * (u.wt + n + 1) ^ dc)
    (fun v cb hv => (hsolve (graphState G H) (n * n) (pairEnum n) pairCode pairCode_injective v
      hv.1.1).wt_lt)
    (fun v cb u cs hv hu => ?_)).mono ?_
  · obtain ⟨⟨A, r, hA, -⟩, -⟩ := hu
    rw [r.exact] at hA
    exact hconv n G H u hA
  rintro out cost ⟨v, cb, u, cs, cc, ⟨⟨-, hcb⟩, hvb⟩, ⟨⟨A, r, -, hcs⟩, hus⟩, ⟨hok, hcc⟩, hcost⟩
  refine ⟨hok, ?_⟩
  set L := Real.log ((n : ℝ) + 2)
  -- The cost of each part, as a quasipolynomial bound.
  have hT := (hC₁ n G H r).2.2.2
  have hT0 : 0 ≤ r.total w := r.total_nonneg hw.nonneg
  have hB : (cb : ℝ) ≤ Real.exp (CB * L ^ 2) := by
    have := hCB n 0 le_rfl hexp0
    rw [zero_add] at this
    exact le_trans (by exact_mod_cast hcb) this
  have hvwt : (v.wt : ℝ) ≤ cb := by exact_mod_cast hvb.le
  have hV := hCV n (r.total w) v.wt hT (hvwt.trans hB)
  have hS : (cs : ℝ) ≤ Real.exp (CS * L ^ 2) := by
    refine hcs.trans (le_trans ?_ (hCS n (r.total w + v.wt) (by positivity) hV))
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have hv0 := (Nat.cast_nonneg v.wt : (0 : ℝ) ≤ v.wt)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) da)
      (Nat.cast_nonneg _)
  have huwt : (u.wt : ℝ) ≤ cs := by exact_mod_cast hus.le
  have hC : (cc : ℝ) ≤ Real.exp (CC * L ^ 2) := by
    have := hCC n u.wt (Nat.cast_nonneg _) (huwt.trans hS)
    refine le_trans ?_ this
    exact_mod_cast hcc
  have hI : ((inputVal G H).wt : ℝ) ≤ Real.exp (CI * L ^ 2) := by
    have := hCI n 0 le_rfl hexp0
    rw [zero_add] at this
    refine le_trans ?_ this
    exact_mod_cast wt_inputVal_le G H
  have hsum := hC₄ n _ _ (hC₃ n _ _ (hC₂ n _ _ hI hB) hS) hC
  have hfin := hCF n _ (by positivity) hsum
  refine le_trans ?_ hfin
  have hcost' : (cost : ℝ) ≤ 20 * ((inputVal G H).wt + cb + cs + cc + 10) := by
    exact_mod_cast hcost
  have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  push_cast at hfin ⊢
  nlinarith

/-- **The final reduction, with the cited inputs taken from the axioms** `GI.Axioms.gmpOutBound`
and `GI.Axioms.simpleValuationDegree`. What remains are the obligations (a), (b), (c). -/
theorem final_of_axioms {Pg : Program} {fm fs : ℕ} {w : Node P₀ → ℝ}
    (ha : Implements .solve Pg fs w) (hb : GraphWrapper Pg fm fs) (hc : WorkBound w) :
    GI.Statement.GraphIsomorphismInQuasipolynomialTime :=
  final GI.Axioms.gmpOutBound GI.Axioms.simpleValuationDegree ha hb hc

end GI.Assembly
