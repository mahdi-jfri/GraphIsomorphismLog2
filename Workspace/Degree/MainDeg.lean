module

public import Workspace.Degree.StringFinal
public import Workspace.Lang.Glue
public import Workspace.Proved.SSMembership

@[expose] public section

/-!
# The main theorem in degree form, from the graph theorem

`graphIsomorphismInDegreeTime_of` proves `GI.Statement.GraphIsomorphismInDegreeTime` from
`GraphSolver fs` (`Degree/Interface.lean`), the contract of the graph program.

* The program `degFinal fs` is `strProgFinal` followed by the graph functions `fs b fd j`, with
  `b` the length of `strProgFinal`, the string solver at `fd = dgb 40`, and `Membership` at the
  primitive `1` of the final program of the general algorithm.
* `StringSolver (degFinal fs) (dgb 40)` holds because `stringSolver_final` moves to extensions.
* `glueDeg` is the glue of `Lang/Glue.lean` with the bound `exp(C log(n + 2) log(d + 2))` in place
  of `exp(C log(n + 2)²)`. The input layout and the output are those of `glue`, so the conversion
  to the machine needs no new work. Only the bound changes (`deg_absorb`).
-/

namespace GI.Degree

open GI.Lang GI.Cited

/-- **A polynomial in a bound `exp(C log(n + 2) log(d + 2))` and in `n` is again such a bound.**
The proof is that of `quasi_absorb`, with `log(n + 2) log(d + 2)` in place of `log(n + 2)²`. It
uses `log 2 ≤ log(d + 2)` to bound the powers of `n + 2`. -/
theorem deg_absorb (A E : ℕ) (C : ℝ) : ∃ C' : ℝ, ∀ (n d lc : ℕ),
    (lc : ℝ) ≤ Real.exp (C * Real.log ((n : ℝ) + 2) * Real.log ((d : ℝ) + 2)) →
    ((A * (lc + 4 * (2 * n * n + 1) + 10) ^ E : ℕ) : ℝ) ≤
      Real.exp (C' * Real.log ((n : ℝ) + 2) * Real.log ((d : ℝ) + 2)) := by
  have hl₀ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨l₀, hl⟩ : ∃ l₀, Real.log 2 = l₀ := ⟨_, rfl⟩
  rw [hl] at hl₀
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, |C| + 2 / l₀ = C₀ := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, ((A : ℝ) + 1) * 15 ^ E = K₀ := ⟨_, rfl⟩
  have hK1 : 1 ≤ K₀ := by
    rw [← hK₀]
    have : (1 : ℝ) ≤ 15 ^ E := one_le_pow₀ (by norm_num)
    nlinarith [(Nat.cast_nonneg A : (0 : ℝ) ≤ A)]
  refine ⟨E * C₀ + Real.log K₀ / l₀ ^ 2, fun n d lc hlc => ?_⟩
  obtain ⟨L, hL⟩ : ∃ L, Real.log ((n : ℝ) + 2) = L := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, Real.log ((d : ℝ) + 2) = M := ⟨_, rfl⟩
  rw [hL, hM] at hlc ⊢
  have hLl : l₀ ≤ L := by
    rw [← hl, ← hL]
    exact Real.log_le_log (by norm_num) (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  have hMl : l₀ ≤ M := by
    rw [← hl, ← hM]
    exact Real.log_le_log (by norm_num) (by have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d); linarith)
  have hL0 : 0 < L := lt_of_lt_of_le hl₀ hLl
  have hM0 : 0 < M := lt_of_lt_of_le hl₀ hMl
  have hLM : 0 < L * M := mul_pos hL0 hM0
  have hC₀0 : 0 ≤ C₀ := by rw [← hC₀]; positivity
  -- The two parts of the base are at most `exp (C₀ L M)`.
  have h1 : (lc : ℝ) ≤ Real.exp (C₀ * (L * M)) := by
    refine hlc.trans (Real.exp_le_exp.mpr ?_)
    rw [← hC₀, mul_assoc]
    have := le_abs_self C
    have : 0 ≤ 2 / l₀ := by positivity
    nlinarith
  have h2 : ((n : ℝ) + 2) ^ 2 ≤ Real.exp (C₀ * (L * M)) := by
    have e : ((n : ℝ) + 2) ^ 2 = Real.exp (2 * L) := by
      rw [show 2 * L = L + L by ring, Real.exp_add, ← hL,
        Real.exp_log (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)]
      ring
    rw [e]
    refine Real.exp_le_exp.mpr ?_
    have h3 : 2 * L ≤ 2 / l₀ * (L * M) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl₀]
      nlinarith
    rw [← hC₀]
    have : 0 ≤ |C| * (L * M) := by positivity
    nlinarith
  have hM1 : 1 ≤ Real.exp (C₀ * (L * M)) := Real.one_le_exp (by positivity)
  have hbase : ((lc + 4 * (2 * n * n + 1) + 10 : ℕ) : ℝ) ≤ 15 * Real.exp (C₀ * (L * M)) := by
    push_cast
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    nlinarith
  -- Now raise to the power `E` and absorb the constant.
  have hpow : ((A * (lc + 4 * (2 * n * n + 1) + 10) ^ E : ℕ) : ℝ) ≤
      K₀ * Real.exp (E * C₀ * (L * M)) := by
    rw [← hK₀, show (E : ℝ) * C₀ * (L * M) = E * (C₀ * (L * M)) by ring, Real.exp_nat_mul]
    push_cast
    have hb0 : (0 : ℝ) ≤ (lc : ℝ) + 4 * (2 * n * n + 1) + 10 := by positivity
    have hb := hbase
    push_cast at hb
    calc (A : ℝ) * ((lc : ℝ) + 4 * (2 * n * n + 1) + 10) ^ E
        ≤ ((A : ℝ) + 1) * (15 * Real.exp (C₀ * (L * M))) ^ E :=
          mul_le_mul (by linarith) (pow_le_pow_left₀ hb0 hb E) (by positivity) (by positivity)
      _ = ((A : ℝ) + 1) * 15 ^ E * Real.exp (C₀ * (L * M)) ^ E := by ring
  have hK : K₀ ≤ Real.exp (Real.log K₀ / l₀ ^ 2 * (L * M)) := by
    calc K₀ = Real.exp (Real.log K₀) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (Real.log K₀ / l₀ ^ 2 * (L * M)) := by
        refine Real.exp_le_exp.mpr ?_
        have hlog : 0 ≤ Real.log K₀ := Real.log_nonneg hK1
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : l₀ ^ 2 ≤ L * M := by nlinarith
        nlinarith
  calc ((A * (lc + 4 * (2 * n * n + 1) + 10) ^ E : ℕ) : ℝ)
      ≤ K₀ * Real.exp (E * C₀ * (L * M)) := hpow
    _ ≤ Real.exp (Real.log K₀ / l₀ ^ 2 * (L * M)) * Real.exp (E * C₀ * (L * M)) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_pos _).le
    _ = Real.exp ((E * C₀ + Real.log K₀ / l₀ ^ 2) * L * M) := by
        rw [← Real.exp_add]; ring_nf

/-- **The glue, in degree form.** If for all `n`, `d` and graphs `G`, `H` on `Fin n` with degrees
at most `d`, function `f` of `P` on `inputVal G H` gives a correct answer at a language cost of at
most `exp(C log(n + 2) log(d + 2))`, then `GraphIsomorphismInDegreeTime` holds. The machine
program is `glueProgram P f` of `Lang/Glue.lean`, and `glue_run` gives its run. -/
theorem glueDeg (P : Program) (f : ℕ) (C : ℝ)
    (h : ∀ (n d : ℕ) (G H : SimpleGraph (Fin n)), GI.Statement.DegreeAtMost G d →
      GI.Statement.DegreeAtMost H d → FunAll P f (inputVal G H) fun w cost => AnswerOK G H w ∧
        (cost : ℝ) ≤ Real.exp (C * Real.log ((n : ℝ) + 2) * Real.log ((d : ℝ) + 2))) :
    GI.Statement.GraphIsomorphismInDegreeTime := by
  obtain ⟨C', hC'⟩ := deg_absorb 1000 (P.degree + 2) C
  refine ⟨glueProgram P f, C', fun n d G H mem hm hG hH => ?_⟩
  obtain ⟨body, hf, hev⟩ := h n d G H hG hH
  obtain ⟨fuel, mem', r, cost, hrun, hout, lc, hlc, hcost⟩ := glue_run hf hm
    (Q := fun c => (c : ℝ) ≤ Real.exp (C * Real.log ((n : ℝ) + 2) * Real.log ((d : ℝ) + 2))) hev
  refine ⟨fuel, mem', r, cost, hrun, hout, ?_⟩
  calc (cost : ℝ) ≤ ((1000 * (lc + 4 * (2 * n * n + 1) + 10) ^ (P.degree + 2) : ℕ) : ℝ) := by
        exact_mod_cast hcost
    _ ≤ Real.exp (C' * Real.log ((n : ℝ) + 2) * Real.log ((d : ℝ) + 2)) := hC' n d lc hlc

/-- **The final program**: `strProgFinal`, then the graph functions `fs b (dgb 40) 1` at
`b = |strProgFinal.funs|`. -/
noncomputable def degFinal (fs : ℕ → ℕ → ℕ → List Expr) : Program :=
  ⟨strProgFinal.funs ++ fs strProgFinal.funs.length (dgb 40) 1, strProgFinal.prims⟩

theorem degFinal_sub (fs : ℕ → ℕ → ℕ → List Expr) : strProgFinal.Sub (degFinal fs) :=
  ⟨List.prefix_append _ _, List.prefix_refl _⟩

theorem degFinal_hasAt (fs : ℕ → ℕ → ℕ → List Expr) :
    (degFinal fs).HasAt strProgFinal.funs.length (fs strProgFinal.funs.length (dgb 40) 1) := by
  have h := Program.hasAt_append strProgFinal.funs (fs strProgFinal.funs.length (dgb 40) 1) []
    strProgFinal.prims
  rwa [List.append_nil] at h

/-- `Membership` is the primitive `1` of the final program. -/
theorem degFinal_membership (fs : ℕ → ℕ → ℕ → List Expr) :
    (degFinal fs).prims[1]? = some (membershipPrim GI.Proved.membership) := rfl

/-- **The main theorem in degree form, from the graph theorem.** -/
theorem graphIsomorphismInDegreeTime_of {fs : ℕ → ℕ → ℕ → List Expr} (h : GraphSolver fs) :
    GI.Statement.GraphIsomorphismInDegreeTime := by
  obtain ⟨C, hC⟩ := h GI.Proved.membership (degFinal fs) _ _ _ (degFinal_hasAt fs)
    (degFinal_membership fs) (stringSolver_final.of_sub (degFinal_sub fs))
  exact glueDeg (degFinal fs) _ C hC

end GI.Degree
