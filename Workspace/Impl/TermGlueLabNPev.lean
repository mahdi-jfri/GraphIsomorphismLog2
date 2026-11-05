module

public import Workspace.Impl.TermGlueLabPItem
public import Workspace.Impl.PolyBd

@[expose] public section

/-!
# The label driver: arguments, stages and the cost recursion

Proof of Theorem A.23, the composition of the label driver `tmGLNeF`. The driver
is a chain of `letE`s, each a call on an argument that only reads the environment: variables,
`get`s at fixed positions and short lists. This file gives the three tools of the composition.

* `tmGLNPev env a` evaluates such an argument directly. If it returns `v`, the program
  computes `v` at cost at most `4 ^ tmGLNSz a * (W + 1)`, with `W` the weight of the
  environment (`tmGLN_pev_det`). So every argument costs a fixed multiple of `W + 1`.
* `tmGLN_stage`: one stage `letE (call f a) body`. If the callee meets a contract with cost
  `F B` at the argument bound `B`, and the rest costs `T` of the new environment weight, the
  stage costs `tmGLNStC (tmGLNSz a) F T W`. `tmGLN_last` is the final call.
* `tmGLN_stC_poly`: these bounds stay polynomial when `F` and `T` are polynomial.
-/

namespace GI.Impl

open GI.Lang
open GI.Cited (Val)

/-- The size of an argument expression. -/
def tmGLNSz : Expr → ℕ
  | .var _ => 1
  | .nat k => k + 1
  | .nil => 1
  | .get a i => tmGLNSz a + tmGLNSz i + 1
  | .snoc a b => tmGLNSz a + tmGLNSz b + 1
  | _ => 1

/-- **Direct evaluation** of an argument made of variables, numbers, `get`s and lists. -/
def tmGLNPev (env : List Val) : Expr → Option Val
  | .var i => env[i]?
  | .nat k => some (.nat k)
  | .nil => some (.list [])
  | .get a i => match tmGLNPev env a, tmGLNPev env i with
      | some (.list vs), some (.nat x) => vs[x]?
      | _, _ => none
  | .snoc a b => match tmGLNPev env a, tmGLNPev env b with
      | some (.list vs), some v => some (.list (vs ++ [v]))
      | _, _ => none
  | _ => none

private theorem tmGLN_pev_ar1 {ca cb w a b X : ℕ} (hw : w < ca) (ha : ca ≤ a) (hb : cb ≤ b)
    (hXa : 4 * a ≤ X) (hXb : 4 * b ≤ X) : ca + cb + w + 1 ≤ 4 * X := by omega

private theorem tmGLN_pev_ar2 {ca cb wl wv a b X : ℕ} (hl : wl < ca) (hv : wv < cb)
    (ha : ca ≤ a) (hb : cb ≤ b) (hXa : 4 * a ≤ X) (hXb : 4 * b ≤ X) :
    ca + cb + (wl + 2 * wv + 2) + 1 ≤ 4 * X := by omega

theorem tmGLN_sz_pos : ∀ e : Expr, 1 ≤ tmGLNSz e := by
  intro e; cases e <;> simp only [tmGLNSz] <;> omega

/-- The two products of a binary node: `4 · 4^a (W+1) ≤ 4^a 4^b (W+1)`. -/
private theorem tmGLN_pev_ar3 (a b W : ℕ) (hb : 1 ≤ b) :
    4 * (4 ^ a * (W + 1)) ≤ 4 ^ a * 4 ^ b * (W + 1) := by
  have h4 : 4 ≤ 4 ^ b := Nat.le_self_pow (by omega) 4
  calc 4 * (4 ^ a * (W + 1)) = 4 ^ a * 4 * (W + 1) := by ring
    _ ≤ 4 ^ a * 4 ^ b * (W + 1) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h4)

private theorem tmGLN_pev_ar3' (a b W : ℕ) (ha : 1 ≤ a) :
    4 * (4 ^ b * (W + 1)) ≤ 4 ^ a * 4 ^ b * (W + 1) := by
  have h := tmGLN_pev_ar3 b a W ha
  calc 4 * (4 ^ b * (W + 1)) ≤ 4 ^ b * 4 ^ a * (W + 1) := h
    _ = 4 ^ a * 4 ^ b * (W + 1) := by ring

private theorem tmGLN_pev_ar4 (a b W : ℕ) :
    4 ^ (a + b + 1) * (W + 1) = 4 * (4 ^ a * 4 ^ b * (W + 1)) := by
  rw [pow_succ, pow_add]; ring

/-- **The cost of a direct argument.** -/
theorem tmGLN_pev_det {P : Program} {env : List Val} :
    ∀ (e : Expr) {v : Val}, tmGLNPev env e = some v →
      Det P env e v (4 ^ tmGLNSz e * ((Val.list env).wt + 1))
  | .var i, v, h => by
    refine (Det.var' (P := P) h).mono ?_
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
    have := wt_getElem_lt env i hi
    simp only [tmGLNSz, pow_one]
    omega
  | .nat k, v, h => by
    cases h
    refine (Det.nat k).mono ?_
    have h1 : k + 3 ≤ 4 ^ (k + 1) := by
      have := Nat.lt_pow_self (show 1 < 4 by norm_num) (n := k)
      rw [pow_succ]
      omega
    have h3 : 4 ^ (k + 1) ≤ 4 ^ (k + 1) * ((Val.list env).wt + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    simp only [tmGLNSz]
    omega
  | .nil, v, h => by
    cases h
    refine Det.nil.mono ?_
    have : 4 ≤ (Val.list env).wt := by rw [wt_list_eq]; omega
    simp only [tmGLNSz, pow_one]
    omega
  | .get a i, v, h => by
    simp only [tmGLNPev] at h
    split at h
    · rename_i vs x ha hi
      have da := tmGLN_pev_det (P := P) a ha
      have di := tmGLN_pev_det (P := P) i hi
      obtain ⟨hx, rfl⟩ := List.getElem?_eq_some_iff.mp h
      refine (Det.get da di hx).mono ?_
      have hw : vs[x].wt < 4 ^ tmGLNSz a * ((Val.list env).wt + 1) :=
        lt_of_lt_of_le (wt_getElem_lt vs x hx) (le_of_lt da.wt_lt)
      have h1 := tmGLN_pev_ar3 (tmGLNSz a) (tmGLNSz i) (Val.list env).wt (tmGLN_sz_pos i)
      have h2 := tmGLN_pev_ar3' (tmGLNSz a) (tmGLNSz i) (Val.list env).wt (tmGLN_sz_pos a)
      simp only [tmGLNSz]
      rw [tmGLN_pev_ar4]
      exact tmGLN_pev_ar1 hw le_rfl le_rfl h1 h2
    · cases h
  | .snoc a b, v, h => by
    simp only [tmGLNPev] at h
    split at h
    · rename_i vs w ha hb
      cases h
      have da := tmGLN_pev_det (P := P) a ha
      have db := tmGLN_pev_det (P := P) b hb
      refine (Det.snoc da db).mono ?_
      have hs := wt_list_snoc_le vs w
      have h1 := tmGLN_pev_ar3 (tmGLNSz a) (tmGLNSz b) (Val.list env).wt (tmGLN_sz_pos b)
      have h2 := tmGLN_pev_ar3' (tmGLNSz a) (tmGLNSz b) (Val.list env).wt (tmGLN_sz_pos a)
      simp only [tmGLNSz]
      rw [tmGLN_pev_ar4]
      exact le_trans (by omega) (tmGLN_pev_ar2 da.wt_lt db.wt_lt le_rfl le_rfl h1 h2)
    · cases h
  | .arith _ _ _, v, h => by cases h
  | .length _, v, h => by cases h
  | .isNat _, v, h => by cases h
  | .ite _ _ _, v, h => by cases h
  | .letE _ _, v, h => by cases h
  | .call _ _, v, h => by cases h
  | .prim _ _, v, h => by cases h

/-- The argument bound of a stage with argument size `s` in an environment of weight `W`. -/
def tmGLNArgB (s W : ℕ) : ℕ := 4 ^ s * (W + 1)

theorem tmGLN_pev_wt {env : List Val} {e : Expr} {v : Val} (h : tmGLNPev env e = some v) :
    v.wt ≤ tmGLNArgB (tmGLNSz e) (Val.list env).wt :=
  le_of_lt (tmGLN_pev_det (P := ⟨[], []⟩) e h).wt_lt

/-- **The cost of a stage** `letE (call f a) body`, with `s` the size of `a`, `F` the cost
of the callee and `T` the cost of the rest. -/
def tmGLNStC (s : ℕ) (F T : ℕ → ℕ) (W : ℕ) : ℕ :=
  tmGLNArgB s W + 2 * F (tmGLNArgB s W) + 2 * T (W + 2 * F (tmGLNArgB s W) + 2) + 3

/-- The cost of the final call. -/
def tmGLNLastC (s : ℕ) (F : ℕ → ℕ) (W : ℕ) : ℕ := tmGLNArgB s W + 2 * F (tmGLNArgB s W) + 1

private theorem tmGLN_stage_ar {ca cb wu A C T1 T2 : ℕ} (hca : ca ≤ A + 2 * C + 1)
    (hcb : cb ≤ T1) (hT : T1 ≤ T2) (hu : wu < cb) :
    ca + cb + wu + 1 ≤ A + 2 * C + 2 * T2 + 3 := by omega

/-- **One stage of the driver.** -/
theorem tmGLN_stage {P : Program} {env : List Val} {a body : Expr} {f : ℕ} {vin : Val}
    {R Q : Val → Prop} {F T : ℕ → ℕ} (hT : Monotone T) (ha : tmGLNPev env a = some vin)
    (hf : FunAll P f vin (fun w c => R w ∧ c ≤ F (tmGLNArgB (tmGLNSz a) (Val.list env).wt)))
    (hb : ∀ w, R w → EvalAll P (env ++ [w]) body
      (fun u c => Q u ∧ c ≤ T (Val.list (env ++ [w])).wt)) :
    EvalAll P env (.letE (.call f a) body)
      (fun u c => Q u ∧ c ≤ tmGLNStC (tmGLNSz a) F T (Val.list env).wt) := by
  refine EvalAll.letE (tmGLP_callAll_le (tmGLN_pev_det a ha) le_rfl hf) fun w ca hw => ?_
  obtain ⟨hR, hca, hww⟩ := hw
  refine (hb w hR).wt_lt.mono fun u cb hu => ?_
  obtain ⟨⟨hQ, hcb⟩, hu⟩ := hu
  refine ⟨hQ, ?_⟩
  have hs := wt_list_snoc_le env w
  have hT' := hT (show (Val.list (env ++ [w])).wt ≤ (Val.list env).wt +
    2 * F (tmGLNArgB (tmGLNSz a) (Val.list env).wt) + 2 by omega)
  exact tmGLN_stage_ar (A := tmGLNArgB (tmGLNSz a) (Val.list env).wt) hca hcb hT' hu

/-- **The final call of the driver.** -/
theorem tmGLN_last {P : Program} {env : List Val} {a : Expr} {f : ℕ} {vin : Val}
    {Q : Val → Prop} {F : ℕ → ℕ} (ha : tmGLNPev env a = some vin)
    (hf : FunAll P f vin (fun w c => Q w ∧ c ≤ F (tmGLNArgB (tmGLNSz a) (Val.list env).wt))) :
    EvalAll P env (.call f a)
      (fun u c => Q u ∧ c ≤ tmGLNLastC (tmGLNSz a) F (Val.list env).wt) :=
  (tmGLP_callAll_le (tmGLN_pev_det a ha) le_rfl hf).mono fun _ _ h => ⟨h.1, h.2.1⟩

/-! ### Monotonicity -/

theorem tmGLN_argB_mono (s : ℕ) : Monotone (tmGLNArgB s) := fun _ _ h =>
  Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1)

theorem tmGLN_stC_mono (s : ℕ) {F T : ℕ → ℕ} (hF : Monotone F) (hT : Monotone T) :
    Monotone (tmGLNStC s F T) := by
  intro W V h
  have h1 := tmGLN_argB_mono s h
  have h2 := hF h1
  have h3 := hT (show W + 2 * F (tmGLNArgB s W) + 2 ≤ V + 2 * F (tmGLNArgB s V) + 2 by omega)
  unfold tmGLNStC
  omega

theorem tmGLN_lastC_mono (s : ℕ) {F : ℕ → ℕ} (hF : Monotone F) : Monotone (tmGLNLastC s F) := by
  intro W V h
  have h1 := tmGLN_argB_mono s h
  have h2 := hF h1
  unfold tmGLNLastC
  omega

/-! ### Polynomial bounds -/

/-- `f` is bounded by a polynomial: `f W ≤ C (W + 1) ^ D`. -/
def TmGLNPoly (f : ℕ → ℕ) : Prop := ∃ C D : ℕ, ∀ W, PB (W + 1) (f W) C D

theorem tmGLN_poly_argB (s : ℕ) : ∃ C D : ℕ, ∀ W, PB (W + 1) (tmGLNArgB s W) C D :=
  ⟨4 ^ s, 1, fun W => by simp [PB, tmGLNArgB]⟩

/-- A polynomial `F` applied to `tmGLNArgB s W` is polynomial in `W`. -/
theorem tmGLN_poly_comp {F : ℕ → ℕ} (hF : TmGLNPoly F) {g : ℕ → ℕ} (hg : TmGLNPoly g) :
    TmGLNPoly fun W => F (g W) := by
  obtain ⟨C, D, hC⟩ := hF
  obtain ⟨Cg, Dg, hCg⟩ := hg
  refine ⟨C * (Cg + 1) ^ D, Dg * D, fun W => ?_⟩
  have hX : 1 ≤ W + 1 := by omega
  have h1 : PB (W + 1) (g W + 1) (Cg + 1) Dg := PB.add_const hX (hCg W) 1
  have h2 := PB.smul C (PB.pow h1 D)
  exact PB.mono_le h2 (hC (g W))

theorem tmGLN_poly_add {f g : ℕ → ℕ} (hf : TmGLNPoly f) (hg : TmGLNPoly g) :
    TmGLNPoly fun W => f W + g W := by
  obtain ⟨C, D, hC⟩ := hf
  obtain ⟨C', D', hC'⟩ := hg
  exact ⟨C + C', max D D', fun W => PB.add (by omega) (hC W) (hC' W)⟩

theorem tmGLN_poly_smul (c : ℕ) {f : ℕ → ℕ} (hf : TmGLNPoly f) : TmGLNPoly fun W => c * f W := by
  obtain ⟨C, D, hC⟩ := hf
  exact ⟨c * C, D, fun W => PB.smul c (hC W)⟩

theorem tmGLN_poly_addc {f : ℕ → ℕ} (hf : TmGLNPoly f) (c : ℕ) : TmGLNPoly fun W => f W + c := by
  obtain ⟨C, D, hC⟩ := hf
  exact ⟨C + c, D, fun W => PB.add_const (by omega) (hC W) c⟩

theorem tmGLN_poly_id : TmGLNPoly fun W => W :=
  ⟨1, 1, fun W => by simp [PB]⟩

theorem tmGLN_stC_poly (s : ℕ) {F T : ℕ → ℕ} (hF : TmGLNPoly F) (hT : TmGLNPoly T) :
    TmGLNPoly (tmGLNStC s F T) := by
  have hA : TmGLNPoly (tmGLNArgB s) := tmGLN_poly_argB s
  have hFA := tmGLN_poly_comp hF hA
  have hW : TmGLNPoly fun W => W + 2 * F (tmGLNArgB s W) + 2 :=
    tmGLN_poly_addc (tmGLN_poly_add tmGLN_poly_id (tmGLN_poly_smul 2 hFA)) 2
  have hTW := tmGLN_poly_comp hT hW
  exact tmGLN_poly_addc (tmGLN_poly_add (tmGLN_poly_add hA (tmGLN_poly_smul 2 hFA))
    (tmGLN_poly_smul 2 hTW)) 3

theorem tmGLN_lastC_poly (s : ℕ) {F : ℕ → ℕ} (hF : TmGLNPoly F) :
    TmGLNPoly (tmGLNLastC s F) := by
  have hA : TmGLNPoly (tmGLNArgB s) := tmGLN_poly_argB s
  exact tmGLN_poly_addc (tmGLN_poly_add hA (tmGLN_poly_smul 2 (tmGLN_poly_comp hF hA))) 1

end GI.Impl
