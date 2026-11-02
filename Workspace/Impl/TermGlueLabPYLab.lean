import Workspace.Impl.TermGlueLabPXLab

/-!
# The labels of the aligned rows `y'`

Step 3 of the label program. With a lift `k(τ)` of `τ` (the lift program), the
aligned rows are `y'_i = y_i^{k_i(τ)⁻¹}`, so `y'_i^{k_i(τ)} = y_i`. For every row `i` the search
of `TermGlueLabPFind` with `w = k_i(τ)` and `l = i` reads the stored cosets `Iso_H(x_j, y_i)`
and returns the first row `x_j` of the type of `y'_i` with `n ∈ N`, `x_j^n = y'_i`
(`tmGLPYLab_spec`). The rows `y'_i` are never formed: only `k_i(τ)` enters. No string call.
-/

namespace GI.Impl

open GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens Membership NormalizedFactor)

variable {n : ℕ} {Ω : Type} [RAct (Perm (Fin n)) Ω]

/-- One step, on `[a, i, acc]` with `a = [gens N, vs, q, [k_i]]`. -/
def tmGLPYStep (find : ℕ) : Expr :=
  .snoc (arg 2) (.call find (mk2 (mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1))
    (.get (arg 0) (.nat 2)) (arg 1)) (.get (.get (arg 0) (.nat 3)) (arg 1))))

/-- **The labels of `y'`** (3 functions), with the search at `find`. -/
def tmGLPYLabFuns (b find : ℕ) : List Expr :=
  loopFuns b (.get (.var 0) (.nat 2)) .nil (tmGLPYStep find)

theorem length_tmGLPYLabFuns (b find : ℕ) : (tmGLPYLabFuns b find).length = 3 := rfl

/-- The state after the rows `k < i`. -/
def TmGLPYInv (N : Subgroup (Perm (Fin n))) {q : ℕ} (X Z : Fin q → Ω) (B i : ℕ) (acc : Val) :
    Prop :=
  ∃ l : List Val, acc = .list l ∧ l.length = i ∧ (∀ v ∈ l, v.wt ≤ B) ∧
    ∀ k : Fin q, k.1 < i → ∃ v, l[k.1]? = some v ∧ TmGLPFindOut N X (Z k) v

/-- The result: the search result for every row. -/
def TmGLPYOut (N : Subgroup (Perm (Fin n))) {q : ℕ} (X Z : Fin q → Ω) (u : Val) : Prop :=
  ∃ l : List Val, u = .list l ∧ l.length = q ∧
    ∀ k : Fin q, ∃ v, l[k.1]? = some v ∧ TmGLPFindOut N X (Z k) v

/-- The input `[gens N, vs, q, [k_i]]`. -/
def tmGLPYIn (σN : List (Perm (Fin n))) (vs : List Val) {q : ℕ} (ks : Fin q → Perm (Fin n)) :
    Val :=
  .list [encGroup σN, .list vs, .nat q, .list ((List.finRange q).map fun i => encPerm (ks i))]

/-- The cost bound, for an input of weight `W`. -/
def tmGLPYLabC (pm pf : Prim) (W : ℕ) : ℕ :=
  (W + 1) * (2 * tmGLPFindC pm pf (20 * W + 40) + 10 ^ 4 * (W + 1) ^ 3) + 10 ^ 6 * (W + 1) ^ 4

theorem tmGLPFindC_mono (pm pf : Prim) {W V : ℕ} (h : W ≤ V) :
    tmGLPFindC pm pf W ≤ tmGLPFindC pm pf V := by
  unfold tmGLPFindC
  have := tmGLPTryC_mono pm pf (show 4 * W + 10 ≤ 4 * V + 10 by omega)
  gcongr

theorem tmGLP_wt_findOut {N : Subgroup (Perm (Fin n))} {q : ℕ} {X : Fin q → Ω} {Z : Ω} {v : Val}
    (hv : TmGLPFindOut N X Z v) : v.wt ≤ 2 * q + 8 * (n + 1) ^ 2 + 10 := by
  rcases hv with ⟨rfl, -⟩ | ⟨j, x, -, rfl, -, -⟩
  · simp
  · have := wt_list2_le (.nat j) (encPerm x)
    have := wt_nat_le j
    have := wt_encPerm_le x
    have := j.2
    omega

set_option maxHeartbeats 4000000 in
/-- **The labels of `y'`.** For a coset table `vs` of `x, y`, elements `k_i ∈ H` and rows `z_i`
with `z_i^{k_i} = y_i`, the result holds the search result for every `z_i`. -/
theorem tmGLPYLab_spec (hm : Membership) (hfac : NormalizedFactor) {P : Program}
    {b find rel jm jf : ℕ} (h : P.HasAt b (tmGLPYLabFuns b find))
    (hfd : P.HasAt find (tmGLPFindFuns find rel)) (hr : TmGLPRelAt P rel jm jf)
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    {H : Subgroup (Perm (Fin n))} {σN : List (Perm (Fin n))} (hNH : gens σN ≤ H)
    (hn : GI.Multicoset.Normalizes H (gens σN)) {q : ℕ} {X Y : Fin q → Ω} {vs : List Val}
    (hT : TmCsTabOK H X Y vs) {ks : Fin q → Perm (Fin n)} (hks : ∀ i, ks i ∈ H)
    {Z : Fin q → Ω} (hZ : ∀ i, Z i ↼ ks i = Y i) :
    FunAll P b (tmGLPYIn σN vs ks) (fun u c => TmGLPYOut (gens σN) X Z u ∧
      c ≤ tmGLPYLabC (membershipPrim hm) (normalizedFactorPrim hfac) (tmGLPYIn σN vs ks).wt) := by
  set a := tmGLPYIn σN vs ks with ha
  set W := a.wt with hW
  set KS : List Val := (List.finRange q).map fun i => encPerm (ks i) with hKS
  have hk := Det.get' (Det.var' (P := P) (env := [a]) (i := 0) (v := a) rfl) (Det.nat 2)
    (vs := [encGroup σN, .list vs, .nat q, .list KS]) (v := .nat q) rfl
  have hKSi : ∀ i : Fin q, KS[i.1]? = some (encPerm (ks i)) := fun i => by
    simp [hKS, List.getElem?_map]
  have wKS : (Val.list KS).wt < W := wt_le_wt_list (by simp [ha, tmGLPYIn, hKS])
  have wvs : (Val.list vs).wt < W := wt_le_wt_list (by simp [ha, tmGLPYIn])
  have wN : (encGroup σN).wt < W := wt_le_wt_list (by simp [ha, tmGLPYIn])
  have hqW : q < W := by
    have : KS.length = q := by simp [hKS]
    have := length_lt_wt_list KS
    omega
  have hnW : 0 < q → n < W := fun hq => by
    have h1 : (encPerm (ks ⟨0, hq⟩)).wt < (Val.list KS).wt :=
      wt_le_wt_list (List.mem_of_getElem? (hKSi ⟨0, hq⟩))
    have := tmGLP_n_lt_wt (ks ⟨0, hq⟩)
    omega
  have hS : W + 1 ≤ (W + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hS3 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hB : 0 < q → 2 * q + 8 * (n + 1) ^ 2 + 10 ≤ 20 * (W + 1) ^ 2 := fun hq => by
    have := Nat.pow_le_pow_left (show n + 1 ≤ W + 1 by have := hnW hq; omega) 2
    omega
  have hM : ∀ i acc, i ≤ q → TmGLPYInv (gens σN) X Z (20 * (W + 1) ^ 2) i acc →
      acc.wt ≤ 50 * (W + 1) ^ 3 := by
    rintro i acc hi ⟨l, rfl, hl, h1, -⟩
    have h2 := wt_list_le_of h1
    have h3 : l.length * (2 * (20 * (W + 1) ^ 2) + 1) ≤ (W + 1) * (41 * (W + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : (W + 1) * (41 * (W + 1) ^ 2) = 41 * (W + 1) ^ 3 := by ring
    have : 4 ≤ (W + 1) ^ 3 := by
      have : 2 ≤ W + 1 := by omega
      calc 4 ≤ 2 ^ 3 := by norm_num
        _ ≤ (W + 1) ^ 3 := Nat.pow_le_pow_left this 3
    omega
  refine (loopBdd_spec h hk Det.nil (by have := wt_nat_le q; omega) (M := 50 * (W + 1) ^ 3)
    (Inv := TmGLPYInv (gens σN) X Z (20 * (W + 1) ^ 2))
    ⟨[], rfl, rfl, fun v hv => absurd hv List.not_mem_nil, fun k hk => absurd hk (Nat.not_lt_zero _)⟩ hM
    (D := fun _ => 2 * tmGLPFindC (membershipPrim hm) (normalizedFactorPrim hfac) (20 * W + 40) +
      10 ^ 4 * (W + 1) ^ 3) ?_).mono ?_
  · rintro i acc hi ⟨l, rfl, hl, hlw, hlv⟩
    have hlW := hM i (.list l) hi.le ⟨l, rfl, hl, hlw, hlv⟩
    set A : Val := .list [a, .nat i, .list l] with hA
    have g0 := Det.arg' (P := P) (vs := [a, .nat i, .list l]) (rest := []) (j := 0) rfl
    have g1 := Det.arg' (P := P) (vs := [a, .nat i, .list l]) (rest := []) (j := 1) rfl
    have g2 := Det.arg' (P := P) (vs := [a, .nat i, .list l]) (rest := []) (j := 2) rfl
    have dN := Det.get' g0 (Det.nat 0) (vs := [encGroup σN, .list vs, .nat q, .list KS])
      (v := encGroup σN) rfl
    have dvs := Det.get' g0 (Det.nat 1) (vs := [encGroup σN, .list vs, .nat q, .list KS])
      (v := .list vs) rfl
    have dq := Det.get' g0 (Det.nat 2) (vs := [encGroup σN, .list vs, .nat q, .list KS])
      (v := .nat q) rfl
    have dKS := Det.get' g0 (Det.nat 3) (vs := [encGroup σN, .list vs, .nat q, .list KS])
      (v := .list KS) rfl
    have dk := Det.get' dKS g1 (hKSi ⟨i, hi⟩)
    -- weights
    have wA := wt_list3_le a (.nat i) (.list l)
    have eA : A.wt = (Val.list [a, .nat i, .list l]).wt := rfl
    have wi := wt_nat_le i
    have wq := wt_nat_le q
    have wk : (encPerm (ks ⟨i, hi⟩)).wt < (Val.list KS).wt :=
      wt_le_wt_list (List.mem_of_getElem? (hKSi ⟨i, hi⟩))
    have wctx := wt_list4_le (encGroup σN) (.list vs) (.nat q) (.nat i)
    have winp := wt_list2_le (.list [encGroup σN, .list vs, .nat q, .nat i]) (encPerm (ks ⟨i, hi⟩))
    have eW : W = (Val.list [encGroup σN, .list vs, .nat q, .list KS]).wt := rfl
    have w4 : 4 ≤ W := by
      have := wt_list4_le (encGroup σN) (.list vs) (.nat q) (.list KS)
      have := wt_list_eq [encGroup σN, .list vs, .nat q, .list KS]
      have := (Val.nat q).two_le_size
      have := (Val.nat q).size_le_wt
      omega
    have dargs := (Det.mk2 (Det.mk4 dN dvs dq g1) dk).mono (c' := 5000 * (W + 1) ^ 3) (by omega)
    have hspec := tmGLPFind_spec hm hfac hfd hr hjm hjf hNH hn hT ⟨i, hi⟩ (hks ⟨i, hi⟩)
      (hZ ⟨i, hi⟩)
    have hmono := tmGLPFindC_mono (membershipPrim hm) (normalizedFactorPrim hfac)
      (show (Val.list [tmGLPCtx σN vs q ((⟨i, hi⟩ : Fin q) : ℕ), encPerm (ks ⟨i, hi⟩)]).wt ≤ 20 * W + 40 by
        have e : (Val.list [tmGLPCtx σN vs q ((⟨i, hi⟩ : Fin q) : ℕ), encPerm (ks ⟨i, hi⟩)]).wt =
          (Val.list [.list [encGroup σN, .list vs, .nat q, .nat i], encPerm (ks ⟨i, hi⟩)]).wt := rfl
        omega)
    have hcall : EvalAll P [A] (.call find (mk2 (mk4 (.get (arg 0) (.nat 0))
        (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)) (arg 1))
        (.get (.get (arg 0) (.nat 3)) (arg 1))))
        (fun w c => TmGLPFindOut (gens σN) X (Z ⟨i, hi⟩) w ∧ c ≤ 5000 * (W + 1) ^ 3 +
          2 * tmGLPFindC (membershipPrim hm) (normalizedFactorPrim hfac) (20 * W + 40) + 1) := by
      refine EvalAll.call_funAll dargs fun v ca hv => ?_
      obtain ⟨rfl, hca⟩ := hv
      refine FunAll.mono (FunAll.wt_lt hspec) fun w cb hw => ⟨hw.1.1, ?_⟩
      have := hw.1.2
      have := hw.2
      omega
    refine (EvalAll.snoc_det g2 hcall).mono ?_
    rintro v c ⟨w, cb, ⟨hw, hcb⟩, rfl, hc⟩
    have hwB : w.wt ≤ 20 * (W + 1) ^ 2 := (tmGLP_wt_findOut hw).trans (hB (by omega))
    refine ⟨⟨l ++ [w], rfl, by simp [hl], ?_, ?_⟩, ?_⟩
    · intro v' hv'
      rcases List.mem_append.1 hv' with hv' | hv'
      · exact hlw v' hv'
      · rw [List.mem_singleton.1 hv']; exact hwB
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · obtain ⟨v', hv', hit⟩ := hlv k hk
        exact ⟨v', by rw [List.getElem?_append_left (by omega)]; exact hv', hit⟩
      · refine ⟨w, by rw [hk, ← hl, List.getElem?_concat_length], ?_⟩
        have : k = ⟨i, hi⟩ := Fin.ext hk
        subst this; exact hw
    · have wsn := wt_list_snoc_le l w
      beta_reduce
      clear hspec hmono hcall
      omega
  · rintro u c ⟨⟨l, rfl, hl, -, hlv⟩, hc⟩
    refine ⟨⟨l, rfl, hl, fun k => hlv k k.2⟩, ?_⟩
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    have h1 : q * (2 * tmGLPFindC (membershipPrim hm) (normalizedFactorPrim hfac) (20 * W + 40) +
        10 ^ 4 * (W + 1) ^ 3) ≤ (W + 1) * (2 * tmGLPFindC (membershipPrim hm)
          (normalizedFactorPrim hfac) (20 * W + 40) + 10 ^ 4 * (W + 1) ^ 3) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : loopModK * (q + 1) * (W + q + 50 * (W + 1) ^ 3 + 1) ≤
        1000 * ((W + 1) * (52 * (W + 1) ^ 3)) := by
      rw [Nat.mul_assoc]; unfold loopModK
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))
    have e2 : (W + 1) * (52 * (W + 1) ^ 3) = 52 * (W + 1) ^ 4 := by ring
    unfold tmGLPYLabC
    generalize loopModK * (q + 1) * (W + q + 50 * (W + 1) ^ 3 + 1) = L at hc h4
    generalize (W + 1) * (2 * tmGLPFindC (membershipPrim hm) (normalizedFactorPrim hfac) (20 * W + 40) +
        10 ^ 4 * (W + 1) ^ 3) = T at hc h1 ⊢
    generalize (W + 1) ^ 4 = C4 at e2 ⊢
    omega

end GI.Impl
