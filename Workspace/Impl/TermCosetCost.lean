import Workspace.Impl.TermCosetTop

/-!
# The cost of the coset program is `expLogSq A N`

The polynomial part `tmCsTopQ` of the cost is bounded by `K (X + 1)^D` (`tmCs_topQ_poly`, by
closure rules for such bounds, `TmCsPoly`). The input weight `X` is polynomial in `N`
(`tm_wtV_le`), so this part is at most `expLogSq` (`pow_le_expLogSq`). The recursive part is
`tmRec_spec_cost`, with `m + q ≤ N + 1`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Multicoset Equiv
open GI.Cited (Val encPerm encGroup gens)

/-! ### Polynomial bounds -/

/-- `f` is bounded by `K (X + 1)^D` for some `K` and `D`. -/
def TmCsPoly (f : ℕ → ℕ) : Prop := ∃ K D : ℕ, ∀ X, f X ≤ K * (X + 1) ^ D

theorem tmCsPoly_const (c : ℕ) : TmCsPoly fun _ => c := ⟨c, 0, fun X => by simp⟩

theorem tmCsPoly_pow (i : ℕ) : TmCsPoly fun X => (X + 1) ^ i := ⟨1, i, fun X => by simp⟩

theorem tmCsPoly_mono {f g : ℕ → ℕ} (h : ∀ X, f X ≤ g X) (hg : TmCsPoly g) : TmCsPoly f := by
  obtain ⟨K, D, hK⟩ := hg
  exact ⟨K, D, fun X => (h X).trans (hK X)⟩

theorem tmCsPoly_add {f g : ℕ → ℕ} (hf : TmCsPoly f) (hg : TmCsPoly g) :
    TmCsPoly fun X => f X + g X := by
  obtain ⟨K₁, D₁, h₁⟩ := hf
  obtain ⟨K₂, D₂, h₂⟩ := hg
  refine ⟨K₁ + K₂, max D₁ D₂, fun X => ?_⟩
  have e₁ : (X + 1) ^ D₁ ≤ (X + 1) ^ max D₁ D₂ := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have e₂ : (X + 1) ^ D₂ ≤ (X + 1) ^ max D₁ D₂ :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have := h₁ X
  have := h₂ X
  calc f X + g X ≤ K₁ * (X + 1) ^ max D₁ D₂ + K₂ * (X + 1) ^ max D₁ D₂ := by
        have := Nat.mul_le_mul_left K₁ e₁
        have := Nat.mul_le_mul_left K₂ e₂
        omega
    _ = (K₁ + K₂) * (X + 1) ^ max D₁ D₂ := by ring

theorem tmCsPoly_mul {f g : ℕ → ℕ} (hf : TmCsPoly f) (hg : TmCsPoly g) :
    TmCsPoly fun X => f X * g X := by
  obtain ⟨K₁, D₁, h₁⟩ := hf
  obtain ⟨K₂, D₂, h₂⟩ := hg
  refine ⟨K₁ * K₂, D₁ + D₂, fun X => ?_⟩
  calc f X * g X ≤ (K₁ * (X + 1) ^ D₁) * (K₂ * (X + 1) ^ D₂) := Nat.mul_le_mul (h₁ X) (h₂ X)
    _ = K₁ * K₂ * (X + 1) ^ (D₁ + D₂) := by ring

theorem tmCsPoly_npow {f : ℕ → ℕ} (hf : TmCsPoly f) (j : ℕ) : TmCsPoly fun X => f X ^ j := by
  obtain ⟨K, D, h⟩ := hf
  refine ⟨K ^ j, D * j, fun X => ?_⟩
  calc f X ^ j ≤ (K * (X + 1) ^ D) ^ j := Nat.pow_le_pow_left (h X) j
    _ = K ^ j * (X + 1) ^ (D * j) := by rw [mul_pow, ← pow_mul]

/-- Composition with an inner map bounded by `c (X + 1)^i`. -/
theorem tmCsPoly_comp {f g : ℕ → ℕ} (hf : TmCsPoly f) {c i : ℕ}
    (hg : ∀ X, g X + 1 ≤ c * (X + 1) ^ i) : TmCsPoly fun X => f (g X) := by
  obtain ⟨K, D, h⟩ := hf
  refine ⟨K * c ^ D, i * D, fun X => ?_⟩
  calc f (g X) ≤ K * (g X + 1) ^ D := h _
    _ ≤ K * (c * (X + 1) ^ i) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hg X) D)
    _ = K * c ^ D * (X + 1) ^ (i * D) := by rw [mul_pow, ← pow_mul]; ring

theorem tmCsPoly_boundSize (p : Prim) : TmCsPoly fun B => p.boundSize B := by
  have h : TmCsPoly fun B => p.c * ((B + 1) + 1) ^ p.k :=
    tmCsPoly_mul (tmCsPoly_const _)
      (tmCsPoly_comp (g := fun B => B + 1) (tmCsPoly_pow p.k) (c := 2) (i := 1)
        (fun X => by simp))
  exact tmCsPoly_mono (fun B => le_of_eq (by unfold Prim.boundSize; rfl)) h

/-- An inner map `b (X + 1)^i`. -/
theorem tmCs_inner_le (b i X : ℕ) : b * (X + 1) ^ i + 1 ≤ (b + 1) * (X + 1) ^ i := by
  have : 1 ≤ (X + 1) ^ i := Nat.one_le_pow _ _ (by omega)
  nlinarith

theorem tmCsPoly_cpow (K b i D : ℕ) : TmCsPoly fun X => K * (b * (X + 1) ^ i) ^ D :=
  tmCsPoly_mul (tmCsPoly_const K)
    (tmCsPoly_npow (tmCsPoly_mul (tmCsPoly_const b) (tmCsPoly_pow i)) D)

theorem tmCsPoly_objK (p : Prim) : TmCsPoly fun X => tmCsObjK p X := by
  unfold tmCsObjK
  refine tmCsPoly_add (tmCsPoly_mul (tmCsPoly_const _) (tmCsPoly_pow 10)) ?_
  exact tmCsPoly_comp (tmCsPoly_boundSize p) (c := 101) (i := 1) (fun X => by simp; omega)

theorem tmCsPoly_objsK (p : Prim) : TmCsPoly fun X => tmCsObjsK p X := by
  unfold tmCsObjsK
  exact tmCsPoly_mul (tmCsPoly_mul (tmCsPoly_const _) (tmCsPoly_pow 3)) (tmCsPoly_objK p)

theorem tmCsPoly_resQ (p : Prim) (Kr Dr Ks Ds : ℕ) :
    TmCsPoly fun X => tmCsResQ p Kr Dr Ks Ds X := by
  unfold tmCsResQ
  refine tmCsPoly_mul (tmCsPoly_const _) (tmCsPoly_npow ?_ 2)
  refine tmCsPoly_add (tmCsPoly_add (tmCsPoly_add (tmCsPoly_add ?_ (tmCsPoly_cpow _ _ _ _))
    (tmCsPoly_cpow _ _ _ _)) ?_) (tmCsPoly_mul (tmCsPoly_const _) (tmCsPoly_pow 12))
  · exact tmCsPoly_comp (tmCsPoly_objsK p) (c := 21) (i := 1) (fun X => by simp; omega)
  · exact tmCsPoly_comp (tmCsPoly_boundSize p) (c := 10 ^ 4 + 1) (i := 6)
      (fun X => tmCs_inner_le _ _ _)

theorem tmCsPoly_topQ (p : Prim) (Kr Dr Ks Ds Kl Dl Kj Dj : ℕ) :
    TmCsPoly fun X => tmCsTopQ p Kr Dr Ks Ds Kl Dl Kj Dj X := by
  unfold tmCsTopQ
  refine tmCsPoly_add (tmCsPoly_add (tmCsPoly_add (tmCsPoly_add (tmCsPoly_add
    (tmCsPoly_resQ p Kr Dr Ks Ds) (tmCsPoly_cpow _ _ _ _)) (tmCsPoly_cpow _ _ _ _)) ?_) ?_)
    (tmCsPoly_mul (tmCsPoly_const _) (tmCsPoly_pow 6))
  · unfold tmCsTabK; exact tmCsPoly_mul (tmCsPoly_const _) (tmCsPoly_pow 4)
  · unfold tmCsRelK; exact tmCsPoly_mul (tmCsPoly_const _) (tmCsPoly_pow 9)

/-! ### Comparison with `expLogSq` -/

theorem tmCs_expLogSq_mul (a b : ℝ) (N : ℕ) :
    expLogSq a N * expLogSq b N = expLogSq (a + b) N := by
  unfold expLogSq; rw [← Real.exp_add]; ring_nf

theorem tmCs_expLogSq_succ {c : ℝ} (hc : 0 ≤ c) (N : ℕ) :
    expLogSq c (N + 1) ≤ expLogSq (4 * c) N := by
  unfold expLogSq
  apply Real.exp_le_exp.2
  have h0 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 2) := Real.log_nonneg (by linarith [N.cast_nonneg (α := ℝ)])
  have h1 : Real.log (((N + 1 : ℕ) : ℝ) + 2) ≤ 2 * Real.log ((N : ℝ) + 2) := by
    rw [← Real.log_rpow (by positivity)]
    apply Real.log_le_log (by positivity)
    push_cast
    rw [show ((N : ℝ) + 2) ^ (2 : ℝ) = ((N : ℝ) + 2) ^ (2 : ℕ) by norm_cast]
    nlinarith [N.cast_nonneg (α := ℝ)]
  have h2 : (0 : ℝ) ≤ Real.log (((N + 1 : ℕ) : ℝ) + 2) := Real.log_nonneg (by push_cast; linarith [N.cast_nonneg (α := ℝ)])
  have h3 : Real.log (((N + 1 : ℕ) : ℝ) + 2) ^ 2 ≤ 4 * Real.log ((N : ℝ) + 2) ^ 2 := by nlinarith
  nlinarith

/-- The constant of the polynomial part. -/
noncomputable def tmCsPolK (p : Prim) (Kr Dr Ks Ds Kl Dl Kj Dj : ℕ) : ℕ :=
  (tmCsPoly_topQ p Kr Dr Ks Ds Kl Dl Kj Dj).choose

/-- The degree of the polynomial part. -/
noncomputable def tmCsPolD (p : Prim) (Kr Dr Ks Ds Kl Dl Kj Dj : ℕ) : ℕ :=
  (tmCsPoly_topQ p Kr Dr Ks Ds Kl Dl Kj Dj).choose_spec.choose

theorem tmCs_topQ_le (p : Prim) (Kr Dr Ks Ds Kl Dl Kj Dj X : ℕ) :
    tmCsTopQ p Kr Dr Ks Ds Kl Dl Kj Dj X ≤
      tmCsPolK p Kr Dr Ks Ds Kl Dl Kj Dj * (X + 1) ^ tmCsPolD p Kr Dr Ks Ds Kl Dl Kj Dj :=
  (tmCsPoly_topQ p Kr Dr Ks Ds Kl Dl Kj Dj).choose_spec.choose_spec X

/-- The constant `A` of the coset program. -/
noncomputable def tmCsA (p : Prim) (Kr Dr Ks Ds Kl Dl Kj Dj Kc Dc : ℕ) : ℝ :=
  3 * (Real.log ((tmCsPolK p Kr Dr Ks Ds Kl Dl Kj Dj * (10 ^ 9) ^ tmCsPolD p Kr Dr Ks Ds Kl Dl Kj Dj
      + 1 : ℕ) : ℝ) + 8 * tmCsPolD p Kr Dr Ks Ds Kl Dl Kj Dj) +
    (3 * Real.log 20 + 4 * (3 * (Real.log (max Kc 1 : ℕ) + Dc) + tmRecA 5)) + 3

/-- **The cost bound.** -/
theorem tmCs_cost_le (p : Prim) (Kr Dr Ks Ds Kl Dl Kj Dj Kc Dc : ℕ) {N X m q ℓ : ℕ}
    (hX : X + 1 ≤ 10 ^ 9 * (N + 2) ^ 8) (hmq : m + q ≤ N + 1)
    (hℓ : (ℓ : ℝ) ≤ 5 * Real.logb 3 m + 1) :
    (tmCsTopQ p Kr Dr Ks Ds Kl Dl Kj Dj X : ℝ) +
      20 * ((5 * ((q : ℝ) + 1) ^ 3 + 1) ^ ℓ * (Kc * (((m + q : ℕ) : ℝ) + 2) ^ Dc)) ≤
      expLogSq (tmCsA p Kr Dr Ks Ds Kl Dl Kj Dj Kc Dc) N := by
  set K := tmCsPolK p Kr Dr Ks Ds Kl Dl Kj Dj
  set D := tmCsPolD p Kr Dr Ks Ds Kl Dl Kj Dj
  -- the polynomial part
  have h1 : tmCsTopQ p Kr Dr Ks Ds Kl Dl Kj Dj X ≤ (K * (10 ^ 9) ^ D + 1) * (N + 2) ^ (8 * D) := by
    calc _ ≤ K * (X + 1) ^ D := tmCs_topQ_le p Kr Dr Ks Ds Kl Dl Kj Dj X
      _ ≤ K * (10 ^ 9 * (N + 2) ^ 8) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX D)
      _ = K * (10 ^ 9) ^ D * (N + 2) ^ (8 * D) := by rw [mul_pow, ← pow_mul (N + 2)]; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hA1 : (1 : ℝ) ≤ ((K * (10 ^ 9) ^ D + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
  have h2 := pow_le_expLogSq hA1 (8 * D) N
  have h1' : (tmCsTopQ p Kr Dr Ks Ds Kl Dl Kj Dj X : ℝ) ≤
      ((K * (10 ^ 9) ^ D + 1 : ℕ) : ℝ) * ((N : ℝ) + 2) ^ (8 * D) := by
    exact_mod_cast h1
  -- the recursive part
  set c := 3 * (Real.log (max Kc 1 : ℕ) + Dc) + tmRecA 5 with hcdef
  have hc0 : 0 ≤ c := by
    have : 0 ≤ Real.log (max Kc 1 : ℕ) := Real.log_nonneg (by exact_mod_cast le_max_right _ _)
    have : 0 ≤ tmRecA 5 := by
      unfold tmRecA
      have := Real.log_pos (show (1 : ℝ) < 2 * 5 by norm_num)
      have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
      positivity
    positivity
  have hRB : (5 * ((q : ℝ) + 1) ^ 3 + 1) ^ ℓ * (Kc * (((m + q : ℕ) : ℝ) + 2) ^ Dc) ≤
      expLogSq (4 * c) N := by
    have hmono : (5 * ((q : ℝ) + 1) ^ 3 + 1) ^ ℓ * (Kc * (((m + q : ℕ) : ℝ) + 2) ^ Dc) ≤
        (5 * ((q : ℝ) + 1) ^ 3 + 1) ^ ℓ * ((max Kc 1 : ℕ) * (((m + q : ℕ) : ℝ) + 2) ^ Dc) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast le_max_left _ _
    refine hmono.trans ((tmRec_spec_cost (by exact le_max_right _ _) hℓ).trans ?_)
    exact (expLogSq_mono_right hc0 hmq).trans (tmCs_expLogSq_succ hc0 N)
  have h20 : (20 : ℝ) ≤ expLogSq (3 * Real.log 20) N := by
    have := pow_le_expLogSq (A := (20 : ℝ)) (by norm_num) 0 N
    simpa using this
  have hE0 : 0 ≤ expLogSq (4 * c) N := (Real.exp_pos _).le
  have hRB0 : 0 ≤ (5 * ((q : ℝ) + 1) ^ 3 + 1) ^ ℓ * (Kc * (((m + q : ℕ) : ℝ) + 2) ^ Dc) := by
    positivity
  have h3 : 20 * ((5 * ((q : ℝ) + 1) ^ 3 + 1) ^ ℓ * (Kc * (((m + q : ℕ) : ℝ) + 2) ^ Dc)) ≤
      expLogSq (3 * Real.log 20 + 4 * c) N := by
    rw [← tmCs_expLogSq_mul]
    exact mul_le_mul h20 hRB hRB0 (by linarith)
  have hA0 : 0 ≤ 3 * (Real.log ((K * (10 ^ 9) ^ D + 1 : ℕ) : ℝ) + (8 * D : ℕ)) := by
    have := Real.log_nonneg hA1
    positivity
  have hB0 : 0 ≤ 3 * Real.log 20 + 4 * c := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 20 by norm_num)
    positivity
  have h4 := expLogSq_add_le hA0 hB0 N
  have e : tmCsA p Kr Dr Ks Ds Kl Dl Kj Dj Kc Dc =
      3 * (Real.log ((K * (10 ^ 9) ^ D + 1 : ℕ) : ℝ) + (8 * D : ℕ)) + (3 * Real.log 20 + 4 * c)
        + 3 := by
    unfold tmCsA; simp only [hcdef, K, D]; push_cast; ring
  rw [e]
  linarith

/-! ### `TermCosetSpec` -/

/-- **T4–T6: the coset program meets `TermCosetSpec`**, given the residual pieces (the radical
preimage, the solvable supplement, the A.20 recursion) and the two abelian computations of
Theorem A.23 (`TermGlueLabSpec`, `TermJSpec`) as hypotheses. -/
theorem tm_termCosetSpec (hst : GI.Cited.PointwiseStab) (dixon : GI.Cited.DixonDerivedLength)
    {P : Program} {f res lab jj tab rel : ℕ}
    {mkg rad sup objs msh sh ell rec comp app red jst rg ax px ay py mx fx my fy first inv : ℕ}
    {dom rg' tb tbe inv' conj mp : ℕ}
    (hA : TmCsTopAt P f res lab jj tab rel mkg rad sup objs msh sh ell rec comp app red jst rg ax
      px ay py mx fx my fy first inv dom rg' tb tbe inv' conj mp)
    (hjst : P.prims[jst]? = some (pointwiseStabPrim hst)) {Kr Dr Ks Ds Kc Dc Kl Dl Kj Dj : ℕ}
    (hrad : Iface.TermRadSpec P Kr Dr rad) (hsup : Iface.TermSupSpec P Ks Ds sup)
    (hrec : Iface.TermRecSpec P Kc Dc rec) (hlab : Iface.TermGlueLabSpec P Kl Dl lab)
    (hjj : Iface.TermJSpec P Kj Dj jj) :
    Iface.TermCosetSpec P (tmCsA (pointwiseStabPrim hst) Kr Dr Ks Ds Kl Dl Kj Dj Kc Dc) f := by
  intro Ω C _ S k e c hc sv lv L hsv hlv hq0 hgood hrow label hnat hq m h0 E hP σH σN σS hH hNg hSg
    htr hlH hlN hlS hcard hsN hN hqα us vs hus hvs r hr
  refine FunAll.mono (tmCs_top_spec hst dixon hA hjst hrad hsup hrec hlab hjj S k e c hc sv lv L hsv
    hlv hq0 hgood hrow label hnat hq h0 E hP σH σN σS hH hNg hSg htr hlH hlN hlS hcard hsN hN hqα
    us vs hus hvs r hr) ?_
  rintro u cost ⟨hu, ℓ, hℓ, hcost⟩
  refine ⟨hu, hcost.trans (tmCs_cost_le _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ hℓ)⟩
  · have hq1 : 0 < L.q := by omega
    have hV := tm_wtV_le hsv hlv E hq1 hlH hlN hlS hus hvs
    have hmN : m ≤ S.N := by
      have : m * L.q = S.size := by rw [← hcard, Fintype.card_fin]
      nlinarith
    have hr4 := wt_encPerm_le r
    have ha := wt_list2_le (.list [.list [sv, lv, coordsVal e S E, a18Out σH σN σS 0,
      encFun (rowLab e L.con.blocks)], .list us, .list vs]) (encPerm r)
    have hY1 : 1 ≤ (S.N + 2) ^ 8 := Nat.one_le_pow _ _ (by omega)
    have hY2 : (m + 1) ^ 2 ≤ (S.N + 2) ^ 8 :=
      (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
    unfold tmVB at hV
    omega
  · have : m * L.q = S.size := by rw [← hcard, Fintype.card_fin]
    nlinarith

end GI.Impl
