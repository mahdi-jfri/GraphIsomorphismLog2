import Workspace.Impl.TermGlueLabPItemM

/-!
# The matrix pair of one generator (step 5, program)

Step 5 of the label program (proof of Theorem A.23). On
`[[gens N, ctx], [g, g⁻¹]]` with `ctx = [t, U, V, d]`, `tmGLPMPairF cm mat` computes the
coordinate matrices `C₁` of `a ↦ g a g⁻¹` and `C₂` of `a ↦ g⁻¹ a g` (`tmGLPCMatF` at `cm`,
twice) and returns the two matrices `(U Cₖ V)ᵀ mod d` (`tmGLPMatF` at `mat`). By
`tmGLP_item_mat` and `tmGLP_item_mat_inv` these are the contract's matrices of `ρ(g)` and
`ρ(g⁻¹)`.

The cost bound is stated with polynomial envelopes of the two callee bounds (hypotheses `hCM`,
`hMC`; both hold by `tmGLPCMatC_poly`, `tmGLPMatC_poly`).
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encInt encIntMatrix encPerm encGroup gens)

variable {n : ℕ}

/-- **The matrix pair of one generator**, on `[[gens N, ctx], [g, g⁻¹]]`. -/
def tmGLPMPairF (cm mat : ℕ) : Expr :=
  .letE (.call cm (mk2 (.get (arg 0) (.nat 0)) (arg 1)))
    (.letE (.call cm (mk2 (.get (arg 0) (.nat 0)) (mk2 (.get (arg 1) (.nat 1)) (.get (arg 1) (.nat 0)))))
      (mk2 (.call mat (mk2 (.get (arg 0) (.nat 1)) (.var 1)))
        (.call mat (mk2 (.get (arg 0) (.nat 1)) (.var 2)))))

/-- The bound of one coordinate-matrix call at input weight `W`. -/
def tmGLPMPX (Cc Dc W : ℕ) : ℕ := Cc * (64 * W + 202) ^ Dc

/-- The bound of one matrix call at input weight `W`. -/
def tmGLPMPZ (Cc Dc Cm Dm W : ℕ) : ℕ := Cm * (3 * (W + tmGLPMPX Cc Dc W) + 8) ^ Dm

/-- **The cost bound of the matrix pair.** -/
def tmGLPMPairC (Cc Dc Cm Dm W : ℕ) : ℕ :=
  1000 * (W + 1) + 40 * tmGLPMPX Cc Dc W + 40 * tmGLPMPZ Cc Dc Cm Dm W

/-- A call of a function with a specification, with bounded argument cost. -/
theorem tmGLP_callAll_le {P : Program} {env : List Val} {a : Expr} {f : ℕ} {vin : Val}
    {ca A C : ℕ} {R : Val → Prop} (ha : Det P env a vin ca) (hca : ca ≤ A)
    (hf : FunAll P f vin (fun w c => R w ∧ c ≤ C)) :
    EvalAll P env (.call f a) (fun w c => R w ∧ c ≤ A + 2 * C + 1 ∧ w.wt < C) := by
  refine EvalAll.call_funAll ha fun v ca' hv => ?_
  obtain ⟨rfl, h⟩ := hv
  exact (FunAll.wt_lt hf).mono fun w c ⟨⟨hR, hc⟩, hw⟩ => ⟨hR, by omega, by omega⟩

private theorem tmGLP_mp_ar1 {c W X a : ℕ} (hc : c ≤ a + 2 * X + 1) (ha : a ≤ 64 * W + 200) :
    c ≤ 64 * W + 201 + 2 * X := by omega

private theorem tmGLP_mp_ar2 {c1 c2 cb ww W X Z : ℕ} (h1 : c1 ≤ 64 * W + 201 + 2 * X)
    (h2 : c2 ≤ 64 * W + 201 + 2 * X) (hb : cb ≤ 2 * (8 * W + 5 * X + 31 + 2 * Z) + 4 * (Z + Z) + 19)
    (hw : ww ≤ 2 * (Z + Z) + 6) :
    c1 + (c2 + cb + ww + 1) + ww + 1 ≤ 1000 * (W + 1) + 40 * X + 40 * Z := by omega

/-- **The matrix pair of one generator.** -/
theorem tmGLPMPair_spec (hm : GI.Cited.ConstructiveMembership) {P : Program}
    {f cm mat mcj cj cp tl mec ec jm mul tr red : ℕ}
    (hf : P.funs[f]? = some (tmGLPMPairF cm mat))
    (hcm : P.funs[cm]? = some (tmGLPCMatF mcj tl mec))
    (hcp : P.HasAt cp (composeFuns cp)) (hcj : P.funs[cj]? = some (supConjF cp))
    (hmcj : P.HasAt mcj (mapFuns mcj cj)) (htl : P.HasAt tl (linTailFuns tl))
    (hmec : P.HasAt mec (mapFuns mec ec)) (hec : linElementCoordinatesAt P ec jm hm)
    (hmat : P.funs[mat]? = some (tmGLPMatF mul tr red))
    (hmul : linDenseMulAt P mul) (htr : P.HasAt tr (tmGLPTrFuns tr))
    (hred : P.HasAt red (linFiniteMatrixReduceFuns red))
    {Ce De Cc Dc Cm Dm : ℕ} (hEB : ∀ W, linElementBudget hm W ≤ Ce * (W + 2) ^ De)
    (hCM : ∀ W, tmGLPCMatC Ce De W ≤ Cc * (W + 2) ^ Dc)
    (hMC : ∀ W t, tmGLPMatC W t ≤ Cm * (W + 0 + t + 2) ^ Dm)
    (σN : List (Perm (Fin n))) (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ)
    (d : Fin σN.length → ℤ) (g : Perm (Fin n))
    (hs1 : ∀ a ∈ σN, g * a * g⁻¹ ∈ gens σN) (hs2 : ∀ a ∈ σN, g⁻¹ * a * g ∈ gens σN) :
    FunAll P f (.list [.list [encGroup σN, tmGLPMCtx U V d], .list [encPerm g, encPerm g⁻¹]])
      (fun w c => ∃ C₁ C₂ : Matrix (Fin σN.length) (Fin σN.length) ℤ,
        w = .list [encIntMatrix (fun i j => (U * C₁ * V) j i % d i),
          encIntMatrix (fun i j => (U * C₂ * V) j i % d i)] ∧
        (∀ j : Fin σN.length, TmGLPCoordOf σN (g * σN[j.val] * g⁻¹) (C₁ j)) ∧
        (∀ j : Fin σN.length, TmGLPCoordOf σN (g⁻¹ * σN[j.val] * g) (C₂ j)) ∧
        c ≤ tmGLPMPairC Cc Dc Cm Dm
          (Val.list [.list [encGroup σN, tmGLPMCtx U V d], .list [encPerm g, encPerm g⁻¹]]).wt) := by
  set a : Val := .list [.list [encGroup σN, tmGLPMCtx U V d], .list [encPerm g, encPerm g⁻¹]]
    with ha
  set W := a.wt with hW
  obtain ⟨X, hX⟩ : ∃ X, tmGLPMPX Cc Dc W = X := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, tmGLPMPZ Cc Dc Cm Dm W = Z := ⟨_, rfl⟩
  unfold tmGLPMPairC
  rw [hZ, hX]
  have gA : ∀ (rest : List Val) (j : ℕ) (v : Val),
      [Val.list [encGroup σN, tmGLPMCtx U V d], .list [encPerm g, encPerm g⁻¹]][j]? = some v →
      Det P (a :: rest) (arg j) v (2 * W + j + 5) := fun rest j v h => Det.arg' h
  have w0 : (Val.list [encGroup σN, tmGLPMCtx U V d]).wt < W := wt_le_wt_list (by simp)
  have w1 : (Val.list [encPerm g, encPerm g⁻¹]).wt < W := wt_le_wt_list (by simp)
  have wG : (encGroup σN).wt < (Val.list [encGroup σN, tmGLPMCtx U V d]).wt :=
    wt_le_wt_list (by simp)
  have wM : (tmGLPMCtx U V d).wt < (Val.list [encGroup σN, tmGLPMCtx U V d]).wt :=
    wt_le_wt_list (by simp)
  have wg : (encPerm g).wt < (Val.list [encPerm g, encPerm g⁻¹]).wt := wt_le_wt_list (by simp)
  have wg' : (encPerm g⁻¹).wt < (Val.list [encPerm g, encPerm g⁻¹]).wt := wt_le_wt_list (by simp)
  have htW : σN.length < W :=
    ((tmGLP_len_lt_encGroup σN).trans wG).trans w0
  -- the pieces of the input
  have hX' : ∀ y, y ≤ 64 * W + 200 → tmGLPCMatC Ce De y ≤ X := fun y hy => by
    rw [← hX]
    exact (hCM y).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hZ' : ∀ y, y ≤ 2 * (W + X) + 6 → tmGLPMatC y σN.length ≤ Z := fun y hy => by
    rw [← hZ]
    unfold tmGLPMPZ
    rw [hX]
    exact (hMC y _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  clear_value a W
  apply FunAll.intro hf
  -- the first coordinate matrix
  have g0 : Det P [a] (arg 0) (.list [encGroup σN, tmGLPMCtx U V d]) (2 * W + 0 + 5) := gA _ _ _ rfl
  have g1 : Det P [a] (arg 1) (.list [encPerm g, encPerm g⁻¹]) (2 * W + 1 + 5) := gA _ _ _ rfl
  have dG := Det.get' g0 (Det.nat 0) (vs := [encGroup σN, tmGLPMCtx U V d]) (v := encGroup σN) rfl
  have i1 := tmGLP_mk2_le dG (A := 4 * W + 10) (by omega) g1 (B := 2 * W + 6) (by omega)
    (X := W) (Y := W) (by omega) (by omega)
  have s1 : FunAll P cm (.list [encGroup σN, .list [encPerm g, encPerm g⁻¹]]) (fun w c =>
      (∃ C : Matrix (Fin σN.length) (Fin σN.length) ℤ, w = encIntMatrix C ∧
        ∀ j : Fin σN.length, TmGLPCoordOf σN (g * σN[j.val]'j.isLt * g⁻¹) (C j)) ∧ c ≤ X) := by
    have hb := hX' _ (i1.2.trans (by omega))
    refine FunAll.mono (tmGLPCMat_spec hm hcm hcp hcj hmcj htl hmec hec hEB σN g hs1) ?_
    rintro w c ⟨C, hw, hC, hc⟩
    exact ⟨⟨C, hw, hC⟩, hc.trans hb⟩
  have hi1 : 4 * W + 10 + (2 * W + 6) + 4 * (W + W) + 19 ≤ 64 * W + 200 := by omega
  have c1 := tmGLP_callAll_le i1.1 hi1 s1
  refine EvalAll.letE c1 fun v1 c1' h1 => ?_
  obtain ⟨⟨C₁, rfl, hC₁⟩, hc1, hv1⟩ := h1
  -- the second coordinate matrix
  have g0' : Det P [a, encIntMatrix C₁] (arg 0) (.list [encGroup σN, tmGLPMCtx U V d]) (2 * W + 0 + 5) := gA _ _ _ rfl
  have g1' : Det P [a, encIntMatrix C₁] (arg 1) (.list [encPerm g, encPerm g⁻¹]) (2 * W + 1 + 5) := gA _ _ _ rfl
  have dG' := Det.get' g0' (Det.nat 0) (vs := [encGroup σN, tmGLPMCtx U V d]) (v := encGroup σN) rfl
  have dp1 := Det.get' g1' (Det.nat 1) (vs := [encPerm g, encPerm g⁻¹]) (v := encPerm g⁻¹) rfl
  have dp0 := Det.get' g1' (Det.nat 0) (vs := [encPerm g, encPerm g⁻¹]) (v := encPerm g) rfl
  have i2 := tmGLP_mk2_le dp1 (A := 4 * W + 10) (by omega) dp0 (B := 4 * W + 10) (by omega)
    (X := W) (Y := W) (by omega) (by omega)
  have i3 := tmGLP_mk2_le dG' (A := 4 * W + 10) (by omega) i2.1 le_rfl (X := W)
    (Y := 2 * (W + W) + 6) (by omega) i2.2
  have hcm2 := tmGLPCMat_spec hm hcm hcp hcj hmcj htl hmec hec hEB σN g⁻¹
    (fun a h => by simpa using hs2 a h)
  rw [inv_inv] at hcm2
  have c2 := tmGLP_callAll_le i3.1 (A := 64 * W + 200) (by omega) (C := X)
    (R := fun w => ∃ C : Matrix (Fin σN.length) (Fin σN.length) ℤ, w = encIntMatrix C ∧
      ∀ j : Fin σN.length, TmGLPCoordOf σN (g⁻¹ * σN[j.val]'j.isLt * g) (C j))
    (hcm2.mono fun w c h => by
      obtain ⟨C, hw, hC, hc⟩ := h
      exact ⟨⟨C, hw, fun j => by simpa using hC j⟩, hc.trans (hX' _ (by omega))⟩)
  refine EvalAll.letE c2 fun v2 c2' h2 => ?_
  obtain ⟨⟨C₂, rfl, hC₂⟩, hc2, hv2⟩ := h2
  -- the two matrices
  have g0'' : Det P [a, encIntMatrix C₁, encIntMatrix C₂] (arg 0) (.list [encGroup σN, tmGLPMCtx U V d]) (2 * W + 0 + 5) :=
    gA _ _ _ rfl
  have dM := Det.get' g0'' (Det.nat 1) (vs := [encGroup σN, tmGLPMCtx U V d])
    (v := tmGLPMCtx U V d) rfl
  have dv1 := Det.var' (P := P) (env := [a, encIntMatrix C₁, encIntMatrix C₂]) (i := 1) rfl
  have dv2 := Det.var' (P := P) (env := [a, encIntMatrix C₁, encIntMatrix C₂]) (i := 2) rfl
  have j1 := tmGLP_mk2_le dM (A := 4 * W + 10) (by omega) dv1 (B := X + 1) (by omega)
    (X := W) (Y := X) (by omega) hv1.le
  have m1 := tmGLP_call_le j1.1 le_rfl (tmGLPMat_spec hmat hmul htr hred U V C₁ d) (C := Z)
    (hZ' _ j1.2)
  have j2 := tmGLP_mk2_le dM (A := 4 * W + 10) (by omega) dv2 (B := X + 1) (by omega)
    (X := W) (Y := X) (by omega) hv2.le
  have m2 := tmGLP_call_le j2.1 le_rfl (tmGLPMat_spec hmat hmul htr hred U V C₂ d) (C := Z)
    (hZ' _ j2.2)
  have fin := tmGLP_mk2_le m1.1 le_rfl m2.1 le_rfl (X := Z) (Y := Z) m1.2.le m2.2.le
  refine fin.1.post fun cb hcb => ⟨C₁, C₂, rfl, hC₁, hC₂, ?_⟩
  have hw := fin.2
  exact tmGLP_mp_ar2 (tmGLP_mp_ar1 hc1 le_rfl) (tmGLP_mp_ar1 hc2 le_rfl) (by omega) hw

/-! ### The offset vector -/

/-- **The offset vector program**, on `[[gens N, ctx], xs]`: the coordinate sum of `1 :: xs`
(`tmGLPCSumFuns` at `cs`), then `(Σ z) V mod d` (`tmGLPVecF` at `vec`). -/
def tmGLPOVecF (cs vec : ℕ) : Expr :=
  .letE (.call cs (mk2 (.get (arg 0) (.nat 0)) (arg 1)))
    (.call vec (mk2 (.get (arg 0) (.nat 1)) (.var 1)))

private theorem tmGLP_ov_ar {c1 cb ww W X Z : ℕ} (h1 : c1 ≤ 64 * W + 201 + 2 * X)
    (hb : cb ≤ 8 * W + 5 * X + 31 + 2 * Z) (hw : ww ≤ Z) :
    c1 + cb + ww + 1 ≤ 1000 * (W + 1) + 40 * X + 40 * Z := by omega

/-- **The offset vector of a list.** On `[[gens N, ctx], xs]` with every entry of `xs` in
`⟨gens N⟩`, the result is `(Σ zs) V mod d` for coordinate vectors `zs` of `1 :: xs`. With
`tmGLP_item_off` and `tmGLP_item_u` this is the contract's offset vector of a generator. The
bound is `tmGLPMPairC` (same shape as the matrix pair). -/
theorem tmGLPOVec_spec (hm : GI.Cited.ConstructiveMembership) {P : Program}
    {f cs vec ec add ib jm mul tr red : ℕ}
    (hf : P.funs[f]? = some (tmGLPOVecF cs vec))
    (hcs : P.HasAt cs (tmGLPCSumFuns cs ec add)) (hec : linElementCoordinatesAt P ec jm hm)
    (hib : linIntSpec P ib) (hadd : P.HasAt add (linVectorBinaryFuns add (ib + 11)))
    (hvec : P.funs[vec]? = some (tmGLPVecF mul tr red))
    (hmul : linDenseMulAt P mul) (htr : P.HasAt tr (tmGLPTrFuns tr))
    (hred : P.HasAt red (linFiniteMatrixReduceFuns red))
    {Ce De Cs Ds Cv Dv : ℕ} (hEB : ∀ W, linElementBudget hm W ≤ Ce * (W + 2) ^ De)
    (hCS : ∀ W, tmGLPCSumC Ce De W ≤ Cs * (W + 2) ^ Ds)
    (hVC : ∀ W t, tmGLPVecC W t ≤ Cv * (W + 0 + t + 2) ^ Dv)
    (σN : List (Perm (Fin n))) (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ)
    (d : Fin σN.length → ℤ) (xs : List (Perm (Fin n))) (hx : ∀ y ∈ xs, y ∈ gens σN) :
    FunAll P f (.list [.list [encGroup σN, tmGLPMCtx U V d], .list (xs.map encPerm)])
      (fun w c => ∃ zs : List (Fin σN.length → ℤ), List.Forall₂ (TmGLPCoordOf σN) (1 :: xs) zs ∧
        w = linVecVal (fun i => Matrix.vecMul zs.sum V i % d i) ∧
        c ≤ tmGLPMPairC Cs Ds Cv Dv
          (Val.list [.list [encGroup σN, tmGLPMCtx U V d], .list (xs.map encPerm)]).wt) := by
  set a : Val := .list [.list [encGroup σN, tmGLPMCtx U V d], .list (xs.map encPerm)] with ha
  set W := a.wt with hW
  obtain ⟨X, hX⟩ : ∃ X, tmGLPMPX Cs Ds W = X := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, tmGLPMPZ Cs Ds Cv Dv W = Z := ⟨_, rfl⟩
  unfold tmGLPMPairC
  rw [hZ, hX]
  have gA : ∀ (rest : List Val) (j : ℕ) (v : Val),
      [Val.list [encGroup σN, tmGLPMCtx U V d], .list (xs.map encPerm)][j]? = some v →
      Det P (a :: rest) (arg j) v (2 * W + j + 5) := fun rest j v h => Det.arg' h
  have w0 : (Val.list [encGroup σN, tmGLPMCtx U V d]).wt < W := wt_le_wt_list (by simp)
  have w1 : (Val.list (xs.map encPerm)).wt < W := wt_le_wt_list (by simp)
  have wG : (encGroup σN).wt < (Val.list [encGroup σN, tmGLPMCtx U V d]).wt :=
    wt_le_wt_list (by simp)
  have wM : (tmGLPMCtx U V d).wt < (Val.list [encGroup σN, tmGLPMCtx U V d]).wt :=
    wt_le_wt_list (by simp)
  have htW : σN.length < W := ((tmGLP_len_lt_encGroup σN).trans wG).trans w0
  have hX' : ∀ y, y ≤ 64 * W + 200 → tmGLPCSumC Ce De y ≤ X := fun y hy => by
    rw [← hX]
    exact (hCS y).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  have hZ' : ∀ y, y ≤ 2 * (W + X) + 6 → tmGLPVecC y σN.length ≤ Z := fun y hy => by
    rw [← hZ]
    unfold tmGLPMPZ
    rw [hX]
    exact (hVC y _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  clear_value a W
  apply FunAll.intro hf
  have g0 : Det P [a] (arg 0) (.list [encGroup σN, tmGLPMCtx U V d]) (2 * W + 0 + 5) :=
    gA _ _ _ rfl
  have g1 : Det P [a] (arg 1) (.list (xs.map encPerm)) (2 * W + 1 + 5) := gA _ _ _ rfl
  have dG := Det.get' g0 (Det.nat 0) (vs := [encGroup σN, tmGLPMCtx U V d]) (v := encGroup σN) rfl
  have i1 := tmGLP_mk2_le dG (A := 4 * W + 10) (by omega) g1 (B := 2 * W + 6) (by omega)
    (X := W) (Y := W) (by omega) (by omega)
  have s1 : FunAll P cs (.list [encGroup σN, .list (xs.map encPerm)]) (fun w c =>
      (∃ zs : List (Fin σN.length → ℤ), List.Forall₂ (TmGLPCoordOf σN) (1 :: xs) zs ∧
        w = linVecVal zs.sum) ∧ c ≤ X) := by
    have hb := hX' _ (i1.2.trans (by omega))
    refine FunAll.mono (tmGLPCSum_spec hm hcs hec hib hadd hEB σN xs hx) ?_
    rintro w c ⟨zs, hz, hw, hc⟩
    exact ⟨⟨zs, hz, hw⟩, hc.trans hb⟩
  have hi1 : 4 * W + 10 + (2 * W + 6) + 4 * (W + W) + 19 ≤ 64 * W + 200 := by omega
  have c1 := tmGLP_callAll_le i1.1 hi1 s1
  refine EvalAll.letE c1 fun v1 c1' h1 => ?_
  obtain ⟨⟨zs, hz, rfl⟩, hc1, hv1⟩ := h1
  have g0' : Det P [a, linVecVal zs.sum] (arg 0) (.list [encGroup σN, tmGLPMCtx U V d])
      (2 * W + 0 + 5) := gA _ _ _ rfl
  have dM := Det.get' g0' (Det.nat 1) (vs := [encGroup σN, tmGLPMCtx U V d])
    (v := tmGLPMCtx U V d) rfl
  have dv1 := Det.var' (P := P) (env := [a, linVecVal zs.sum]) (i := 1) rfl
  have j1 := tmGLP_mk2_le dM (A := 4 * W + 10) (by omega) dv1 (B := X + 1) (by omega)
    (X := W) (Y := X) (by omega) hv1.le
  have m1 := tmGLP_call_le j1.1 le_rfl (tmGLPVec_spec hvec hmul htr hred U V d zs.sum) (C := Z)
    (hZ' _ j1.2)
  refine m1.1.post fun cb hcb => ⟨zs, hz, rfl, ?_⟩
  exact tmGLP_ov_ar (tmGLP_mp_ar1 hc1 le_rfl) (by omega) m1.2.le

end GI.Impl
