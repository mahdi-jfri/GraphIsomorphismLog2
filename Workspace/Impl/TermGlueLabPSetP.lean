import Workspace.Impl.TermGlueLabPSet

/-!
# The setup program of step 5

Step 5 of the label program (proof of Theorem A.23). `tmGLPSetF abel mec ap quo inv`
on `[gens N*, gens N, [b_j]]` returns the context `[t, U, V, d]` (see `TermGlueLabPSet.lean` for
the steps). The facts of the result are `TmGLPSetOut`. The callees `abel`, `quo`, `inv` are
given by their specifications with monotone bounds `FA`, `FQ`, `FI` (they hold with polynomial
bounds by `linAbelianCoordinates_spec_poly`, `tmGLQBudget_poly` and `tmGLPInvC_poly`).
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encInt encIntMatrix encPerm encGroup gens FullRankInst fullRankInput)

variable {n : ℕ}

/-- **The setup program**, on `[gens N*, gens N, [b_j]]`. -/
def tmGLPSetF (abel mec ap quo inv : ℕ) : Expr :=
  .letE (.call abel (mk2 (arg 0) (arg 1)))
    (.letE (.call mec (mk2 (arg 1) (arg 2)))
      (.letE (.call ap (mk2 (.var 1) (.var 2)))
        (.letE (.call quo (mk3 (.length (.var 3)) (.length (.var 1)) (.var 3)))
          (.letE (.call inv (mk3 (.length (.var 1)) (.length (.var 1)) (.get (.var 4) (.nat 1))))
            (mk4 (.length (.var 1)) (.var 5) (.get (.var 4) (.nat 1))
              (.get (.var 4) (.nat 0)))))))

/-- **The facts of the context** `[t, U, V, d]`: `M` presents `N/N*` on the stored generators
of `N`, the rows of `Z` are coordinates of the `b_j`, `[d, V]` is a quotient output for
`[M; Z]`, and `U = V⁻¹`. -/
def TmGLPSetOut (σS σN bs : List (Perm (Fin n))) (ctx : Val) : Prop :=
  ∃ (M : Matrix (Fin σN.length) (Fin σN.length) ℤ) (Z : Matrix (Fin bs.length) (Fin σN.length) ℤ)
    (U V D : Matrix (Fin σN.length) (Fin σN.length) ℤ),
    ctx = tmGLPMCtx U V (fun i => D i i) ∧ linPermPresentation σS σN M ∧
    (∀ j : Fin bs.length, TmGLPCoordOf σN (bs[j.val]'j.isLt) (Z j)) ∧ IsUnit V.det ∧
    (∀ i, 0 < D i i) ∧
    (∀ w, (∃ y, Matrix.vecMul y (tmGLQStack M Z) = w) ↔ ∀ i, D i i ∣ (Matrix.vecMul w V) i) ∧
    U * V = 1 ∧ V * U = 1

/-- The stage bounds of the setup. -/
def tmGLPSetA (FA : ℕ → ℕ) (W : ℕ) : ℕ := FA (4 * W + 6)
def tmGLPSetZ (Ce De W : ℕ) : ℕ := tmGLPItemsC (tmGLPBud Ce De) (4 * W + 6)
def tmGLPSetAp (FA : ℕ → ℕ) (Ce De W : ℕ) : ℕ :=
  loopModK * (tmGLPSetZ Ce De W + 1) * (10 * (tmGLPSetA FA W + tmGLPSetZ Ce De W) + 20)
def tmGLPSetQ (FA FQ : ℕ → ℕ) (Ce De W : ℕ) : ℕ :=
  FQ (8 * (tmGLPSetAp FA Ce De W + tmGLPSetA FA W) + 20)
def tmGLPSetI (FA FQ FI : ℕ → ℕ) (Ce De W : ℕ) : ℕ :=
  FI (8 * (tmGLPSetQ FA FQ Ce De W + tmGLPSetA FA W) + 20)

/-- **The cost bound of the setup.** -/
def tmGLPSetC (FA FQ FI : ℕ → ℕ) (Ce De W : ℕ) : ℕ :=
  1000 * (W + 1) + 100 * (tmGLPSetA FA W + tmGLPSetZ Ce De W + tmGLPSetAp FA Ce De W +
    tmGLPSetQ FA FQ Ce De W + tmGLPSetI FA FQ FI Ce De W)

private theorem tmGLP_set_ar {c1 c2 c3 c4 c5 c6 w1 w2 w3 w4 w5 W A Z Ap Q I : ℕ}
    (h1 : c1 ≤ 12 * W + 31 + 2 * A) (h2 : c2 ≤ 12 * W + 33 + 2 * Z)
    (h3 : c3 ≤ 5 * (A + Z) + 22 + 2 * Ap)
    (h4 : c4 ≤ 5 * (Ap + A) + 40 + 3 * (8 * (Ap + A) + 20) + 2 * Q)
    (h5 : c5 ≤ 5 * (Q + A) + 40 + 3 * (8 * (Q + A) + 20) + 2 * I)
    (h6 : c6 ≤ 4 * (A + Q + I) + 40 + 4 * (2 * (A + 2 + I + Q + Q) + 8))
    (hw : ∀ w ∈ [w1, w2, w3, w4, w5], w ≤ 2 * (A + 2 + I + Q + Q) + 8) :
    c1 + (c2 + (c3 + (c4 + (c5 + c6 + w1 + 1) + w2 + 1) + w3 + 1) + w4 + 1) + w5 + 1 ≤
      1000 * (W + 1) + 100 * (A + Z + Ap + Q + I) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hw
  omega

set_option maxHeartbeats 1000000 in
/-- **The setup program.** -/
theorem tmGLPSet_spec (hm : GI.Cited.ConstructiveMembership) {P : Program}
    {f abel mec ec jm ap quo inv : ℕ} (hf : P.funs[f]? = some (tmGLPSetF abel mec ap quo inv))
    (σS σN bs : List (Perm (Fin n))) (ht : 0 < σN.length)
    {FA FQ FI : ℕ → ℕ} (hFA : Monotone FA) (hFQ : Monotone FQ) (hFI : Monotone FI)
    (hab : FunAll P abel (.list [encGroup σS, encGroup σN]) (fun out c =>
      (∃ M : Matrix (Fin σN.length) (Fin σN.length) ℤ, out = encIntMatrix M ∧
        linPermPresentation σS σN M) ∧ c ≤ FA (Val.list [encGroup σS, encGroup σN]).wt))
    (hmec : P.HasAt mec (mapFuns mec ec)) (hec : linElementCoordinatesAt P ec jm hm)
    {Ce De : ℕ} (hEB : ∀ W, linElementBudget hm W ≤ Ce * (W + 2) ^ De)
    (hbs : ∀ b ∈ bs, b ∈ gens σN) (hap : P.HasAt ap (appendFuns ap))
    (hquo : ∀ I : FullRankInst, FunAll P quo (fullRankInput I) (fun out c =>
      TmGLQOut I.A out ∧ c ≤ FQ (fullRankInput I).wt))
    (hinv : ∀ {t : ℕ} (ht : 0 < t) (V : Matrix (Fin t) (Fin t) ℤ) (hV : IsUnit V.det),
      FunAll P inv (fullRankInput (tmGLPInst ht V hV)) (fun w c =>
        ∃ U : Matrix (Fin t) (Fin t) ℤ, w = encIntMatrix U ∧ U * V = 1 ∧ V * U = 1 ∧
          c ≤ FI (fullRankInput (tmGLPInst ht V hV)).wt)) :
    FunAll P f (.list [encGroup σS, encGroup σN, .list (bs.map encPerm)]) (fun w c =>
      TmGLPSetOut σS σN bs w ∧ c ≤ tmGLPSetC FA FQ FI Ce De
        (Val.list [encGroup σS, encGroup σN, .list (bs.map encPerm)]).wt) := by
  set a : Val := .list [encGroup σS, encGroup σN, .list (bs.map encPerm)] with ha
  set W := a.wt with hW
  obtain ⟨A, hA⟩ : ∃ A, tmGLPSetA FA W = A := ⟨_, rfl⟩
  obtain ⟨Zc, hZc⟩ : ∃ Zc, tmGLPSetZ Ce De W = Zc := ⟨_, rfl⟩
  obtain ⟨Ap, hAp⟩ : ∃ Ap, tmGLPSetAp FA Ce De W = Ap := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, tmGLPSetQ FA FQ Ce De W = Q := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I, tmGLPSetI FA FQ FI Ce De W = I := ⟨_, rfl⟩
  have hAp' : loopModK * (Zc + 1) * (10 * (A + Zc) + 20) = Ap := by
    rw [← hAp, tmGLPSetAp, hA, hZc]
  have hQ' : FQ (8 * (Ap + A) + 20) = Q := by rw [← hQ, tmGLPSetQ, hAp, hA]
  have hI' : FI (8 * (Q + A) + 20) = I := by rw [← hI, tmGLPSetI, hQ, hA]
  unfold tmGLPSetC
  rw [hA, hZc, hAp, hQ, hI]
  have w0 : (encGroup σS).wt < W := wt_le_wt_list (by simp)
  have w1 : (encGroup σN).wt < W := wt_le_wt_list (by simp)
  have w2 : (Val.list (bs.map encPerm)).wt < W := wt_le_wt_list (by simp)
  have gA : ∀ (rest : List Val) (j : ℕ) (v : Val),
      [encGroup σS, encGroup σN, .list (bs.map encPerm)][j]? = some v →
      Det P (a :: rest) (arg j) v (2 * W + j + 5) := fun rest j v h => Det.arg' h
  clear_value a W
  apply FunAll.intro hf
  -- step 1: the presentation `M`
  have i1 := tmGLP_mk2_le (gA [] 0 _ rfl) le_rfl (gA [] 1 _ rfl) le_rfl (X := W) (Y := W)
    w0.le w1.le
  have c1 := tmGLP_callAll_le i1.1 le_rfl (C := A)
    (R := fun out => ∃ M : Matrix (Fin σN.length) (Fin σN.length) ℤ, out = encIntMatrix M ∧
      linPermPresentation σS σN M)
    (FunAll.mono hab fun w c h => ⟨h.1, h.2.trans (by rw [← hA]; exact hFA (i1.2.trans (by omega)))⟩)
  refine EvalAll.letE c1 fun v1 c1' h1 => ?_
  obtain ⟨⟨M, rfl, hMp⟩, hc1, hv1⟩ := h1
  have hdet : M.det ≠ 0 := by
    obtain ⟨_, _, hcert⟩ := hMp
    exact hcert.1
  -- step 2: the rows `Z`
  have i2 := tmGLP_mk2_le (gA [encIntMatrix M] 1 _ rfl) le_rfl (gA [encIntMatrix M] 2 _ rfl)
    le_rfl (X := W) (Y := W) w1.le w2.le
  have c2 := tmGLP_callAll_le i2.1 le_rfl (C := Zc)
    (R := fun w => ∃ Z : Matrix (Fin bs.length) (Fin σN.length) ℤ, w = encIntMatrix Z ∧
      ∀ j : Fin bs.length, TmGLPCoordOf σN (bs[j.val]'j.isLt) (Z j))
    (FunAll.mono (tmGLPZRows_spec hm hmec hec hEB σN bs hbs) fun w c h => by
      obtain ⟨Z, hw, hZ, hc⟩ := h
      refine ⟨⟨Z, hw, hZ⟩, hc.trans ?_⟩
      rw [← hZc]
      exact tmGLPItemsC_mono (fun a b h => by unfold tmGLPBud; gcongr) (by
        have := wt_list2_le (encGroup σN) (Val.list (bs.map encPerm)); omega))
  refine EvalAll.letE c2 fun v2 c2' h2 => ?_
  obtain ⟨⟨Z, rfl, hZ⟩, hc2, hv2⟩ := h2
  -- step 3: the stacked matrix
  set xs : List Val := (List.finRange σN.length).map fun i => linVecVal (M i) with hxs
  set ys : List Val := (List.finRange bs.length).map fun j => linVecVal (Z j) with hys
  have eM : encIntMatrix M = .list xs := rfl
  have eZ : encIntMatrix Z = .list ys := rfl
  have dv1 := Det.var' (P := P) (env := [a, encIntMatrix M, encIntMatrix Z]) (i := 1) rfl
  have dv2 := Det.var' (P := P) (env := [a, encIntMatrix M, encIntMatrix Z]) (i := 2) rfl
  have i3 := tmGLP_mk2_le dv1 le_rfl dv2 le_rfl (X := A) (Y := Zc) hv1.le hv2.le
  have hyl : ys.length < Zc := by
    have := length_lt_wt_list ys; rw [← eZ] at this; omega
  have hxl : xs.length < A := by
    have := length_lt_wt_list xs; rw [← eM] at this; omega
  have c3 := tmGLP_callAll_le i3.1 le_rfl (C := Ap)
    (R := fun w => w = encIntMatrix (tmGLQStack M Z))
    (by
      rw [eM, eZ]
      refine FunAll.mono (append_spec hap xs ys) fun w c ⟨hw, hc⟩ => ⟨?_, ?_⟩
      · rw [hw, tmGLP_enc_stack]
      · have hs1 := sum_wt_lt_wt_list xs
        have hs2 := sum_wt_lt_wt_list ys
        have hww := wt_list_le (xs ++ ys)
        simp only [List.map_append, List.sum_append, List.length_append] at hww
        rw [← eM] at hs1; rw [← eZ] at hs2
        have hin : (Val.list [.list xs, .list ys]).wt ≤ 2 * (A + Zc) + 6 := by
          rw [← eM, ← eZ]; exact i3.2
        rw [hw] at hc
        refine hc.trans ?_
        rw [← hAp']
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega))
  refine EvalAll.letE c3 fun v3 c3' h3 => ?_
  obtain ⟨rfl, hc3, hv3⟩ := h3
  -- step 4: the quotient program
  set I0 : FullRankInst := ⟨σN.length + bs.length, σN.length, ht, by omega, tmGLQStack M Z,
    tmGLQ_stack_inj M hdet Z⟩ with hI0
  have dv3 := Det.var' (P := P)
    (env := [a, encIntMatrix M, encIntMatrix Z, encIntMatrix (tmGLQStack M Z)]) (i := 3) rfl
  have dv1' := Det.var' (P := P)
    (env := [a, encIntMatrix M, encIntMatrix Z, encIntMatrix (tmGLQStack M Z)]) (i := 1) rfl
  have dl3 := Det.length (vs := (List.finRange (σN.length + bs.length)).map
    fun i => linVecVal (tmGLQStack M Z i)) dv3
  have dl1 := Det.length (vs := xs) dv1'
  simp only [hxs, List.length_map, List.length_finRange] at dl3 dl1
  have hst : σN.length + bs.length < Ap := by
    have := length_lt_wt_list ((List.finRange (σN.length + bs.length)).map
      fun i => linVecVal (tmGLQStack M Z i))
    simp only [List.length_map, List.length_finRange] at this
    have e : encIntMatrix (tmGLQStack M Z) = .list ((List.finRange (σN.length + bs.length)).map
      fun i => linVecVal (tmGLQStack M Z i)) := rfl
    rw [← e] at this; omega
  have hxl' : σN.length < A := by simpa [hxs] using hxl
  have d4 := Det.mk3 dl3 dl1 dv3
  have w4 : (fullRankInput I0).wt ≤ 8 * (Ap + A) + 20 := by
    have := wt_list3_le (.nat (σN.length + bs.length)) (.nat σN.length)
      (encIntMatrix (tmGLQStack M Z))
    have := wt_nat_le (σN.length + bs.length)
    have := wt_nat_le σN.length
    change (Val.list [.nat (σN.length + bs.length), .nat σN.length,
      encIntMatrix (tmGLQStack M Z)]).wt ≤ _
    omega
  have c4 := tmGLP_callAll_le (vin := fullRankInput I0) d4 le_rfl (C := Q)
    (R := fun out => TmGLQOut I0.A out)
    (FunAll.mono (hquo I0) fun w c h => ⟨h.1, h.2.trans (by rw [← hQ']; exact hFQ w4)⟩)
  have w4' : (Val.list [.nat (σN.length + bs.length), .nat σN.length,
      encIntMatrix (tmGLQStack M Z)]).wt ≤ 8 * (Ap + A) + 20 := w4
  refine EvalAll.letE c4 fun v4 c4' h4 => ?_
  obtain ⟨⟨V, D, rfl, hV, hpos, hrel⟩, hc4, hv4⟩ := h4
  -- step 5: the inverse
  set env5 : List Val := [a, encIntMatrix M, encIntMatrix Z, encIntMatrix (tmGLQStack M Z),
    .list [linVecVal (fun i => D i i), encIntMatrix V]] with henv5
  have dv1'' := Det.var' (P := P) (env := env5) (i := 1) rfl
  have dl1' := Det.length (vs := xs) dv1''
  simp only [hxs, List.length_map, List.length_finRange] at dl1'
  have dv4 := Det.var' (P := P) (env := env5) (i := 4) rfl
  have dgV := Det.get' dv4 (Det.nat 1) (vs := [linVecVal (fun i => D i i), encIntMatrix V])
    (v := encIntMatrix V) rfl
  have wV : (encIntMatrix V).wt < Q := (wt_le_wt_list (by simp)).trans hv4
  have wd : (linVecVal (fun i => D i i)).wt < Q := (wt_le_wt_list (by simp)).trans hv4
  have d5 := Det.mk3 dl1' dl1' dgV
  have w5 : (fullRankInput (tmGLPInst ht V hV)).wt ≤ 8 * (Q + A) + 20 := by
    have := wt_list3_le (.nat σN.length) (.nat σN.length) (encIntMatrix V)
    have := wt_nat_le σN.length
    change (Val.list [.nat σN.length, .nat σN.length, encIntMatrix V]).wt ≤ _
    omega
  have c5 := tmGLP_callAll_le (vin := fullRankInput (tmGLPInst ht V hV)) d5 le_rfl (C := I)
    (R := fun w => ∃ U : Matrix (Fin σN.length) (Fin σN.length) ℤ, w = encIntMatrix U ∧
      U * V = 1 ∧ V * U = 1)
    (FunAll.mono (hinv ht V hV) fun w c h => by
      obtain ⟨U, hw, h1, h2, hc⟩ := h
      exact ⟨⟨U, hw, h1, h2⟩, hc.trans (by rw [← hI']; exact hFI w5)⟩)
  have w5' : (Val.list [.nat σN.length, .nat σN.length, encIntMatrix V]).wt ≤ 8 * (Q + A) + 20 :=
    w5
  refine EvalAll.letE c5 fun v5 c5' h5 => ?_
  obtain ⟨⟨U, rfl, hUV, hVU⟩, hc5, hv5⟩ := h5
  -- step 6: the context
  set env6 : List Val := env5 ++ [encIntMatrix U] with henv6
  have dv1''' := Det.var' (P := P) (env := env6) (i := 1) rfl
  have dl1'' := Det.length (vs := xs) dv1'''
  simp only [hxs, List.length_map, List.length_finRange] at dl1''
  have dv5 := Det.var' (P := P) (env := env6) (i := 5) rfl
  have dv4' := Det.var' (P := P) (env := env6) (i := 4) rfl
  have dgV' := Det.get' dv4' (Det.nat 1) (vs := [linVecVal (fun i => D i i), encIntMatrix V])
    (v := encIntMatrix V) rfl
  have dgd' := Det.get' dv4' (Det.nat 0) (vs := [linVecVal (fun i => D i i), encIntMatrix V])
    (v := linVecVal (fun i => D i i)) rfl
  have d6 := Det.mk4 dl1'' dv5 dgV' dgd'
  refine d6.post fun c6 hc6 => ⟨⟨M, Z, U, V, D, rfl, hMp, hZ, hV, hpos, hrel, hUV, hVU⟩, ?_⟩
  have w6 := wt_list4_le (.nat σN.length) (encIntMatrix U) (encIntMatrix V)
    (linVecVal (fun i => D i i))
  have wn := wt_nat_le σN.length
  have hw6 : (Val.list [.nat σN.length, encIntMatrix U, encIntMatrix V,
      linVecVal (fun i => D i i)]).wt ≤ 2 * (A + 2 + I + Q + Q) + 8 := by omega
  have h5' : c5' ≤ 5 * (Q + A) + 40 + 3 * (8 * (Q + A) + 20) + 2 * I := by omega
  have q1 : (encIntMatrix V).wt < Q := wV
  have q2 : (linVecVal (fun i => D i i)).wt < Q := wd
  have q3 : (encIntMatrix U).wt < I := hv5
  have h6' : c6 ≤ 4 * (A + Q + I) + 40 + 4 * (2 * (A + 2 + I + Q + Q) + 8) := by omega
  refine tmGLP_set_ar (by omega) (by omega) (by omega) (by omega) h5' h6' ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro w (rfl | rfl | rfl | rfl | rfl) <;> exact hw6

end GI.Impl
