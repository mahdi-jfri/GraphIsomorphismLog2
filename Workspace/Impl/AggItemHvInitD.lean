module

public import Workspace.Impl.AggItemHvInit

@[expose] public section

/-!
# Case 2a init program, part 1: the data that need no choice

The init program of Case 2a starts from the sorted
dominant sets `Φ` of `X` and `Φ'` of `Y`. Its first part computes, with no cited call:

1. the indicators of `Φ` and `Φ'` (`it_hvInd_spec`);
2. the even aligner `σ` with `σ Φ = Φ'` and the paired transposition `(a b)(c d)`
   (`it_hvSg_spec`);
3. the context of the label lift (`it_hvLc_spec`);
4. the flag `[2 ≤ |Φᶜ|]`, as `1 < q - |Φ|`;
5. the graph pairs of `A` (`it_hvA_spec`) and their first parts (`it_hvFst_spec`).

`itHvDaF` returns `[[σ, (a b)(c d)], ctx, flag, gA]` (`it_hvDa_spec`). The callees enter by their
specifications, so the lemma does not depend on the layout of the helpers.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPts)

variable {k q : ℕ}

/-- The program's list of graph pairs of `A` has at most `2 |S| + 1` entries. -/
theorem itHvAL_length_le (Φ : Finset (Fin q)) (S : List (Perm (Fin k) × Perm (Fin q))) :
    (itHvAL Φ S).length ≤ 2 * S.length + 1 := by
  unfold itHvAL
  split_ifs
  · simp
  · omega

/-- `(a + 1)^n ≤ B^m` for `a + 1 ≤ B` and `n ≤ m`. -/
theorem itHv_pw {a B n m : ℕ} (h : a + 1 ≤ B) (hnm : n ≤ m) : (a + 1) ^ n ≤ B ^ m :=
  (Nat.pow_le_pow_left h n).trans (Nat.pow_le_pow_right (by omega) hnm)

/-- On `[st, Px, Py]`: `[[σ, (a b)(c d)], ctx, flag, gA]`. -/
def itHvDaF (ind sg lc af fst : ℕ) : Expr :=
  .letE (.get (arg 0) (.nat 1))
  (.letE (.get (.var 1) (.nat 1))
  (.letE (.call ind (mk2 (.var 2) (arg 1)))
  (.letE (.call ind (mk2 (.var 2) (arg 2)))
  (.letE (.call sg (mk3 (.var 3) (.var 4) (arg 1)))
  (.letE (.call lc (mk2 (.var 1) (.get (arg 0) (.nat 2))))
  (.letE (.call af (mk2 (.var 3) (.get (arg 0) (.nat 3))))
  (.letE (.call fst (mk2 (.nat 0) (.var 7)))
    (mk4 (.var 5) (.var 6) (.arith .lt (.nat 1) (.arith .sub (.var 2) (.length (arg 1))))
      (.var 8)))))))))

/-- The cost bound of `itHvDaF`, for a size `M` at least the input weight and `k + q + 1`. -/
def itHvDaC (M : ℕ) : ℕ := 10 ^ 21 * (M + 1) ^ 6

theorem itHvDaC_mono {a b : ℕ} (h : a ≤ b) : itHvDaC a ≤ itHvDaC b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6)

set_option maxHeartbeats 2000000 in
/-- **The first part of the init program.** -/
theorem it_hvDa_spec {P : Program} {f ind sg lc af fst : ℕ}
    (hf : P.funs[f]? = some (itHvDaF ind sg lc af fst)) (hq : 2 ≤ q)
    (hind : ∀ Φ : Finset (Fin q),
      FunDet P ind (.list [.nat q, encPts (Φ.sort (· ≤ ·))]) (itHvInd Φ) (itHvIndC q))
    (hsg : ∀ (Φ Φ' : Finset (Fin q)) (a b : Fin q) (rest : List (Fin q)),
      Φ.sort (· ≤ ·) = a :: b :: rest →
      FunDet P sg (.list [itHvInd Φ, itHvInd Φ', encPts (Φ.sort (· ≤ ·))])
        (.list [encPerm (itHvSig Φ Φ' a b), encPerm (swap a b * itHvCD Φ hq)]) (itHvSgC q))
    (hlc : ∀ ps : List (Perm (Fin k) × Perm (Fin q)),
      FunDet P lc (.list [.list [.nat k, .nat q], .list (ps.map pairV)]) (liftLabCtx k q ps)
        (itHvLcC (pM k q ps)))
    (haf : ∀ (Φ : Finset (Fin q)) (S : List (Perm (Fin k) × Perm (Fin q))),
      (∀ s ∈ S, ∀ a, s.2 a ∈ Φ ↔ a ∈ Φ) → ∀ M, S.length + k + q + 1 ≤ M →
      FunDet P af (.list [itHvInd Φ, .list (S.map pairV)]) (.list ((itHvAL Φ S).map pairV))
        (itHvAC M))
    (hfst : ∀ ps : List (Perm (Fin k) × Perm (Fin q)),
      FunDet P fst (.list [.nat 0, .list (ps.map pairV)]) (.list (ps.map fun p => encPerm p.1))
        (10 ^ 6 * pM k q ps ^ 4))
    (sv cv : Val) (ps fx fy : List (Perm (Fin k) × Perm (Fin q))) (Φ Φ' : Finset (Fin q))
    (hfx : ∀ s ∈ fx, ∀ a, s.2 a ∈ Φ ↔ a ∈ Φ) {a b : Fin q} {rest : List (Fin q)}
    (hs : Φ.sort (· ≤ ·) = a :: b :: rest) {M : ℕ}
    (hM : (Val.list [.list [sv, .list [.nat k, .nat q], .list (ps.map pairV),
      .list (fx.map pairV), .list (fy.map pairV), cv], encPts (Φ.sort (· ≤ ·)),
      encPts (Φ'.sort (· ≤ ·))]).wt ≤ M) (hkq : k + q + 1 ≤ M) :
    FunDet P f (.list [.list [sv, .list [.nat k, .nat q], .list (ps.map pairV),
      .list (fx.map pairV), .list (fy.map pairV), cv], encPts (Φ.sort (· ≤ ·)),
      encPts (Φ'.sort (· ≤ ·))])
      (.list [.list [encPerm (itHvSig Φ Φ' a b), encPerm (swap a b * itHvCD Φ hq)],
        liftLabCtx k q ps, .nat (if 1 < q - Φ.card then 1 else 0),
        .list ((itHvAL Φ fx).map fun p => encPerm p.1)]) (itHvDaC M) := by
  set Px := encPts (Φ.sort (· ≤ ·)) with hPx
  set Py := encPts (Φ'.sort (· ≤ ·)) with hPy
  set kq : Val := .list [.nat k, .nat q] with hkqv
  set st := Val.list [sv, kq, .list (ps.map pairV), .list (fx.map pairV), .list (fy.map pairV), cv]
    with hst
  set x := Val.list [st, Px, Py] with hx
  set B := M + 1 with hB
  -- the input
  have wst : st.wt < x.wt := wt_le_wt_list (by simp [hx])
  have wPx : Px.wt < x.wt := wt_le_wt_list (by simp [hx])
  have wkq : kq.wt < st.wt := wt_le_wt_list (by simp [hst])
  have wps : (Val.list (ps.map pairV)).wt < st.wt := wt_le_wt_list (by simp [hst])
  have wfx : (Val.list (fx.map pairV)).wt < st.wt := wt_le_wt_list (by simp [hst])
  have wq : (Val.nat q).wt < kq.wt := wt_le_wt_list (by simp [hkqv])
  have lps : ps.length < (Val.list (ps.map pairV)).wt := by
    have := length_lt_wt_list (ps.map pairV); simpa using this
  have lfx : fx.length < (Val.list (fx.map pairV)).wt := by
    have := length_lt_wt_list (fx.map pairV); simpa using this
  have lPx : Φ.card < Px.wt := by
    have h := length_lt_wt_list ((Φ.sort (· ≤ ·)).map fun i : Fin q => Val.nat i)
    rw [List.length_map, Finset.length_sort] at h
    rw [hPx, itHv_encPts, natList]
    simpa [Function.comp_def] using h
  have est : (Val.list [sv, kq, .list (ps.map pairV), .list (fx.map pairV), .list (fy.map pairV),
    cv]).wt = st.wt := rfl
  have ex : (Val.list [st, Px, Py]).wt = x.wt := rfl
  have ekq : (Val.list [.nat k, .nat q]).wt = kq.wt := rfl
  have eP : (Val.list (((Φ.sort (· ≤ ·)).map Fin.val).map Val.nat)).wt = Px.wt := by
    rw [hPx, itHv_encPts]; rfl
  -- the callees
  have cIx := hind Φ
  have cIy := hind Φ'
  have cSg := hsg Φ Φ' a b rest hs
  have cLc := hlc ps
  have cAf := haf Φ fx hfx (3 * B) (by omega)
  have cFs := hfst (itHvAL Φ fx)
  have hAL := itHvAL_length_le Φ fx
  -- the cost of each callee is at most `T`
  set T := 10 ^ 17 * B ^ 6 with hT
  have hB1 : 1 ≤ B := by omega
  have p46 : B ^ 4 ≤ B ^ 6 := Nat.pow_le_pow_right hB1 (by omega)
  have p56 : B ^ 5 ≤ B ^ 6 := Nat.pow_le_pow_right hB1 (by omega)
  have tI : itHvIndC q ≤ T := by
    have := itHv_pw (a := q) (B := B) (n := 4) (m := 6) (by omega) (by omega)
    unfold itHvIndC; omega
  have tS : itHvSgC q ≤ T := by
    have := itHv_pw (a := q) (B := B) (n := 4) (m := 6) (by omega) (by omega)
    unfold itHvSgC; omega
  have tL : itHvLcC (pM k q ps) ≤ T := by
    have h1 : pM k q ps ≤ 3 * B := by unfold pM; omega
    have h2 : pM k q ps ^ 6 ≤ (3 * B) ^ 6 := Nat.pow_le_pow_left h1 6
    have h3 : (3 * B) ^ 6 = 729 * B ^ 6 := by ring
    unfold itHvLcC; omega
  have tA : itHvAC (3 * B) ≤ T := by
    have h3 : (3 * B) ^ 5 = 243 * B ^ 5 := by ring
    unfold itHvAC; omega
  have tF : 10 ^ 6 * pM k q (itHvAL Φ fx) ^ 4 ≤ T := by
    have h1 : pM k q (itHvAL Φ fx) ≤ 4 * B := by unfold pM; omega
    have h2 : pM k q (itHvAL Φ fx) ^ 4 ≤ (4 * B) ^ 4 := Nat.pow_le_pow_left h1 4
    have h3 : (4 * B) ^ 4 = 256 * B ^ 4 := by ring
    omega
  have hMT : M + 10 ≤ T := by
    have : B ≤ B ^ 6 := Nat.le_self_pow (by norm_num) _
    omega
  -- the weights of the values
  have vIx := FunDet.wt_lt cIx
  have vIy := FunDet.wt_lt cIy
  have vSg := FunDet.wt_lt cSg
  have vLc := FunDet.wt_lt cLc
  have vAf := FunDet.wt_lt cAf
  have vFs := FunDet.wt_lt cFs
  set fl := if 1 < q - Φ.card then 1 else 0 with hfl
  have hfl1 : fl ≤ 1 := by rw [hfl]; split_ifs <;> omega
  set W := 30 * T + 30 with hW
  set sgV := Val.list [encPerm (itHvSig Φ Φ' a b), encPerm (swap a b * itHvCD Φ hq)]
  set gAV := Val.list ((itHvAL Φ fx).map fun p => encPerm p.1)
  have hgA : (itHvAL Φ fx).map (fun p => encPerm p.1) =
      (itHvAL Φ fx).map (fun p => encPerm p.1) := rfl
  -- the chain
  have d1 : StDC P [x] (.get (arg 0) (.nat 1)) kq 5 0 W :=
    (StDC.get (StDC.arg (vs := [st, Px, Py]) (rest := []) (j := 0) rfl (by omega) (by omega)
      (by omega)) (StDC.nat 1 (by omega)) rfl (by omega)).mono (by omega) le_rfl
  have d2 : StDC P [x, kq] (.get (.var 1) (.nat 1)) (.nat q) 3 0 W :=
    StDC.get (StDC.var' (i := 1) rfl (by omega)) (StDC.nat 1 (by omega)) rfl (by omega)
  have d3 : StDC P [x, kq, .nat q] (.call ind (mk2 (.var 2) (arg 1))) (itHvInd Φ) 8
      (itHvIndC q) W :=
    (StDC.call (StDC.mk2 (StDC.var' (i := 2) rfl (by omega))
      (StDC.arg (vs := [st, Px, Py]) (j := 1) rfl (by omega) (by omega) (by omega))
      (by have := wt_list2_le (.nat q) Px; omega) (by omega)) cIx (by omega)).mono
      (by omega) (by omega)
  have d4 : StDC P [x, kq, .nat q, itHvInd Φ] (.call ind (mk2 (.var 2) (arg 2))) (itHvInd Φ') 8
      (itHvIndC q) W :=
    (StDC.call (StDC.mk2 (StDC.var' (i := 2) rfl (by omega))
      (StDC.arg (vs := [st, Px, Py]) (j := 2) rfl (by omega) (by omega)
        (by have : Py.wt < x.wt := wt_le_wt_list (by simp [hx]); omega))
      (by
        have : Py.wt < x.wt := wt_le_wt_list (by simp [hx])
        have := wt_list2_le (.nat q) Py; omega) (by omega)) cIy (by omega)).mono
      (by omega) (by omega)
  have d5 : StDC P [x, kq, .nat q, itHvInd Φ, itHvInd Φ'] (.call sg (mk3 (.var 3) (.var 4) (arg 1)))
      sgV 10 (itHvSgC q) W :=
    (StDC.call (StDC.mk3 (StDC.var' (i := 3) rfl (by omega)) (StDC.var' (i := 4) rfl (by omega))
      (StDC.arg (vs := [st, Px, Py]) (j := 1) rfl (by omega) (by omega) (by omega))
      (by have := wt_list3_le (itHvInd Φ) (itHvInd Φ') Px; omega) (by omega)) cSg
      (by omega)).mono (by omega) (by omega)
  have d6 : StDC P [x, kq, .nat q, itHvInd Φ, itHvInd Φ', sgV]
      (.call lc (mk2 (.var 1) (.get (arg 0) (.nat 2)))) (liftLabCtx k q ps) 13
      (itHvLcC (pM k q ps)) W :=
    (StDC.call (StDC.mk2 (StDC.var' (i := 1) rfl (by omega))
      (StDC.get (StDC.arg (vs := [st, Px, Py]) (j := 0) rfl (by omega) (by omega) (by omega))
        (StDC.nat 2 (by omega)) rfl (by omega))
      (by have := wt_list2_le kq (.list (ps.map pairV)); omega) (by omega)) cLc
      (by omega)).mono (by omega) (by omega)
  have d7 : StDC P [x, kq, .nat q, itHvInd Φ, itHvInd Φ', sgV, liftLabCtx k q ps]
      (.call af (mk2 (.var 3) (.get (arg 0) (.nat 3))))
      (.list ((itHvAL Φ fx).map pairV)) 13 (itHvAC (3 * B)) W :=
    (StDC.call (StDC.mk2 (StDC.var' (i := 3) rfl (by omega))
      (StDC.get (StDC.arg (vs := [st, Px, Py]) (j := 0) rfl (by omega) (by omega) (by omega))
        (StDC.nat 3 (by omega)) rfl (by omega))
      (by have := wt_list2_le (itHvInd Φ) (.list (fx.map pairV)); omega) (by omega)) cAf
      (by omega)).mono (by omega) (by omega)
  have d8 : StDC P [x, kq, .nat q, itHvInd Φ, itHvInd Φ', sgV, liftLabCtx k q ps,
      .list ((itHvAL Φ fx).map pairV)] (.call fst (mk2 (.nat 0) (.var 7))) gAV 6
      (10 ^ 6 * pM k q (itHvAL Φ fx) ^ 4) W :=
    (StDC.call (StDC.mk2 (StDC.nat 0 (by omega)) (StDC.var' (i := 7) rfl (by omega))
      (by
        have := wt_list2_le (.nat 0) (.list ((itHvAL Φ fx).map pairV))
        have := wt_nat_le 0; omega) (by omega)) cFs (by omega)).mono (by omega) (by omega)
  have hlen : (((Φ.sort (· ≤ ·)).map Fin.val).map Val.nat).length = Φ.card := by simp
  have d9 : StDC P [x, kq, .nat q, itHvInd Φ, itHvInd Φ', sgV, liftLabCtx k q ps,
      .list ((itHvAL Φ fx).map pairV), gAV]
      (mk4 (.var 5) (.var 6) (.arith .lt (.nat 1) (.arith .sub (.var 2) (.length (arg 1))))
        (.var 8)) (.list [sgV, liftLabCtx k q ps, .nat fl, gAV]) 20 0 W := by
    have dl : StDC P [x, kq, .nat q, itHvInd Φ, itHvInd Φ', sgV, liftLabCtx k q ps,
        .list ((itHvAL Φ fx).map pairV), gAV] (.length (arg 1)) (.nat Φ.card) 4 0 W := by
      have h := StDC.length (P := P) (W := W) (StDC.arg (vs := [st, Px, Py]) (j := 1)
        (rest := [kq, .nat q, itHvInd Φ, itHvInd Φ', sgV, liftLabCtx k q ps,
          .list ((itHvAL Φ fx).map pairV), gAV]) (v := .list (((Φ.sort (· ≤ ·)).map Fin.val).map Val.nat))
          (by rw [hPx, itHv_encPts]; rfl) (by omega) (by omega) (by omega)) (by omega)
      rw [hlen] at h
      exact h
    have dsub := StDC.arith' (op := .sub) (z := q - Φ.card) (StDC.var' (i := 2) rfl (by omega)) dl rfl (by omega)
    have dlt := StDC.arith' (op := .lt) (z := fl) (StDC.nat 1 (by omega)) dsub rfl (by omega)
    exact (StDC.mk4 (StDC.var' (i := 5) rfl (by omega)) (StDC.var' (i := 6) rfl (by omega)) dlt
      (StDC.var' (i := 8) rfl (by omega))
      (by
        have := wt_list4_le sgV (liftLabCtx k q ps) (.nat fl) gAV
        have := wt_nat_le fl; omega) (by omega)).mono (by omega) le_rfl
  have hout : (Val.list [sgV, liftLabCtx k q ps, .nat fl, gAV]).wt ≤ W := by
    have := wt_list4_le sgV (liftLabCtx k q ps) (.nat fl) gAV
    have := wt_nat_le fl; omega
  have dall := StDC.letE d1 (StDC.letE d2 (StDC.letE d3 (StDC.letE d4 (StDC.letE d5
    (StDC.letE d6 (StDC.letE d7 (StDC.letE d8 d9 hout) hout) hout) hout) hout) hout) hout) hout
  refine StDC.funDet hf dall ?_
  -- the cost
  have e6 : B ^ 6 = (M + 1) ^ 6 := rfl
  unfold itHvDaC
  omega

end GI.Impl
