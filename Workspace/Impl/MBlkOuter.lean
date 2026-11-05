module

public import Workspace.Impl.MBlkClos

@[expose] public section

/-!
# The outer rounds, as a program

* `mblkTestFuns`: a `foldl` over the representatives that tests whether some point has a
  representative other than a given one, so whether a partition has at least two classes.
* `mblkOuterF`: one outer step `mblkOuterStep gs z lab b` with `z = 0`: join the classes of `0`
  and `b`, take the closure, and keep it when the test says it has two classes.
* `mblkOuterFoldFuns`: a `foldl` of the outer steps over the points (`mblkOuterRound`).
* `mblkOuterIterFuns`: `n` outer rounds from the identity (`mblkResult`).

The context of the outer steps is `C = [[mids n, gens], n]`.
-/

namespace GI.Impl

open GI.Lang GI.Cited Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-! ### The test for two classes -/

/-- The step of the test's `foldl`: on `[c0, acc, l]`, `acc` if `l = c0`, else `1`. -/
def mblkTestF : Expr := .ite (.arith .eq (arg 2) (arg 0)) (arg 1) (.nat 1)

theorem mblkTestF_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some mblkTestF) {c0 l : ℕ}
    (hc0 : c0 ≤ n) (hl : l ≤ n) (B : Bool) :
    FunDet P f (.list [.nat c0, boolVal B, .nat l]) (boolVal (B || decide (l ≠ c0)))
      (300 * (n + 1)) := by
  set A := Val.list [.nat c0, boolVal B, .nat l] with hA
  have d0 := Det.arg' (P := P) (rest := []) (vs := [.nat c0, boolVal B, .nat l]) (j := 0) rfl
  have d1 := Det.arg' (P := P) (rest := []) (vs := [.nat c0, boolVal B, .nat l]) (j := 1) rfl
  have d2 := Det.arg' (P := P) (rest := []) (vs := [.nat c0, boolVal B, .nat l]) (j := 2) rfl
  have dc := Det.arith' (op := .eq) d2 d0 rfl
  have dt := Det.ite' dc d1 (Det.nat (P := P) (env := [A]) 1)
  have hv : (if BinOp.eval .eq l c0 = 0 then Val.nat 1 else boolVal B) =
      boolVal (B || decide (l ≠ c0)) := by
    simp only [BinOp.eval]
    by_cases h : l = c0 <;> simp [h]
  rw [hv] at dt
  refine FunDet.intro hf (dt.mono ?_)
  have h1 := wt_nat_le c0
  have h2 := wt_boolVal_le B
  have h3 := wt_nat_le l
  have h4 : A.wt ≤ 2 * ((Val.nat c0).wt + (boolVal B).wt + (Val.nat l).wt) + 7 :=
    wt_list3_le _ _ _
  have h5 := wt_boolVal_le (B || decide (l ≠ c0))
  have h6 := wt_nat_le 1
  have h8 : BinOp.eval .eq l c0 ≤ 1 := by simp only [BinOp.eval]; split_ifs <;> omega
  have e : (Val.list [.nat c0, boolVal B, .nat l]).wt = A.wt := rfl
  omega

/-- The test, at base `b` (four functions): on `[c0, mlab lab, 0]`, the value `1` if some point
has a representative other than `c0`, else `0`. -/
def mblkTestFuns (b : ℕ) : List Expr := foldlFuns b (b + 3) ++ [mblkTestF]

theorem mblkTest_spec {P : Program} {b : ℕ} (h : P.HasAt b (mblkTestFuns b))
    (lab : Fin n → Fin n) {c0 : ℕ} (hc0 : c0 ≤ n) :
    FunDet P b (.list [.nat c0, mlab lab, .nat 0])
      (boolVal (decide (∃ x, (lab x : ℕ) ≠ c0))) (40000 * (n + 1) ^ 3) := by
  have hf : P.funs[b + 3]? = some mblkTestF := by
    simpa [mblkTestFuns, foldlFuns, loopFuns] using h.right.single
  set xs := (List.finRange n).map fun i : Fin n => Val.nat (lab i : ℕ) with hxs
  have hlen : xs.length = n := by simp [hxs]
  have hF := foldl_spec h.left (c := .nat c0) (xs := xs) (acc0 := .nat 0)
    (Inv := fun i acc => acc = boolVal (((List.finRange n).take i).any
      fun x => decide ((lab x : ℕ) ≠ c0)))
    (M := 3) (B := fun _ => 300 * (n + 1)) (by simp)
    (fun i acc _ hacc => hacc ▸ wt_boolVal_le _)
    (fun i acc hi hacc => by
      subst hacc
      have hi' : i < (List.finRange n).length := by simpa [hxs] using hi
      have e : xs[i] = Val.nat (lab (List.finRange n)[i] : ℕ) := by simp [hxs]
      rw [e]
      refine FunAll.mono (mblkTestF_spec hf hc0 (lab _).isLt.le _) fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
        List.any_append, List.any_cons, List.any_nil, Bool.or_false])
  refine hF.mono fun w cost hw => ?_
  obtain ⟨hw1, hc⟩ := hw
  rw [hlen, List.take_of_length_le (by simp)] at hw1
  refine ⟨?_, ?_⟩
  · rw [hw1]
    congr 2
    rw [Bool.eq_iff_iff]
    simp
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, hlen] at hc
  have h2 := wt_mlab_le lab
  have h4 := wt_list3_le (.nat c0) (.list xs) (.nat 0)
  have h5 := wt_nat_le c0
  have h6 := wt_nat_le 0
  have e1 : (Val.list xs).wt = (mlab lab).wt := rfl
  have hN1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hN : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have h7 : loopModK * (n + 1) * ((Val.list [.nat c0, .list xs, .nat 0]).wt + n + 3 + 1) ≤
      loopModK * (n + 1) * (30 * (n + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
  have e7 : loopModK * (n + 1) * (30 * (n + 1) ^ 2) = 30000 * (n + 1) ^ 3 := by
    simp only [loopModK]; ring
  have h8 : n * (300 * (n + 1)) ≤ 300 * (n + 1) ^ 3 := by
    have : n * (n + 1) ≤ (n + 1) ^ 3 := by
      calc n * (n + 1) ≤ (n + 1) * (n + 1) := Nat.mul_le_mul_right _ (by omega)
        _ = (n + 1) ^ 2 := by ring
        _ ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    have e : n * (300 * (n + 1)) = 300 * (n * (n + 1)) := by ring
    omega
  omega

/-! ### One outer step -/

/-- The context of the outer steps. -/
abbrev mctx (gs : List (Perm (Fin n))) : Val :=
  .list [.list [mids n, .list (gs.map encPerm)], .nat n]

theorem wt_mctx_le (gs : List (Perm (Fin n))) :
    (mctx gs).wt ≤ 100 * ((gs.length + 1) * (n + 1)) ^ 2 := by
  have h1 := wt_mids_le n
  have h2 := wt_list_encPerms_le gs
  have h3 := wt_list2_le (mids n) (.list (gs.map encPerm))
  have h4 := wt_list2_le (.list [mids n, .list (gs.map encPerm)]) (.nat n)
  have h5 := wt_nat_le n
  have e : (mctx gs).wt = (Val.list [.list [mids n, .list (gs.map encPerm)], .nat n]).wt := rfl
  generalize hS : (gs.length + 1) * (n + 1) = S at h2 ⊢
  have hNS : n + 1 ≤ S := hS ▸ Nat.le_mul_of_pos_left _ (by omega)
  have hN2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hNS 2
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  omega

/-- On `[C, mlab lab, b]`: `mlab (mblkOuterStep gs 0 lab b)`. -/
def mblkOuterF (mm cl tst : ℕ) : Expr :=
  .letE (.call mm (mk2 (mk2 (.get (arg 1) (.nat 0)) (.get (arg 1) (arg 2))) (arg 1)))
    (.letE (.call cl (mk3 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.var 1)))
      (.ite (.call tst (mk3 (.get (.var 2) (.nat 0)) (.var 2) (.nat 0))) (.var 2) (arg 1)))

/-- The layout of the functions an outer step calls. -/
structure MOuterAt (P : Program) (mm cl rf gf tst : ℕ) : Prop where
  merge : P.HasAt mm (mblkMergeFuns mm)
  clos : P.HasAt cl (mblkClosFuns cl rf)
  round : P.HasAt rf (mblkRoundFuns rf gf)
  gen : P.HasAt gf (mblkGenFuns gf mm)
  test : P.HasAt tst (mblkTestFuns tst)

theorem mblkOuterF_spec {P : Program} {f mm cl rf gf tst : ℕ}
    (hf : P.funs[f]? = some (mblkOuterF mm cl tst)) (hA : MOuterAt P mm cl rf gf tst)
    (gs : List (Perm (Fin n))) (hn : 0 < n) (lab : Fin n → Fin n) (b : Fin n) :
    FunDet P f (.list [mctx gs, mlab lab, .nat b]) (mlab (mblkOuterStep gs ⟨0, hn⟩ lab b))
      (1000000 * ((gs.length + 1) * (n + 1)) ^ 6) := by
  set z : Fin n := ⟨0, hn⟩ with hz
  set A := Val.list [mctx gs, mlab lab, .nat b] with hA'
  set M := mblkMerge lab z b with hM
  set c := mblkClos gs M with hc
  have da := Det.get' (P := P) (env := [A])
    (Det.arg' (rest := []) (vs := [mctx gs, mlab lab, .nat b]) (j := 1) rfl) (Det.nat 0)
    (encFun_getElem? (fun y => (lab y : ℕ)) z)
  have db := Det.get' (P := P) (env := [A])
    (Det.arg' (rest := []) (vs := [mctx gs, mlab lab, .nat b]) (j := 1) rfl)
    (Det.arg' (j := 2) rfl) (encFun_getElem? (fun y => (lab y : ℕ)) b)
  have dL := Det.arg' (P := P) (rest := []) (vs := [mctx gs, mlab lab, .nat b]) (j := 1) rfl
  have d1 := Det.call (Det.mk2 (Det.mk2 da db) dL) (mblkMerge_spec hA.merge lab z b)
  have g0 := Det.get' (P := P) (env := [A, mlab M])
    (Det.arg' (rest := [mlab M]) (vs := [mctx gs, mlab lab, .nat b]) (j := 0) rfl)
    (Det.nat 0) (show [Val.list [mids n, .list (gs.map encPerm)], .nat n][0]? = some _ from rfl)
  have g1 := Det.get' (P := P) (env := [A, mlab M])
    (Det.arg' (rest := [mlab M]) (vs := [mctx gs, mlab lab, .nat b]) (j := 0) rfl)
    (Det.nat 1) (show [Val.list [mids n, .list (gs.map encPerm)], .nat n][1]? = some _ from rfl)
  have d2 := Det.call (Det.mk3 g0 g1 (Det.var' (P := P) (env := [A, mlab M]) (i := 1) rfl))
    (mblkClos_spec hA.clos hA.round hA.gen hA.merge gs M)
  set E := [A, mlab M, mlab c] with hE
  have t0 := Det.get' (P := P) (env := E) (Det.var' (i := 2) rfl) (Det.nat 0)
    (encFun_getElem? (fun y => (c y : ℕ)) z)
  have d3 := Det.call (Det.mk3 t0 (Det.var' (P := P) (env := E) (i := 2) rfl) (Det.nat 0))
    (mblkTest_spec hA.test c (c z).isLt.le)
  have dt := Det.ite' d3 (Det.var' (P := P) (env := E) (i := 2) rfl)
    (Det.arg' (P := P) (rest := [mlab M, mlab c]) (vs := [mctx gs, mlab lab, .nat b]) (j := 1) rfl)
  have hv : (if (decide (∃ x, (c x : ℕ) ≠ (c z : ℕ))).toNat = 0 then mlab lab else mlab c) =
      mlab (mblkOuterStep gs z lab b) := by
    have e : (∃ x, (c x : ℕ) ≠ (c z : ℕ)) ↔ ∃ x, mblkTry gs z lab b x ≠ mblkTry gs z lab b z := by
      simp only [ne_eq, Fin.val_inj]; rfl
    unfold mblkOuterStep
    by_cases h : ∃ x, mblkTry gs z lab b x ≠ mblkTry gs z lab b z
    · rw [if_pos h, if_neg (by simp [e.mpr h])]; rfl
    · rw [if_neg h, if_pos (by simp only [decide_eq_false (mt e.mp h)]; rfl)]
  rw [hv] at dt
  refine FunDet.intro hf ((Det.letE d1 (Det.letE d2 dt)).mono ?_)
  -- the cost
  have w1 := wt_mlab_le lab
  have w2 := wt_mlab_le M
  have w3 := wt_mlab_le c
  have w4 := wt_mlab_le (mblkOuterStep gs z lab b)
  have w5 := wt_mctx_le gs
  have w6 := wt_nat_le b
  have w7 : A.wt ≤ 2 * ((mctx gs).wt + (mlab lab).wt + (Val.nat b).wt) + 7 := wt_list3_le _ _ _
  have w8 := wt_nat_le (lab z)
  have w9 := wt_nat_le (lab b)
  have w10 := wt_list2_le (.nat (lab z)) (.nat (lab b))
  have w11 := wt_list2_le (.list [.nat (lab z), .nat (lab b)]) (mlab lab)
  have w12 := wt_mids_le n
  have w13 := wt_list_encPerms_le gs
  have w14 := wt_list2_le (mids n) (.list (gs.map encPerm))
  have w15 := wt_list3_le (.list [mids n, .list (gs.map encPerm)]) (.nat n) (mlab M)
  have w16 := wt_nat_le n
  have w17 := wt_nat_le (c z)
  have w18 := wt_list3_le (.nat (c z)) (mlab c) (.nat 0)
  have w19 := wt_boolVal_le (decide (∃ x, (c x : ℕ) ≠ (c z : ℕ)))
  have w20 := wt_nat_le 0
  have e1 : (Val.list [mctx gs, mlab lab, .nat b]).wt = A.wt := rfl
  have k1 : (mlab (mblkMerge lab z b)).wt ≤ 4 * (n + 1) ^ 2 := wt_mlab_le _
  have k2 : (mlab (mblkClos gs M)).wt ≤ 4 * (n + 1) ^ 2 := wt_mlab_le _
  have k3 : (Val.list ((List.finRange n).map fun i => Val.nat ((fun x => (c x : ℕ)) i))).wt ≤
      4 * (n + 1) ^ 2 := wt_mlab_le c
  have k4 : (if (mlab c).wt ≤ (mlab lab).wt then (mlab lab).wt else (mlab c).wt) ≤
      4 * (n + 1) ^ 2 := by split <;> omega
  have := b.isLt
  have := (lab z).isLt
  have := (lab b).isLt
  have := (c z).isLt
  generalize hS : (gs.length + 1) * (n + 1) = S at w5 w13 ⊢
  have hNS : n + 1 ≤ S := hS ▸ Nat.le_mul_of_pos_left _ (by omega)
  have hS1 : 1 ≤ S := le_trans (by omega) hNS
  have hN2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hNS 2
  have hN3 : (n + 1) ^ 3 ≤ S ^ 3 := Nat.pow_le_pow_left hNS 3
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have hS23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by omega)
  have hS36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by omega)
  omega

/-! ### One outer round -/

/-- The outer round's `foldl`, at base `b` (four functions): on `[C, mids n, mlab lab]`, the
value `mlab (mblkOuterRound gs 0 lab)`. -/
def mblkOuterFoldFuns (b mm cl tst : ℕ) : List Expr := foldlFuns b (b + 3) ++ [mblkOuterF mm cl tst]

theorem mblkOuterFold_spec {P : Program} {b mm cl rf gf tst : ℕ}
    (h : P.HasAt b (mblkOuterFoldFuns b mm cl tst)) (hA : MOuterAt P mm cl rf gf tst)
    (gs : List (Perm (Fin n))) (hn : 0 < n) (lab : Fin n → Fin n) :
    FunDet P b (.list [mctx gs, mids n, mlab lab]) (mlab (mblkOuterRound gs ⟨0, hn⟩ lab))
      (1300000 * ((gs.length + 1) * (n + 1)) ^ 7) := by
  have hf : P.funs[b + 3]? = some (mblkOuterF mm cl tst) := by
    simpa [mblkOuterFoldFuns, foldlFuns, loopFuns] using h.right.single
  set xs := (List.finRange n).map fun i : Fin n => Val.nat (i : ℕ) with hxs
  have hlen : xs.length = n := by simp [hxs]
  have hF := foldl_spec h.left (c := mctx gs) (xs := xs) (acc0 := mlab lab)
    (Inv := fun i acc => acc = mlab (((List.finRange n).take i).foldl
      (mblkOuterStep gs ⟨0, hn⟩) lab))
    (M := 4 * (n + 1) ^ 2) (B := fun _ => 1000000 * ((gs.length + 1) * (n + 1)) ^ 6) (by simp)
    (fun i acc _ hacc => hacc ▸ wt_mlab_le _)
    (fun i acc hi hacc => by
      subst hacc
      have hi' : i < (List.finRange n).length := by simpa [hxs] using hi
      have e : xs[i] = Val.nat ((List.finRange n)[i] : ℕ) := by simp [hxs]
      rw [e]
      refine FunAll.mono (mblkOuterF_spec hf hA gs hn _ (List.finRange n)[i])
        fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, List.take_add_one, List.getElem?_eq_getElem hi', Option.toList_some,
        List.foldl_append]
      rfl)
  refine hF.mono fun w cost hw => ?_
  obtain ⟨hw1, hc⟩ := hw
  rw [hlen, List.take_of_length_le (by simp)] at hw1
  refine ⟨hw1, ?_⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, hlen] at hc
  have h1 := wt_mctx_le gs
  have h2 := wt_mlab_le lab
  have h3 := wt_mids_le n
  have h4 := wt_list3_le (mctx gs) (.list xs) (mlab lab)
  have e1 : (Val.list xs).wt = (mids n).wt := rfl
  generalize hS : (gs.length + 1) * (n + 1) = S at h1 hc ⊢
  have hNS : n + 1 ≤ S := hS ▸ Nat.le_mul_of_pos_left _ (by omega)
  have hS1 : 1 ≤ S := le_trans (by omega) hNS
  have hN2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hNS 2
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have h5 : loopModK * (n + 1) * ((Val.list [mctx gs, .list xs, mlab lab]).wt + n +
      4 * (n + 1) ^ 2 + 1) ≤ loopModK * S * (300 * S ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hNS) (by omega)
  have e5 : loopModK * S * (300 * S ^ 2) = 300000 * S ^ 3 := by simp only [loopModK]; ring
  have h6 : n * (1000000 * S ^ 6) ≤ 1000000 * S ^ 7 := by
    have : n * S ^ 6 ≤ S ^ 7 := by
      rw [pow_succ, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    have e : n * (1000000 * S ^ 6) = 1000000 * (n * S ^ 6) := by ring
    omega
  have h7 : S ^ 3 ≤ S ^ 7 := Nat.pow_le_pow_right hS1 (by omega)
  omega

/-! ### The outer rounds -/

/-- The body of the outer iteration: on `[C, i, mlab lab]`, one outer round. -/
def mblkIterOuterF (of : ℕ) : Expr :=
  .call of (mk3 (arg 0) (.get (.get (arg 0) (.nat 0)) (.nat 0)) (arg 2))

theorem mblkIterOuter_spec {P : Program} {f ofb mm cl rf gf tst : ℕ}
    (hf : P.funs[f]? = some (mblkIterOuterF ofb)) (ho : P.HasAt ofb (mblkOuterFoldFuns ofb mm cl tst))
    (hA : MOuterAt P mm cl rf gf tst) (gs : List (Perm (Fin n))) (hn : 0 < n)
    (lab : Fin n → Fin n) {i : ℕ} (hi : i ≤ n) :
    FunDet P f (.list [mctx gs, .nat i, mlab lab]) (mlab (mblkOuterRound gs ⟨0, hn⟩ lab))
      (1400000 * ((gs.length + 1) * (n + 1)) ^ 7) := by
  have g0 := Det.arg' (P := P) (rest := []) (vs := [mctx gs, .nat i, mlab lab]) (j := 0) rfl
  have g1 := Det.get' (P := P) (Det.get' g0 (Det.nat 0)
    (show [Val.list [mids n, .list (gs.map encPerm)], .nat n][0]? = some _ from rfl)) (Det.nat 0)
    (show [mids n, Val.list (gs.map encPerm)][0]? = some _ from rfl)
  have g2 := Det.arg' (P := P) (rest := []) (vs := [mctx gs, .nat i, mlab lab]) (j := 2) rfl
  refine FunDet.intro hf ((Det.call (Det.mk3 g0 g1 g2)
    (mblkOuterFold_spec ho hA gs hn lab)).mono ?_)
  have h1 := wt_mlab_le lab
  have h2 := wt_mids_le n
  have h3 := wt_mlab_le (mblkOuterRound gs ⟨0, hn⟩ lab)
  have h4 := wt_mctx_le gs
  have h5 := wt_list3_le (mctx gs) (.nat i) (mlab lab)
  have h6 := wt_list3_le (mctx gs) (mids n) (mlab lab)
  have h7 := wt_list2_le (mids n) (.list (gs.map encPerm))
  have h8 := wt_nat_le i
  have h9 : (mids n).wt < (Val.list [mids n, .list (gs.map encPerm)]).wt := wt_le_wt_list (by simp)
  have h10 : (Val.list [mids n, .list (gs.map encPerm)]).wt < (mctx gs).wt :=
    wt_le_wt_list (by simp)
  generalize hS : (gs.length + 1) * (n + 1) = S at h4 ⊢
  have hNS : n + 1 ≤ S := hS ▸ Nat.le_mul_of_pos_left _ (by omega)
  have hS1 : 1 ≤ S := le_trans (by omega) hNS
  have hN2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hNS 2
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have hS7 : S ^ 2 ≤ S ^ 7 := Nat.pow_le_pow_right hS1 (by omega)
  omega

/-- `n` outer rounds, at base `b` (four functions): on `[C, n, mids n]`, the value
`mlab (mblkResult gs 0)`. -/
def mblkOuterIterFuns (b ofb : ℕ) : List Expr := iterFuns b (b + 3) ++ [mblkIterOuterF ofb]

theorem mblkOuterIter_spec {P : Program} {b ofb mm cl rf gf tst : ℕ}
    (h : P.HasAt b (mblkOuterIterFuns b ofb)) (ho : P.HasAt ofb (mblkOuterFoldFuns ofb mm cl tst))
    (hA : MOuterAt P mm cl rf gf tst) (gs : List (Perm (Fin n))) (hn : 0 < n) :
    FunDet P b (.list [mctx gs, .nat n, mids n]) (mlab (mblkResult gs ⟨0, hn⟩))
      (1800000 * ((gs.length + 1) * (n + 1)) ^ 8) := by
  have hf : P.funs[b + 3]? = some (mblkIterOuterF ofb) := by
    simpa [mblkOuterIterFuns, iterFuns, loopFuns] using h.right.single
  have hI := iter_spec h.left (c := mctx gs) (k := n) (acc0 := mids n)
    (Inv := fun i acc => acc = mlab ((mblkOuterRound gs ⟨0, hn⟩)^[i] id))
    (M := 4 * (n + 1) ^ 2) (B := fun _ => 1400000 * ((gs.length + 1) * (n + 1)) ^ 7) rfl
    (fun i acc _ hacc => hacc ▸ wt_mlab_le _)
    (fun i acc hi hacc => by
      subst hacc
      refine FunAll.mono (mblkIterOuter_spec hf ho hA gs hn _ hi.le) fun w c hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, Function.iterate_succ_apply'])
  refine hI.mono fun w cost hw => ⟨hw.1, ?_⟩
  have hc' := hw.2
  rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc'
  have h1 := wt_mids_le n
  have h4 := wt_mctx_le gs
  have h6 := wt_list3_le (mctx gs) (.nat n) (mids n)
  have h8 := wt_nat_le n
  generalize hS : (gs.length + 1) * (n + 1) = S at h4 hc' ⊢
  have hNS : n + 1 ≤ S := hS ▸ Nat.le_mul_of_pos_left _ (by omega)
  have hS1 : 1 ≤ S := le_trans (by omega) hNS
  have hN2 : (n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hNS 2
  have hS2 : S ≤ S ^ 2 := Nat.le_self_pow (by omega) _
  have h7 : loopModK * (n + 1) * ((Val.list [mctx gs, .nat n, mids n]).wt + n +
      4 * (n + 1) ^ 2 + 1) ≤ loopModK * S * (300 * S ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ hNS) (by omega)
  have e7 : loopModK * S * (300 * S ^ 2) = 300000 * S ^ 3 := by simp only [loopModK]; ring
  have h9 : n * (1400000 * S ^ 7) ≤ 1400000 * S ^ 8 := by
    have : n * S ^ 7 ≤ S ^ 8 := by
      rw [pow_succ, Nat.mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
    have e : n * (1400000 * S ^ 7) = 1400000 * (n * S ^ 7) := by ring
    omega
  have h10 : S ^ 3 ≤ S ^ 8 := Nat.pow_le_pow_right hS1 (by omega)
  omega

end GI.Impl
