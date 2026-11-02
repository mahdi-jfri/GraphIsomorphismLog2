import Workspace.Impl.VsQTopM

/-!
# The entry

On the task input `[encGroup gs, p, matrices, encVec v]` the program `vsQTopE` builds the global
context `Γ = vsQGam I` (the exponent `E = n! - 2`, the table of the input matrices in the carried
form `[p, 0^d, E, Mᵀ]`, and the identity), cuts the generators to at most `n²` (`reduce`),
runs the driver on the initial state `vsQ0` and returns the generators of the stabilizer.

* `vsQFact_spec`: `n!` by a fold.
* `vsQTbl0_spec`: the table.
* `vsQTop_spec`: the entry, with the driver as a hypothesis.
-/

open Matrix Module

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

theorem vsQ_memCost_mono (h : Membership) {n n' : ℕ} (hn : n ≤ n') : memCost h n ≤ memCost h n' := by
  unfold memCost
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left (by omega) 6)) _)

theorem vsQ_reduceCost_mono_n (h : Membership) {n n' : ℕ} (hn : n ≤ n') (m : ℕ) :
    reduceCost h n m ≤ reduceCost h n' m := by
  unfold reduceCost
  have h1 := Nat.mul_le_mul_left (m + 1) (vsQ_memCost_mono h hn)
  have h2 : ((m + 2) * (n + 1)) ^ 6 ≤ ((m + 2) * (n' + 1)) ^ 6 :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left _ (by omega)) 6
  have h3 := Nat.mul_le_mul_left reduceK h2
  omega

theorem vsQ_wt_fact (r : ℕ) : (Val.nat r.factorial).wt ≤ r ^ 2 + 3 := by
  rw [wt_nat]
  have h1 : r.factorial < 2 ^ (r ^ 2) + 1 := by
    have := Nat.factorial_le_pow r
    have h2 : r ^ r ≤ (2 ^ r) ^ r := Nat.pow_le_pow_left Nat.lt_two_pow_self.le r
    rw [← pow_mul, ← sq] at h2
    omega
  have : GI.Machine.len r.factorial ≤ r ^ 2 + 1 := by
    apply GI.Machine.len_le_iff.mpr
    have := Nat.one_le_two_pow (n := r ^ 2)
    rw [pow_succ]; omega
  omega

/-- The step of the factorial, on `[c, acc, x]`: `acc (x + 1)`. -/
def vsQFactStepE : Expr := .arith .mul (arg 1) (.arith .add (arg 2) (.nat 1))

/-- The factorial fold. -/
def vsQFactG (acc x : Val) : Val :=
  match acc, x with
  | .nat a, .nat k => .nat (a * (k + 1))
  | _, _ => .nat 0

theorem vsQFact_take (n i : ℕ) (hi : i ≤ n) :
    (((List.range n).map Val.nat).take i).foldl vsQFactG (.nat 1) = .nat i.factorial := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.take_add_one, List.foldl_append, ih (by omega)]
    have hi' : i < ((List.range n).map Val.nat).length := by simp; omega
    rw [List.getElem?_eq_getElem hi']
    simp [vsQFactG, Nat.factorial_succ, mul_comm]

set_option maxHeartbeats 4000000 in
/-- **The factorial.** On `[0, range n, 1]` the fold returns `n!`. -/
theorem vsQFact_spec {P : Program} {fold st : ℕ} (hfold : P.HasAt fold (foldlFuns fold st))
    (hst : P.funs[st]? = some vsQFactStepE) (n : ℕ) :
    FunDet P fold (.list [.nat 0, natList (List.range n), .nat 1]) (.nat n.factorial)
      (10 ^ 6 * (n + 1) ^ 4) := by
  have hfin : ((List.range n).map Val.nat).foldl vsQFactG (.nat 1) = .nat n.factorial := by
    have := vsQFact_take n n le_rfl
    rwa [List.take_of_length_le (by simp)] at this
  have hsp := foldl_spec_fun hfold (c := .nat 0) (xs := (List.range n).map Val.nat) (acc0 := .nat 1)
    (G := vsQFactG) (M := n ^ 2 + 3) (B := fun _ => 100 * (n + 1) ^ 2)
    (fun i hi => by
      rw [vsQFact_take n i (by simpa using hi)]
      have := vsQ_wt_fact i
      have : i ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left (by simpa using hi) 2
      omega)
    (fun i hi => by
      rw [vsQFact_take n i (by simp at hi; omega)]
      have hx : ((List.range n).map Val.nat)[i] = .nat i := by simp
      rw [hx]
      refine FunDet.intro hst ?_
      have a1 := Det.arg' (P := P) (vs := [Val.nat 0, .nat i.factorial, .nat i]) (rest := []) (j := 1) rfl
      have a2 := Det.arg' (P := P) (vs := [Val.nat 0, .nat i.factorial, .nat i]) (rest := []) (j := 2) rfl
      have d := Det.arith (op := .mul) a1 (Det.arith (op := .add) a2 (Det.nat (P := P)
        (env := [Val.list [.nat 0, .nat i.factorial, .nat i]]) 1))
      have e : vsQFactG (.nat i.factorial) (.nat i) = .nat (GI.Machine.BinOp.eval .mul i.factorial
          (GI.Machine.BinOp.eval .add i 1)) := rfl
      rw [e]
      refine d.mono ?_
      have hin : i < n := by simpa using hi
      have w1 := vsQ_wt_fact i
      have w2 := wt_nat_le i
      have w3 := wt_nat_le 0
      have w4 := wt_nat_le 1
      have l3 := wt_list3_le (.nat 0) (.nat i.factorial) (.nat i)
      have w5 : (Val.nat (GI.Machine.BinOp.eval .add i 1)).wt ≤ i + 3 := wt_nat_le _
      have w6 : (Val.nat (GI.Machine.BinOp.eval .mul i.factorial (GI.Machine.BinOp.eval .add i 1))).wt ≤
          (i + 1) ^ 2 + 3 := by
        have : GI.Machine.BinOp.eval .mul i.factorial (GI.Machine.BinOp.eval .add i 1) = (i + 1).factorial := by
          simp [GI.Machine.BinOp.eval, Nat.factorial_succ, mul_comm]
        rw [this]; exact vsQ_wt_fact (i + 1)
      have hev : GI.Machine.BinOp.eval .add i 1 = i + 1 := rfl
      have q1 : i ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have q2 : (i + 1) ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      have q3 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _

      beta_reduce
      omega)
  refine hsp.mono ?_ |> fun h => by rw [hfin] at h; exact h
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, List.length_map, List.length_range]
  have wr : (natList (List.range n)).wt ≤ 5 * (n + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp at hy; omega) (by simp)
  have l3 := wt_list3_le (.nat 0) (natList (List.range n)) (.nat 1)
  have := wt_nat_le 0; have := wt_nat_le 1
  have e : (Val.list ((List.range n).map Val.nat)).wt = (natList (List.range n)).wt := rfl
  have q2 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q3 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q4 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q5 : (n + 1) ^ 3 ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : n * (100 * (n + 1) ^ 2) ≤ (n + 1) * (100 * (n + 1) ^ 2) := Nat.mul_le_mul_right _ (by omega)
  have e1 : (n + 1) * (100 * (n + 1) ^ 2) = 100 * (n + 1) ^ 3 := by ring
  have h2 : loopModK * (n + 1) * ((Val.list [Val.nat 0, Val.list ((List.range n).map Val.nat), Val.nat 1]).wt +
      n + (n ^ 2 + 3) + 1) ≤ 1000 * (n + 1) * (100 * (n + 1) ^ 2) :=
    Nat.mul_le_mul (le_refl _) (by
      have e' : (Val.list [Val.nat 0, Val.list ((List.range n).map Val.nat), Val.nat 1]).wt =
        (Val.list [Val.nat 0, natList (List.range n), Val.nat 1]).wt := rfl
      omega)
  have e2 : 1000 * (n + 1) * (100 * (n + 1) ^ 2) = 10 ^ 5 * (n + 1) ^ 3 := by ring
  have mk : loopModK = 1000 := rfl
  omega

/-- The table item, on `[[p, z, E, d], M]`: `[p, z, E, Mᵀ]`. -/
def vsQTblItE (tr : ℕ) : Expr :=
  mk4 (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2))
    (.call tr (mk2 (arg 1) (.get (arg 0) (.nat 3))))

set_option maxHeartbeats 4000000 in
theorem vsQTblIt_spec {P : Program} {it tr : ℕ} (hit : P.funs[it]? = some (vsQTblItE tr))
    (htr : P.HasAt tr (vsQTrFuns tr)) {N E : ℕ} (hpN : I.p ≤ N) (hdN : I.d ≤ N) (hE : (Val.nat E).wt ≤ N)
    (M : Matrix (Fin I.d) (Fin I.d) (ZMod I.p)) :
    FunDet P it (.list [.list [.nat I.p, natList (List.replicate I.d 0), .nat E, .nat I.d], encModMatrix M])
      (vsQE I.p I.d E M) (10 ^ 7 * (N + 1) ^ 5) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  set c := Val.list [.nat I.p, natList (List.replicate I.d 0), .nat E, .nat I.d]
  have g0 := Det.arg' (P := P) (vs := [c, encModMatrix M]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [c, encModMatrix M]) (rest := []) (j := 1)
    (v := .list ((vsQL M).map natList)) (by rw [encModMatrix_eq]; rfl)
  have c0 := Det.get' g0 (Det.nat 0) (show [Val.nat I.p, natList (List.replicate I.d 0), .nat E, .nat I.d][0]? =
    some (.nat I.p) from rfl)
  have c1 := Det.get' g0 (Det.nat 1) (show [Val.nat I.p, natList (List.replicate I.d 0), .nat E, .nat I.d][1]? =
    some (natList (List.replicate I.d 0)) from rfl)
  have c2 := Det.get' g0 (Det.nat 2) (show [Val.nat I.p, natList (List.replicate I.d 0), .nat E, .nat I.d][2]? =
    some (.nat E) from rfl)
  have c3 := Det.get' g0 (Det.nat 3) (show [Val.nat I.p, natList (List.replicate I.d 0), .nat E, .nat I.d][3]? =
    some (.nat I.d) from rfl)
  have dtr := Det.call (Det.mk2 g1 c3) (vsQTr_spec htr hpN hdN (vsQL_sq M))
  rw [vsQL_tr] at dtr
  have dout := Det.mk4 c0 c1 c2 dtr
  refine FunDet.intro hit (dout.mono ?_)
  have wz : (natList (List.replicate I.d 0)).wt ≤ 5 * (N + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp at hy; omega) (by simp; omega)
  have wM : (Val.list ((vsQL M).map natList)).wt ≤ 11 * (N + 1) ^ 3 + 4 := wt_vsFSq_le hpN hdN (vsQL_sq M)
  have wMt : (Val.list ((vsQL Mᵀ).map natList)).wt ≤ 11 * (N + 1) ^ 3 + 4 := wt_vsFSq_le hpN hdN (vsQL_sq Mᵀ)
  have eM : (encModMatrix M).wt = (Val.list ((vsQL M).map natList)).wt := by rw [encModMatrix_eq]
  have := wt_nat_le I.p; have := wt_nat_le I.d; have := wt_nat_le 0; have := wt_nat_le 1
  have := wt_nat_le 2; have := wt_nat_le 3
  have l4 := wt_list4_le (.nat I.p) (natList (List.replicate I.d 0)) (.nat E) (.nat I.d)
  have ec : c.wt = (Val.list [.nat I.p, natList (List.replicate I.d 0), .nat E, .nat I.d]).wt := rfl
  have l2 := wt_list2_le c (encModMatrix M)
  have l2' := wt_list2_le (.list ((vsQL M).map natList)) (.nat I.d)
  have l4' := wt_list4_le (.nat I.p) (natList (List.replicate I.d 0)) (.nat E) (.list ((vsQL Mᵀ).map natList))
  have q12 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q23 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q35 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q1 : 1 ≤ (N + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  have eE : (vsQE I.p I.d E M).wt = (Val.list [.nat I.p, natList (List.replicate I.d 0), .nat E,
    .list ((vsQL Mᵀ).map natList)]).wt := rfl
  clear_value c
  omega

theorem vsQL_one_tr {p d : ℕ} (hp : 1 < p) :
    vsQL ((1 : Matrix (Fin d) (Fin d) (ZMod p))ᵀ) = vsWId d := by
  haveI : Fact (1 < p) := ⟨hp⟩
  apply List.ext_getElem (by simp [vsQL, vsWId])
  intro i h1 h2
  simp only [vsQL, vsWId, List.getElem_map, List.getElem_finRange, List.getElem_range, vsUnit]
  apply List.ext_getElem (by simp)
  intro j k1 k2
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, transpose_apply, one_apply]
  by_cases hij : j = i
  · subst hij; simp [ZMod.val_one]
  · rw [if_neg (fun h => hij (by simpa [Fin.ext_iff] using h)), if_neg hij]; simp

/-- The task input. -/
noncomputable def vsQTaskIn (I : VecStabInst) : Val :=
  .list [encGroup I.gs, .nat I.p,
    .list (I.gs.attach.map fun g => encModMatrix (I.φ ⟨g.1, Subgroup.subset_closure g.2⟩).val), encVec I.v]

/-- The entry, on the task input. -/
def vsQTopE (rng fold idp rep tbm red drv tl : ℕ) : Expr :=
  .letE (.length (arg 3))
  (.letE (.arith .sub (.call fold (mk3 (.nat 0) (.call rng (.get (arg 0) (.nat 0))) (.nat 1))) (.nat 2))
  (.letE (.call idp (.var 1))
  (.letE (.call rep (mk2 (.var 1) (.nat 0)))
  (.letE (.call tbm (mk2 (mk4 (arg 1) (.var 4) (.var 2) (.var 1)) (arg 2)))
  (.letE (.call red (arg 0))
  (.letE (.call drv (mk6 (mk3 (arg 0) (.var 5) (mk4 (arg 1) (.var 4) (.var 2) (.var 3))) (.var 6) .nil (.var 3)
      (arg 3) (arg 3)))
    (.call tl (.get (.get (.var 7) (.nat 2)) (.nat 1)))))))))

/-- The cost of the entry, in the input weight `X` and the driver bound `c X^K`. -/
noncomputable def vsQTopCost (hm : Membership) (X c K : ℕ) : ℕ :=
  10 ^ 15 * (X + 1) ^ 12 + 2 * reduceCost hm X X + 2 * c * (X + 1) ^ K + 2 * linTailCost (10 ^ 4 * (X + 1) ^ 6)

theorem vsQ_in_sizes (I : VecStabInst) :
    I.n ≤ (vsQTaskIn I).wt ∧ I.d ≤ (vsQTaskIn I).wt ∧ I.gs.length ≤ (vsQTaskIn I).wt := by
  have h1 : (encGroup I.gs).wt < (vsQTaskIn I).wt := wt_le_wt_list (by simp [vsQTaskIn])
  have h2 : (encVec I.v).wt < (vsQTaskIn I).wt := wt_le_wt_list (by simp [vsQTaskIn])
  have h3 : (Val.list ((1 :: I.gs).map encPerm)).wt < (encGroup I.gs).wt :=
    wt_le_wt_list (by simp [encGroup, encPerms])
  have h4 := length_lt_wt_list ((1 :: I.gs).map encPerm)
  have h5 : (encPerm (1 : Perm (Fin I.n))).wt < (Val.list ((1 :: I.gs).map encPerm)).wt :=
    wt_le_wt_list (by simp)
  have h6 := length_lt_wt_list ((List.finRange I.n).map fun i => Val.nat ((1 : Perm (Fin I.n)) i))
  have e6 : (encPerm (1 : Perm (Fin I.n))).wt =
    (Val.list ((List.finRange I.n).map fun i => Val.nat ((1 : Perm (Fin I.n)) i))).wt := rfl
  have h7 := length_lt_wt_list ((List.finRange I.d).map fun i => Val.nat (I.v i).val)
  have e7 : (encVec I.v).wt = (Val.list ((List.finRange I.d).map fun i => Val.nat (I.v i).val)).wt := rfl
  simp only [List.length_map, List.length_finRange, List.length_cons] at h4 h6 h7
  omega

set_option maxHeartbeats 16000000 in
/-- **The entry.** -/
theorem vsQTop_spec {P : Program} {f rng fold st idp rep tbm it tr red jm drv tl : ℕ} {hm : Membership}
    (hf : P.funs[f]? = some (vsQTopE rng fold idp rep tbm red drv tl))
    (hrng : P.HasAt rng (rangeFuns rng)) (hfold : P.HasAt fold (foldlFuns fold st))
    (hst : P.funs[st]? = some vsQFactStepE) (hidp : P.HasAt idp (vsWIdFuns idp))
    (hrep : P.HasAt rep (replicateFuns rep)) (htbm : P.HasAt tbm (mapFuns tbm it))
    (hit : P.funs[it]? = some (vsQTblItE tr)) (htr : P.HasAt tr (vsQTrFuns tr))
    (hred : P.HasAt red (reduceFuns red jm)) (hjm : P.prims[jm]? = some (membershipPrim hm))
    (htl : P.HasAt tl (linTailFuns tl)) {cD K : ℕ} (hK : 2 ≤ K)
    (hDrv : ∀ (s : VsQSt I) (hs : VsQStOK s), FunAll P drv (vsQStV I s) (VsQDrvOK cD K s hs)) :
    FunAll P f (vsQTaskIn I) (fun w cost => GensOf ((vecStab I).map (gens I.gs).subtype) w ∧
      cost ≤ vsQTopCost hm (vsQTaskIn I).wt cD K) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  obtain ⟨hnX, hdX, hgX⟩ := vsQ_in_sizes I
  set X := (vsQTaskIn I).wt with hX
  set EG := encGroup I.gs
  set ML := I.gs.attach.map fun g => ((I.φ ⟨g.1, Subgroup.subset_closure g.2⟩ : GL (Fin I.d) (ZMod I.p)) :
    Matrix (Fin I.d) (Fin I.d) (ZMod I.p))
  set MV := Val.list (ML.map encModMatrix)
  set EV := encVec I.v
  have eIn : vsQTaskIn I = .list [EG, .nat I.p, MV, EV] := by
    simp only [vsQTaskIn, MV, ML, List.map_map]; rfl
  rw [eIn] at hX ⊢
  set A := Val.list [EG, .nat I.p, MV, EV]
  have a0 : ∀ rest, Det P (A :: rest) (arg 0) EG (2 * A.wt + 0 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [EG, .nat I.p, MV, EV]) (rest := rest) (j := 0) rfl
  have a1 : ∀ rest, Det P (A :: rest) (arg 1) (.nat I.p) (2 * A.wt + 1 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [EG, .nat I.p, MV, EV]) (rest := rest) (j := 1) rfl
  have a2 : ∀ rest, Det P (A :: rest) (arg 2) MV (2 * A.wt + 2 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [EG, .nat I.p, MV, EV]) (rest := rest) (j := 2) rfl
  have a3 : ∀ rest, Det P (A :: rest) (arg 3) EV (2 * A.wt + 3 + 5) := fun rest =>
    Det.arg' (P := P) (vs := [EG, .nat I.p, MV, EV]) (rest := rest) (j := 3) rfl
  have eEV : EV = .list ((List.finRange I.d).map fun i => Val.nat (I.v i).val) := rfl
  -- 1. `d`
  have dd := Det.length (a3 [])
  rw [List.length_map, List.length_finRange] at dd
  -- 2. `E = n! - 2`
  have eEG : EG = .list [.nat I.n, .list ((1 :: I.gs).map encPerm)] := rfl
  have dn := Det.get' (a0 [.nat I.d]) (Det.nat 0) (show [Val.nat I.n, .list ((1 :: I.gs).map encPerm)][0]? =
    some (.nat I.n) from rfl)
  have hr : FunDet P rng (.nat I.n) (natList (List.range I.n))
      (loopModK * (I.n + 1) * ((Val.nat I.n).wt + I.n + (natList (List.range I.n)).wt + 1)) :=
    (range_spec hrng I.n).mono fun w c h => by obtain ⟨rfl, h2⟩ := h; exact ⟨rfl, h2⟩
  have dfold := Det.call (Det.mk3 (Det.nat (P := P) (env := [A, .nat I.d]) 0) (Det.call dn hr)
    (Det.nat (P := P) (env := [A, .nat I.d]) 1)) (vsQFact_spec hfold hst I.n)
  have dE := Det.arith (op := .sub) dfold (Det.nat (P := P) (env := [A, .nat I.d]) 2)
  have eE : GI.Machine.BinOp.eval .sub I.n.factorial 2 = vsQExp I := rfl
  rw [eE] at dE
  set E := vsQExp I
  -- 3. the identity and the zero vector
  set E2 := [A, Val.nat I.d, .nat E]
  have dId := Det.call (Det.var' (P := P) (env := E2) (i := 1) rfl) (vsWId_spec hidp (N := X) hdX)
  set E3 := [A, Val.nat I.d, .nat E, vsWVs (vsWId I.d)]
  have hz : FunDet P rep (.list [.nat I.d, .nat 0]) (natList (List.replicate I.d 0))
      (loopModK * (I.d + 1) * ((Val.list [.nat I.d, .nat 0]).wt + I.d +
        (natList (List.replicate I.d 0)).wt + 1)) :=
    (replicate_spec hrep I.d (.nat 0)).mono fun w c h => by
      obtain ⟨rfl, h2⟩ := h
      have e : Val.list (List.replicate I.d (Val.nat 0)) = natList (List.replicate I.d 0) := by
        simp [natList, List.map_replicate]
      rw [e] at h2 ⊢; exact ⟨rfl, h2⟩
  have dz := Det.call (Det.mk2 (Det.var' (P := P) (env := E3) (i := 1) rfl) (Det.nat (P := P) (env := E3) 0)) hz
  set Z := natList (List.replicate I.d 0)
  set E4 := [A, Val.nat I.d, .nat E, vsWVs (vsWId I.d), Z]
  -- 4. the table
  set NT := X ^ 2 + X + 3
  have hpX : I.p ≤ X := I.p_le.trans hnX
  have hEw : (Val.nat E).wt ≤ NT := by
    have h1 := vsQ_wt_fact I.n
    have h2 : (Val.nat E).wt ≤ (Val.nat I.n.factorial).wt := by
      rw [wt_nat, wt_nat]
      exact Nat.add_le_add_right (GI.Machine.len_mono (Nat.sub_le _ _)) _
    have h3 : I.n ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hnX 2
    simp only [NT]; omega
  have htbl := vsQ_map htbm (c := .list [.nat I.p, Z, .nat E, .nat I.d]) ML encModMatrix
    (vsQE I.p I.d E) encModMatrix_injective
    (fun M _ => vsQTblIt_spec hit htr (N := NT) (by simp only [NT]; omega) (by simp only [NT]; omega) hEw M)
  have dctx := Det.mk4 (a1 E4.tail) (Det.var' (P := P) (env := E4) (i := 4) rfl)
    (Det.var' (P := P) (env := E4) (i := 2) rfl) (Det.var' (P := P) (env := E4) (i := 1) rfl)
  have dtbl := Det.call (Det.mk2 dctx (a2 E4.tail)) htbl
  set TB := Val.list (ML.map (vsQE I.p I.d E))
  set E5 := [A, Val.nat I.d, .nat E, vsWVs (vsWId I.d), Z, TB]
  -- 5. the reduction
  have dred := Det.call (a0 E5.tail) (reduce_spec hm hred hjm I.gs)
  set HS := encGroup (keepList I.gs)
  set E6 := [A, Val.nat I.d, .nat E, vsWVs (vsWId I.d), Z, TB, HS]
  -- 6. the context `Γ` and the state
  have dG := Det.mk3 (a0 E6.tail) (Det.var' (P := P) (env := E6) (i := 5) rfl)
    (Det.mk4 (a1 E6.tail) (Det.var' (P := P) (env := E6) (i := 4) rfl)
      (Det.var' (P := P) (env := E6) (i := 2) rfl) (Det.var' (P := P) (env := E6) (i := 3) rfl))
  have eone : Val.list [.nat I.p, Z, .nat E, vsWVs (vsWId I.d)] = vsQE I.p I.d E 1 := by
    simp only [vsQE, Z, vsWVs, vsQL_one_tr I.prime.one_lt]
  have eTB : TB = vsQTable I := by
    simp only [TB, ML, vsQTable, List.map_map]; rfl
  have eG : Val.list [EG, TB, .list [.nat I.p, Z, .nat E, vsWVs (vsWId I.d)]] = vsQGam I := by
    rw [eone, eTB]; rfl
  rw [eG] at dG
  have dS := Det.snoc (Det.snoc (Det.mk4 dG (Det.var' (P := P) (env := E6) (i := 6) rfl)
    (Det.nil (P := P) (env := E6)) (Det.var' (P := P) (env := E6) (i := 3) rfl)) (a3 E6.tail)) (a3 E6.tail)
  have eS : Val.list ([vsQGam I, HS, Val.list [], vsWVs (vsWId I.d)] ++ [EV] ++ [EV]) = vsQStV I (vsQ0 I) := by
    simp only [vsQStV, vsQ0, HS, EV, encVec_eq, List.cons_append, List.nil_append]; rfl
  rw [eS] at dS
  -- the chain
  refine FunAll.intro hf (EvalAll.letE dd fun v1 c1 hv1 => ?_)
  obtain ⟨rfl, hc1⟩ := hv1
  refine EvalAll.letE dE fun v2 c2 hv2 => ?_
  obtain ⟨rfl, hc2⟩ := hv2
  refine EvalAll.letE dId fun v3 c3 hv3 => ?_
  obtain ⟨rfl, hc3⟩ := hv3
  refine EvalAll.letE dz fun v4 c4 hv4 => ?_
  obtain ⟨rfl, hc4⟩ := hv4
  refine EvalAll.letE dtbl fun v5 c5 hv5 => ?_
  obtain ⟨rfl, hc5⟩ := hv5
  refine EvalAll.letE dred fun v6 c6 hv6 => ?_
  obtain ⟨rfl, hc6⟩ := hv6
  -- 7. the driver
  have hs0 := vsQ0_ok (I := I)
  obtain ⟨CS, hCS, dS'⟩ : ∃ CS, CS = _ ∧ Det P E6 _ (vsQStV I (vsQ0 I)) CS := ⟨_, rfl, dS⟩
  set BD := vsQBd cD K (vsQ0 I).dim (vsQ0 I).Ab
  refine EvalAll.letE (Ra := fun w cc => (∃ a, w = vsQAnsV a ∧ VsQAnsOK hs0.prob a) ∧
      cc ≤ CS + 2 * BD + 1 ∧ w.wt ≤ BD)
    (EvalAll.call_funAll dS' fun v ca hv => ?_) fun v7 c7 hv7 => ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine (hDrv (vsQ0 I) hs0).wt_lt.mono fun w cc hw => ?_
    obtain ⟨⟨a, rfl, ha, hc⟩, hwc⟩ := hw
    exact ⟨⟨a, rfl, ha⟩, by omega, by omega⟩
  obtain ⟨⟨a, rfl, ha⟩, hc7, hw7⟩ := hv7
  -- the answer is not empty
  rcases a with _ | ⟨h0, ks⟩
  · exact absurd ((Set.eq_empty_iff_forall_notMem.1 ha) 1 vsQ0_sol) id
  obtain ⟨-, hks, hksl⟩ := ha
  set E7 := [A, Val.nat I.d, .nat E, vsWVs (vsWId I.d), Z, TB, HS, vsQAnsV (some (h0, ks))]
  have d72 := Det.get' (Det.var' (P := P) (env := E7) (i := 7) rfl) (Det.nat 2)
    (show [Val.nat 1, encPerm h0, encGroup ks][2]? = some (encGroup ks) from rfl)
  have d72' : Det P E7 _ (.list [.nat I.n, .list ((1 :: ks).map encPerm)]) _ := d72
  have d721 := Det.get' d72' (Det.nat 1) (show [Val.nat I.n, .list ((1 :: ks).map encPerm)][1]? =
    some (.list ((1 :: ks).map encPerm)) from rfl)
  have dout := Det.call d721 (linTail_spec htl ((1 :: ks).map encPerm))
  simp only [List.map_cons, List.drop_succ_cons, List.drop_zero] at dout
  refine Det.post dout fun c hc => ⟨⟨ks, rfl, hksl, ?_⟩, ?_⟩
  · rw [hks]; exact vsQ0_stab
  · -- the cost
    have hXA : A.wt = X := hX.symm
    have q1 : 1 ≤ (X + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    have pw : ∀ i j, i ≤ j → (X + 1) ^ i ≤ (X + 1) ^ j := fun i j h => Nat.pow_le_pow_right (by omega) h
    have hX1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    -- the small values
    have wn := wt_nat_le I.n; have wd := wt_nat_le I.d; have wp := wt_nat_le I.p
    have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2; have := wt_nat_le 3
    have wr : (natList (List.range I.n)).wt ≤ 5 * (X + 1) ^ 2 :=
      wt_natList_le_sq (fun y hy => by simp at hy; omega) (by simp; omega)
    have wfa := vsQ_wt_fact I.n
    have hn2 : I.n ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hn4 : (I.n + 1) ^ 4 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have wId : (vsWVs (vsWId I.d)).wt ≤ 11 * (X + 1) ^ 3 + 4 :=
      wt_vsWVs_le (fun u hu => ⟨fun y hy => ((vsWId_fit I.prime.one_lt I.d u hu).1 y hy).le.trans
        (by omega), by rw [(vsWId_fit I.prime.one_lt I.d u hu).2]; exact hdX⟩) (by simp [vsWId]; omega)
    have wZ : Z.wt ≤ 5 * (X + 1) ^ 2 := wt_natList_le_sq (fun y hy => by simp at hy; omega) (by simp; omega)
    have hX2 : 2 ≤ X := by have := I.prime.two_le; omega
    have hNT : NT + 1 ≤ 2 * (X + 1) ^ 2 := by simp only [NT]; nlinarith
    have hNT3 : (NT + 1) ^ 3 ≤ 8 * (X + 1) ^ 6 := by
      calc (NT + 1) ^ 3 ≤ (2 * (X + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left hNT 3
        _ = 8 * (X + 1) ^ 6 := by ring
    have hNT5 : (NT + 1) ^ 5 ≤ 32 * (X + 1) ^ 10 := by
      calc (NT + 1) ^ 5 ≤ (2 * (X + 1) ^ 2) ^ 5 := Nat.pow_le_pow_left hNT 5
        _ = 32 * (X + 1) ^ 10 := by ring
    have hML : ML.length = I.gs.length := by simp [ML]
    -- the table and the context
    have wE1 : ∀ M : Matrix (Fin I.d) (Fin I.d) (ZMod I.p), (vsQE I.p I.d E M).wt ≤ 100 * (X + 1) ^ 6 := by
      intro M
      have wMt : (Val.list ((vsQL Mᵀ).map natList)).wt ≤ 11 * (X + 1) ^ 3 + 4 :=
        wt_vsFSq_le (by omega) hdX (vsQL_sq Mᵀ)
      have l4 := wt_list4_le (.nat I.p) Z (.nat E) (.list ((vsQL Mᵀ).map natList))
      have eE : (vsQE I.p I.d E M).wt = (Val.list [.nat I.p, Z, .nat E,
        .list ((vsQL Mᵀ).map natList)]).wt := rfl
      have := pw 3 6 (by omega); have := pw 2 6 (by omega)
      omega
    have wTB : TB.wt ≤ 300 * (X + 1) ^ 7 := by
      have h1 := vs_wt_list_le_of (ML.map (vsQE I.p I.d E)) (c := 100 * (X + 1) ^ 6) (by
        intro v hv
        obtain ⟨M, -, rfl⟩ := List.mem_map.1 hv
        exact wE1 M)
      rw [List.length_map, hML] at h1
      have eTB' : TB.wt = (Val.list (ML.map (vsQE I.p I.d E))).wt := rfl
      have h2 : I.gs.length * (2 * (100 * (X + 1) ^ 6) + 1) ≤ (X + 1) * (201 * (X + 1) ^ 6) :=
        Nat.mul_le_mul (by omega) (by have := pw 0 6 (by omega); simp at this; omega)
      have e : (X + 1) * (201 * (X + 1) ^ 6) = 201 * (X + 1) ^ 7 := by ring
      have := pw 0 7 (by omega); simp at this
      omega
    have wΓ : (vsQGam I).wt ≤ 2000 * (X + 1) ^ 7 := by
      have l3 := wt_list3_le EG TB (vsQE I.p I.d E 1)
      have e : (vsQGam I).wt = (Val.list [EG, TB, vsQE I.p I.d E 1]).wt := by rw [eTB]; rfl
      have hEG : EG.wt < A.wt := wt_le_wt_list (by simp [A])
      have := wE1 1; have := pw 6 7 (by omega); have : X + 1 ≤ (X + 1) ^ 7 := Nat.le_self_pow (by norm_num) _
      omega
    have wHS : HS.wt ≤ 320 * (X + 1) ^ 6 :=
      (wt_encGroup_le_sq (length_keepList_le _)).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6))
    have wks : (encGroup ks).wt ≤ 320 * (X + 1) ^ 6 :=
      (wt_encGroup_le_sq hksl).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 6))
    have wh0 : (encPerm h0).wt ≤ 4 * (X + 1) ^ 2 :=
      (wt_encPerm_le h0).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
    have hEGA : EG.wt < A.wt := wt_le_wt_list (by simp [A])
    have hMVA : MV.wt < A.wt := wt_le_wt_list (by simp [A])
    have hEVA : EV.wt < A.wt := wt_le_wt_list (by simp [A])
    have mk : mapK = 1000 := rfl
    have mk2 : loopModK = 1000 := rfl
    have t1 : c1 ≤ 10 * X + 20 := by omega
    have t2 : c2 ≤ 10 ^ 8 * (X + 1) ^ 4 := by
      have l3 := wt_list3_le (.nat 0) (natList (List.range I.n)) (.nat 1)
      have h1 : loopModK * (I.n + 1) * ((Val.nat I.n).wt + I.n + (natList (List.range I.n)).wt + 1) ≤
          1000 * (X + 1) * (20 * (X + 1) ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
      have e1 : 1000 * (X + 1) * (20 * (X + 1) ^ 2) = 2 * 10 ^ 4 * (X + 1) ^ 3 := by ring
      have := pw 2 4 (by omega); have := pw 3 4 (by omega)
      have hE2 : (Val.nat (GI.Machine.BinOp.eval .sub I.n.factorial 2)).wt ≤ NT := hEw
      clear_value EG MV EV A E Z TB HS NT
      omega
    have t3 : c3 ≤ 3 * 10 ^ 8 * (X + 1) ^ 4 := by
      have := pw 3 4 (by omega); have := pw 2 4 (by omega)
      omega
    have t4 : c4 ≤ 10 ^ 5 * (X + 1) ^ 3 := by
      have l2 := wt_list2_le (.nat I.d) (.nat 0)
      have h1 : loopModK * (I.d + 1) * ((Val.list [Val.nat I.d, Val.nat 0]).wt + I.d + Z.wt + 1) ≤
          1000 * (X + 1) * (20 * (X + 1) ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by omega)
      have e1 : 1000 * (X + 1) * (20 * (X + 1) ^ 2) = 2 * 10 ^ 4 * (X + 1) ^ 3 := by ring
      have := pw 2 3 (by omega)
      omega
    have t5 : c5 ≤ 10 ^ 10 * (X + 1) ^ 12 := by
      have l4 := wt_list4_le (.nat I.p) Z (.nat E) (.nat I.d)
      have l2 := wt_list2_le (.list [.nat I.p, Z, .nat E, .nat I.d]) MV
      have eMV : (Val.list (List.map encModMatrix ML)).wt = MV.wt := rfl
      have eMV2 : (Val.list [Val.list [Val.nat I.p, Z, Val.nat E, Val.nat I.d], Val.list (List.map encModMatrix ML)]).wt =
        (Val.list [Val.list [Val.nat I.p, Z, Val.nat E, Val.nat I.d], MV]).wt := rfl
      have h1 : ML.length * (10 ^ 7 * (NT + 1) ^ 5) ≤ (X + 1) * (10 ^ 7 * (32 * (X + 1) ^ 10)) :=
        Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ hNT5)
      have e1 : (X + 1) * (10 ^ 7 * (32 * (X + 1) ^ 10)) = 32 * 10 ^ 7 * (X + 1) ^ 11 := by ring
      have h2 : mapK * (ML.length + 1) * ((Val.list [Val.list [Val.nat I.p, Z, Val.nat E, Val.nat I.d],
          Val.list (List.map encModMatrix ML)]).wt + TB.wt + 1) ≤ 1000 * (X + 1) * (10 ^ 4 * (X + 1) ^ 7) :=
        Nat.mul_le_mul (Nat.mul_le_mul (le_refl _) (by omega)) (by
          have q27 := pw 2 7 (by omega); have q17 : X + 1 ≤ (X + 1) ^ 7 := Nat.le_self_pow (by norm_num) _
          clear_value EG MV EV A E Z TB HS NT
          clear * - l4 l2 eMV eMV2 wp wd wZ hEw hNT hpX hdX hMVA hXA wTB q27 q17
          omega)
      have e2 : 1000 * (X + 1) * (10 ^ 4 * (X + 1) ^ 7) = 10 ^ 7 * (X + 1) ^ 8 := by ring
      have := pw 11 12 (by omega); have := pw 8 12 (by omega); have := pw 7 12 (by omega)
      have := pw 2 12 (by omega)
      have : X + 1 ≤ (X + 1) ^ 12 := Nat.le_self_pow (by norm_num) _
      clear_value EG MV EV A E Z TB HS NT
      omega
    have t6 : c6 ≤ 2 * X + reduceCost hm X X + 320 * (X + 1) ^ 6 + 6 := by
      have h1 := reduceCost_mono hm I.n (show I.gs.length ≤ X from hgX)
      have h2 := vsQ_reduceCost_mono_n hm (show I.n ≤ X from hnX) X
      omega
    have tCS : CS ≤ 10 ^ 6 * (X + 1) ^ 7 := by
      rw [hCS]
      have l4 := wt_list4_le (.nat I.p) Z (.nat E) (vsWVs (vsWId I.d))
      have l4' := wt_list4_le (vsQGam I) HS (Val.list []) (vsWVs (vsWId I.d))
      have l5 := wt_list_le ([vsQGam I, HS, Val.list [], vsWVs (vsWId I.d)] ++ [EV])
      have l6 := wt_list_le ([vsQGam I, HS, Val.list [], vsWVs (vsWId I.d)] ++ [EV] ++ [EV])
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
        List.length_append, List.length_cons, List.length_nil] at l5 l6
      have w0 : (Val.list []).wt ≤ 10 := (wt_list_le []).trans (by simp)
      have eS' : (vsQStV I (vsQ0 I)).wt = (Val.list ([vsQGam I, HS, Val.list [], vsWVs (vsWId I.d)] ++ [EV] ++ [EV])).wt := by
        rw [← eS]
      have q67 := pw 6 7 (by omega); have q37 := pw 3 7 (by omega); have q27 := pw 2 7 (by omega)
      have : X + 1 ≤ (X + 1) ^ 7 := Nat.le_self_pow (by norm_num) _
      clear_value EG MV EV A E Z TB HS NT
      omega
    have hBD : BD ≤ cD * (X + 1) ^ K := by
      have hD1 : 1 ≤ max (vsQ0 I).dim 1 := le_max_right _ _
      have e1 : BD = vsQBd cD K (max (vsQ0 I).dim 1) (vsQ0 I).Ab := by
        simp only [BD, vsQBd, max_eq_left hD1]
      rw [e1]
      refine (vsQBd_le_Fn _ hD1 hK).trans ?_
      unfold vsQFn
      refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ K)
      have := vsQD_le hs0
      have := vsQD_eq hs0
      omega
    have hEk : (Val.list (encPerm (1 : Perm (Fin I.n)) :: List.map encPerm ks)).wt < (encGroup ks).wt :=
      wt_le_wt_list (show Val.list (encPerm (1 : Perm (Fin I.n)) :: List.map encPerm ks) ∈
        [Val.nat I.n, Val.list ((1 :: ks).map encPerm)] by simp)
    have hks1 : (Val.list (List.map encPerm ks)).wt ≤ (Val.list (encPerm (1 : Perm (Fin I.n)) :: List.map encPerm ks)).wt := by
      rw [wt_list_eq, wt_list_eq]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have h1 := GI.Machine.len_mono (show (List.map encPerm ks).length ≤ (List.map encPerm ks).length + 1 by omega)
      have h2 := GI.Machine.len_mono (show ((List.map encPerm ks).map Val.size).sum ≤
        (encPerm (1 : Perm (Fin I.n))).size + ((List.map encPerm ks).map Val.size).sum by omega)
      omega
    have wans : (Val.list [Val.nat 1, encPerm h0, encGroup ks]).wt ≤ 10 ^ 3 * (X + 1) ^ 6 := by
      have l3 := wt_list3_le (.nat 1) (encPerm h0) (encGroup ks)
      have := pw 2 6 (by omega); have := pw 0 6 (by omega); simp at this
      omega
    have hW6 : (Val.list (encPerm (1 : Perm (Fin I.n)) :: List.map encPerm ks)).wt ≤ 10 ^ 4 * (X + 1) ^ 6 := by
      omega
    have hLT : linTailCost (Val.list (encPerm (1 : Perm (Fin I.n)) :: List.map encPerm ks)).wt ≤
        linTailCost (10 ^ 4 * (X + 1) ^ 6) := by
      unfold linTailCost
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    unfold vsQTopCost
    have := pw 4 12 (by omega); have := pw 3 12 (by omega); have := pw 7 12 (by omega)
    have := pw 6 12 (by omega)
    have : X + 1 ≤ (X + 1) ^ 12 := Nat.le_self_pow (by norm_num) _
    have hBD2 : 2 * BD ≤ 2 * cD * (X + 1) ^ K := by rw [mul_assoc]; omega
    clear_value EG MV EV A E Z TB HS NT BD
    omega

end GI.Impl