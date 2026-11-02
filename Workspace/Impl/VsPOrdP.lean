import Workspace.Impl.VsPOrd

/-!
# An element of prime order modulo `L`, as a program

On `[ctx, x]` with `x ∈ G`, `Λ(x) ∉ L` (and `Λ(1) ∈ L`), the program `vsPOrdFuns`

1. walks `y := y^q` for `q = 2, …, n` until `Λ(y^q) ∈ L` (`vsPWalk`; it stops since `x^(n!) = 1`);
2. finds the least `j ≥ 1` with `Λ(y^j) ∈ L` (`vsPJ`), and the least prime `r ∣ j` (`vsPR`);
3. returns `[x₂, r]` with `x₂ = y^(j/r)`.

Then `Λ(x₂) ∉ L`, `Λ(x₂^r) ∈ L`, `r` is a prime with `r ≤ n`, and `x₂` is a power of `x`
(`vsPOrd_out`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-! ### The two tests -/

/-- On `[[ctx, y], t]`: is `Λ(y^(t+1)) ∈ L`? -/
def vsPPredBE (pow inl : ℕ) : Expr :=
  .call inl (mk2 (.get (arg 0) (.nat 0))
    (.call pow (mk4 (.nat 0) (.get (arg 0) (.nat 1)) (arg 1) (.get (arg 0) (.nat 1)))))

/-- On `[j, t]`: does `t + 2` divide `j`? -/
def vsPPredCE : Expr :=
  .arith .eq (.arith .mod (arg 0) (.arith .add (arg 1) (.nat 2))) (.nat 0)

/-- The test of the search for `j`, on values. -/
def vsPQB {n : ℕ} (ib : Perm (Fin n) → Bool) (y : Perm (Fin n)) : Val → Bool
  | .nat t => ib (y ^ (t + 1))
  | .list _ => false

/-- The test of the search for `r`, on values. -/
def vsPQC (j : ℕ) : Val → Bool
  | .nat t => decide (j % (t + 2) = 0)
  | .list _ => false

set_option maxHeartbeats 1000000 in
theorem vsPPredB_spec {P : Program} {f pow inl phi Cφ N W : ℕ}
    (hf : P.funs[f]? = some (vsPPredBE pow inl)) (hpow : P.HasAt pow (vsPPowFuns pow))
    (hinl : P.HasAt inl (vsPInLPFuns inl phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {y : Perm (Fin I.n)} (hy : y ∈ gens I.gs) {t : ℕ}
    (ht : t ≤ N) :
    FunDet P f (.list [.list [vsPCtx I ws' cs rows hs, encPerm y], .nat t])
      (boolVal (vsPQB (vsPInLB I ws' cs rows) y (.nat t))) (vsPWStepCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set vs := [Val.list [C, encPerm y], .nat t]
  have a0 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) rfl
  have c0 := Det.get' a0 (Det.nat 0) (show [C, encPerm y][0]? = some C from rfl)
  have c1 := Det.get' a0 (Det.nat 1) (show [C, encPerm y][1]? = some (encPerm y) from rfl)
  have dz := Det.call (Det.mk4 (Det.nat 0) c1 a1 c1) (vsPPow_spec hpow y y t)
  have ez : y ^ t * y = y ^ (t + 1) := (pow_succ y t).symm
  rw [ez] at dz
  have dI := Det.call (Det.mk2 c0 dz) (vsPInLP_spec hinl hphi H (pow_mem hy (t + 1)))
  refine FunDet.intro hf (dI.mono ?_)
  have hn := H.n
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hn3 : (I.n + 1) ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hpc := vsPPowCost_le (n := I.n) (e := t) (k := N) (by have := vsP_bits_le t; omega)
  have hpc' : 10 ^ 6 * (N + 1) ^ 2 * (I.n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 5 := by
    calc 10 ^ 6 * (N + 1) ^ 2 * (I.n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 2 * (N + 1) ^ 3 :=
          Nat.mul_le_mul_left _ hn3
      _ = 10 ^ 6 * (N + 1) ^ 5 := by ring
  have wC : C.wt ≤ W := H.cw
  have wy := wt_encPerm_le y
  have wz := wt_encPerm_le (y ^ (t + 1))
  have wt' := wt_nat_le t
  have w1 := wt_list2_le C (encPerm y)
  have w2 := wt_list2_le (.list [C, encPerm y]) (.nat t)
  have w4 := wt_list4_le (.nat 0) (encPerm y) (.nat t) (encPerm y)
  have w5 := wt_list2_le C (encPerm (y ^ (t + 1)))
  have wb := wt_boolVal_le (vsPInLB I ws' cs rows (y ^ (t + 1)))
  have ev : (Val.list vs).wt = (Val.list [Val.list [C, encPerm y], .nat t]).wt := rfl
  have eb : boolVal (vsPQB (vsPInLB I ws' cs rows) y (.nat t)) =
      boolVal (vsPInLB I ws' cs rows (y ^ (t + 1))) := rfl
  have w0 : (Val.nat 0).wt = 2 := rfl
  have q1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  unfold vsPWStepCost
  omega

theorem vsPPredC_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some vsPPredCE) (j t : ℕ) :
    FunDet P f (.list [.nat j, .nat t]) (boolVal (vsPQC j (.nat t))) (100 * (j + t + 10)) := by
  have a0 := Det.arg' (P := P) (vs := [.nat j, .nat t]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [.nat j, .nat t]) (rest := []) (j := 1) rfl
  have d1 := Det.arith' (op := .add) a1 (Det.nat 2) rfl
  have d2 := Det.arith' (op := .mod) a0 d1 rfl
  have d3 := Det.arith' (op := .eq) d2 (Det.nat 0) rfl
  have ev : Val.nat (GI.Machine.BinOp.eval .eq (GI.Machine.BinOp.eval .mod j
      (GI.Machine.BinOp.eval .add t 2)) 0) = boolVal (vsPQC j (.nat t)) := by
    simp only [GI.Machine.BinOp.eval, vsPQC, boolVal]
    split_ifs with h <;> simp [h]
  rw [ev] at d3
  refine FunDet.intro hf (d3.mono ?_)
  have w := wt_list2_le (.nat j) (.nat t)
  have wj := wt_nat_le j
  have wt' := wt_nat_le t
  have hb : GI.Machine.BinOp.eval .eq (GI.Machine.BinOp.eval .mod j
      (GI.Machine.BinOp.eval .add t 2)) 0 ≤ 1 := by
    simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega
  have hm : GI.Machine.BinOp.eval .mod j (GI.Machine.BinOp.eval .add t 2) ≤ j := by
    simp only [GI.Machine.BinOp.eval]; exact Nat.mod_le _ _
  have ha : GI.Machine.BinOp.eval .add t 2 = t + 2 := rfl
  omega

/-! ### The program -/

/-- On `[ctx, x]`: `[x₂, r]`. -/
def vsPOrdE (walk fb fc rng pow : ℕ) : Expr :=
  .letE (.call walk (mk3 (arg 0) (.arith .sub (vsPC 6) (.nat 1)) (mk3 (.nat 0) (arg 1) (.nat 0))))
  (.letE (.get (.var 1) (.nat 1))
  (.letE (.call fb (mk2 (mk2 (arg 0) (.var 2)) (.call rng (vsPC 6))))
  (.letE (.arith .add (.var 3) (.nat 1))
  (.letE (.call fc (mk2 (.var 4) (.call rng (.var 4))))
  (.letE (.arith .add (.var 5) (.nat 2))
    (mk2 (.call pow (mk4 (.nat 0) (.var 2) (.arith .sub (.arith .div (.var 4) (.var 6)) (.nat 1))
      (.var 2))) (.var 6)))))))

/-- The program at base `b` (81 functions; `phi` is the matrix program). -/
def vsPOrdFuns (b phi : ℕ) : List Expr :=
  [vsPOrdE (b + 1) (b + 5) (b + 9) (b + 13) (b + 16)] ++ iterFuns (b + 1) (b + 4) ++
    [vsPWStepE (b + 16) (b + 22)] ++ findFuns (b + 5) (b + 8) ++ [vsPPredBE (b + 16) (b + 22)] ++
    findFuns (b + 9) (b + 12) ++ [vsPPredCE] ++ rangeFuns (b + 13) ++ vsPPowFuns (b + 16) ++
    vsPInLPFuns (b + 22) phi

theorem vsPOrdFuns_length (b phi : ℕ) : (vsPOrdFuns b phi).length = 81 := rfl

/-- The walked element. -/
noncomputable def vsPOrdY (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (x : Perm (Fin I.n)) : Perm (Fin I.n) :=
  (vsPWalk (vsPInLB I ws' cs rows) (I.n - 1) x).2.1

/-- The least `j`. -/
noncomputable def vsPOrdJ (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (x : Perm (Fin I.n)) : ℕ :=
  vsPJ (vsPInLB I ws' cs rows) I.n (vsPOrdY I ws' cs rows x)

/-- The prime `r`. -/
noncomputable def vsPOrdR (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (x : Perm (Fin I.n)) : ℕ :=
  vsPR (vsPOrdJ I ws' cs rows x)

/-- The element `x₂`. -/
noncomputable def vsPOrdX (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (x : Perm (Fin I.n)) : Perm (Fin I.n) :=
  vsPOrdY I ws' cs rows x ^ (vsPOrdJ I ws' cs rows x / vsPOrdR I ws' cs rows x)

/-- **What the program returns.** -/
theorem vsPOrd_out {ws' cs : List (List ℕ)} {rows : List VsRow} {x : Perm (Fin I.n)}
    (hx : vsPInLB I ws' cs rows x = false) (h1 : vsPInLB I ws' cs rows 1 = true) (hn : 2 ≤ I.n) :
    vsPOrdX I ws' cs rows x ∈ Subgroup.zpowers x ∧ (vsPOrdR I ws' cs rows x).Prime ∧
      vsPOrdR I ws' cs rows x ≤ I.n ∧ vsPInLB I ws' cs rows (vsPOrdX I ws' cs rows x) = false ∧
      vsPInLB I ws' cs rows (vsPOrdX I ws' cs rows x ^ vsPOrdR I ws' cs rows x) = true ∧
      2 ≤ vsPOrdJ I ws' cs rows x ∧ vsPOrdJ I ws' cs rows x ≤ I.n ∧
      1 ≤ vsPOrdJ I ws' cs rows x / vsPOrdR I ws' cs rows x := by
  set ib := vsPInLB I ws' cs rows
  have hf := vsPWalk_found ib hx h1 hn
  obtain ⟨-, hz, hib, hq, -, h1'⟩ := vsPWalk_inv ib hx (I.n - 1)
  obtain ⟨hq1, hq2⟩ := h1' hf
  obtain ⟨hJ2, hJm, hpr, hrj, -, hq1', hfx, htr⟩ := vsPOrd_math ib hib hq1 hq2 (m := I.n) (by omega)
  exact ⟨Subgroup.pow_mem _ hz _, hpr, hrj.trans hJm, hfx, htr, hJ2, hJm, hq1'⟩

/-- The cost of the program. -/
def vsPOrdCost (Cφ N W : ℕ) : ℕ := 3 * vsPWalkCost Cφ N W + 10 ^ 9 * (N + 1) ^ 5

theorem vsP_range_det {P : Program} {b : ℕ} (h : P.HasAt b (rangeFuns b)) (m : ℕ) :
    FunAll P b (.nat m) (fun w c => w = natList (List.range m) ∧
      c ≤ 1000 * (m + 1) * (m + 2 + m + 5 * (m + 1) ^ 2 + 1)) := by
  refine (range_spec h m).mono fun w c hw => ⟨hw.1, hw.2.trans ?_⟩
  rw [hw.1]
  have w1 := wt_nat_le m
  have w2 : (natList (List.range m)).wt ≤ 5 * (m + 1) ^ 2 :=
    wt_natList_le_sq (fun y hy => by simp at hy; omega) (by simp)
  simp only [loopModK]
  exact Nat.mul_le_mul_left _ (by omega)

theorem vsP_rng_le {m N : ℕ} (h : m ≤ N) :
    1000 * (m + 1) * (m + 2 + m + 5 * (m + 1) ^ 2 + 1) ≤ 10000 * (N + 1) ^ 3 := by
  have h2 : (m + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  calc 1000 * (m + 1) * (m + 2 + m + 5 * (m + 1) ^ 2 + 1)
      ≤ 1000 * (N + 1) * (10 * (N + 1) ^ 2) := Nat.mul_le_mul (by omega) (by omega)
    _ = 10000 * (N + 1) ^ 3 := by ring

theorem vsP_loop_le {m N W Z : ℕ} (h : m ≤ N) (hZ : Z ≤ 4 * W + 100 * (N + 1) ^ 2) :
    1000 * (m + 1) * Z ≤ 4000 * ((N + 1) * W) + 10 ^ 5 * (N + 1) ^ 3 := by
  calc 1000 * (m + 1) * Z ≤ 1000 * (N + 1) * (4 * W + 100 * (N + 1) ^ 2) :=
        Nat.mul_le_mul (by omega) hZ
    _ = 4000 * ((N + 1) * W) + 10 ^ 5 * (N + 1) ^ 3 := by ring

set_option maxHeartbeats 4000000 in
/-- **The element of prime order modulo `L`, as a program.** -/
theorem vsPOrd_spec {P : Program} {b phi Cφ N W : ℕ} (h : P.HasAt b (vsPOrdFuns b phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) (hn : 2 ≤ I.n) (hnN : I.n + 2 ≤ N)
    {x : Perm (Fin I.n)} (hx : x ∈ gens I.gs) (hxb : vsPInLB I ws' cs rows x = false)
    (h1 : vsPInLB I ws' cs rows 1 = true) :
    FunDet P b (.list [vsPCtx I ws' cs rows hs, encPerm x])
      (.list [encPerm (vsPOrdX I ws' cs rows x), .nat (vsPOrdR I ws' cs rows x)])
      (vsPOrdCost Cφ N W) := by
  have h0 : P.funs[b]? = some (vsPOrdE (b + 1) (b + 5) (b + 9) (b + 13) (b + 16)) :=
    h.get (j := 0) (by simp [vsPOrdFuns])
  have hit : P.HasAt (b + 1) (iterFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hst : P.funs[b + 4]? = some (vsPWStepE (b + 16) (b + 22)) :=
    h.get (j := 4) (by rw [vsPOrdFuns_length]; omega)
  have hfb : P.HasAt (b + 5) (findFuns (b + 5) (b + 8)) := h.block 5 rfl
  have hpb : P.funs[b + 8]? = some (vsPPredBE (b + 16) (b + 22)) :=
    h.get (j := 8) (by rw [vsPOrdFuns_length]; omega)
  have hfc : P.HasAt (b + 9) (findFuns (b + 9) (b + 12)) := h.block 9 rfl
  have hpc : P.funs[b + 12]? = some vsPPredCE := h.get (j := 12) (by rw [vsPOrdFuns_length]; omega)
  have hrg : P.HasAt (b + 13) (rangeFuns (b + 13)) := h.block 13 rfl
  have hpw : P.HasAt (b + 16) (vsPPowFuns (b + 16)) := h.block 16 rfl
  have hin : P.HasAt (b + 22) (vsPInLPFuns (b + 22) phi) := h.block 22 rfl
  set ib := vsPInLB I ws' cs rows
  obtain ⟨hzX, hpr, hrn, hfx, htr, hJ2, hJn, hq1⟩ := vsPOrd_out hxb h1 hn
  set cv := [vsQGam I, vsWFrVal I.p I.d ws' cs, .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ (cs.length * cs.length)), encGroup hs, .nat I.n] with hcv
  set C := vsPCtx I ws' cs rows hs
  have eC : C = .list cv := rfl
  set a := vsPWalk ib (I.n - 1) x
  set y := a.2.1
  have hy : y ∈ gens I.gs := Subgroup.zpowers_le.2 hx (vsPWalk_inv ib hxb (I.n - 1)).2.1
  set j := vsPOrdJ I ws' cs rows x
  set r := vsPOrdR I ws' cs rows x
  have ej : j = vsPJ ib I.n y := rfl
  have er : r = vsPR j := rfl
  -- step 1: the walk
  set A := Val.list [C, encPerm x]
  have a0 := Det.arg' (P := P) (vs := [C, encPerm x]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [C, encPerm x]) (rest := []) (j := 1) rfl
  have a0' : Det P [A] (arg 0) (.list cv) _ := a0
  have c6 := Det.get' a0' (Det.nat 6) (show cv[6]? = some (.nat I.n) from rfl)
  have dk := Det.arith' (op := .sub) c6 (Det.nat 1) rfl
  have dacc := Det.mk3 (Det.nat (P := P) (env := [A]) 0) a1 (Det.nat 0)
  have dW := Det.call (Det.mk3 a0 dk dacc)
    (vsPWalk_spec hit hst hpw hin hphi H (k := I.n - 1) (by omega)
      hx hxb)
  -- step 2: y
  set e1 := [A, vsPAccV a]
  have dy := Det.get' (Det.var' (P := P) (env := e1) (i := 1) rfl) (Det.nat 1)
    (show [Val.nat a.1, encPerm y, .nat a.2.2][1]? = some (encPerm y) from rfl)
  -- step 3: the search for j
  set e2 := e1 ++ [encPerm y]
  have b0 := Det.arg' (P := P) (vs := [C, encPerm x]) (rest := [vsPAccV a, encPerm y]) (j := 0) rfl
  have b0' : Det P e2 (arg 0) (.list cv) _ := b0
  have b6 := Det.get' b0' (Det.nat 6) (show cv[6]? = some (.nat I.n) from rfl)
  have dR := Det.call b6 ((vsP_range_det hrg I.n).mono fun w c hw => ⟨hw.1, hw.2⟩)
  have eR : natList (List.range I.n) = .list ((List.range I.n).map Val.nat) := rfl
  rw [eR] at dR
  have vy := Det.var' (P := P) (env := e2) (i := 2) rfl
  have hpB : ∀ v ∈ (List.range I.n).map Val.nat, FunDet P (b + 8) (.list [.list [C, encPerm y], v])
      (boolVal (vsPQB ib y v)) (vsPWStepCost Cφ N W) := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    exact vsPPredB_spec hpb hpw hin hphi H hy (by simp at ht; omega)
  have dFB := Det.call (Det.mk2 (Det.mk2 b0 vy) dR)
    ((find_spec hfb hpB).mono fun w c hw => ⟨hw.1, hw.2⟩)
  have eFB : ((List.range I.n).map Val.nat).findIdx (vsPQB ib y) =
      (List.range I.n).findIdx (fun t => ib (y ^ (t + 1))) := by
    rw [List.findIdx_map]; rfl
  rw [eFB] at dFB
  set tB := (List.range I.n).findIdx (fun t => ib (y ^ (t + 1)))
  have ejt : j = tB + 1 := rfl
  -- step 4: j
  set e3 := e2 ++ [.nat tB]
  have dj := Det.arith' (op := .add) (Det.var' (P := P) (env := e3) (i := 3) rfl) (Det.nat 1)
    (show GI.Machine.BinOp.eval .add tB 1 = j by rw [ejt]; rfl)
  -- step 5: the search for r
  set e4 := e3 ++ [.nat j]
  have vj := Det.var' (P := P) (env := e4) (i := 4) rfl
  have dRj := Det.call vj ((vsP_range_det hrg j).mono fun w c hw => ⟨hw.1, hw.2⟩)
  have eRj : natList (List.range j) = .list ((List.range j).map Val.nat) := rfl
  rw [eRj] at dRj
  have hpC : ∀ v ∈ (List.range j).map Val.nat, FunDet P (b + 12) (.list [.nat j, v])
      (boolVal (vsPQC j v)) (100 * (2 * N + 10)) := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hv
    simp at ht
    exact (vsPPredC_spec hpc j t).mono (by omega)
  have dFC := Det.call (Det.mk2 vj dRj) ((find_spec hfc hpC).mono fun w c hw => ⟨hw.1, hw.2⟩)
  have eFC : ((List.range j).map Val.nat).findIdx (vsPQC j) =
      (List.range j).findIdx (fun t => decide (j % (t + 2) = 0)) := by
    rw [List.findIdx_map]; rfl
  rw [eFC] at dFC
  set tC := (List.range j).findIdx (fun t => decide (j % (t + 2) = 0))
  have ert : r = tC + 2 := rfl
  -- step 6: r
  set e5 := e4 ++ [.nat tC]
  have dr := Det.arith' (op := .add) (Det.var' (P := P) (env := e5) (i := 5) rfl) (Det.nat 2)
    (show GI.Machine.BinOp.eval .add tC 2 = r by rw [ert]; rfl)
  -- step 7: the power
  set e6 := e5 ++ [.nat r]
  have v2 := Det.var' (P := P) (env := e6) (i := 2) rfl
  have v4 := Det.var' (P := P) (env := e6) (i := 4) rfl
  have v6 := Det.var' (P := P) (env := e6) (i := 6) rfl
  have dq := Det.arith' (op := .sub) (Det.arith' (op := .div) v4 v6 rfl) (Det.nat 1) rfl
  have dP := Det.call (Det.mk4 (Det.nat 0) v2 dq v2) (vsPPow_spec hpw y y (j / r - 1))
  have eP : y ^ (j / r - 1) * y = vsPOrdX I ws' cs rows x := by
    rw [← pow_succ, Nat.sub_add_cancel hq1]; rfl
  rw [eP] at dP
  have dOut := Det.mk2 dP v6
  apply FunDet.intro h0
  refine (Det.letE dW (Det.letE dy (Det.letE dFB (Det.letE dj (Det.letE dFC
    (Det.letE dr dOut)))))).mono ?_
  -- the cost
  have hNn := H.n
  have hJ : j ≤ I.n := hJn
  have hrj : r ≤ j := by rw [er, vsPR_eq hJ2]; exact Nat.minFac_le (by omega)
  have htB : tB + 1 = j := ejt.symm
  have htC : tC + 2 = r := ert.symm
  have Q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have Q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have Q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hj2 : (j + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have wC : C.wt ≤ W := H.cw
  have wx := wt_encPerm_le x
  have wy := wt_encPerm_le y
  have wX := wt_encPerm_le (vsPOrdX I ws' cs rows x)
  have wCx := wt_list2_le C (encPerm x)
  have wCy := wt_list2_le C (encPerm y)
  have wnI := wt_nat_le I.n
  have wn1 := wt_nat_le (I.n - 1)
  have wj := wt_nat_le j
  have wr := wt_nat_le r
  have wtB := wt_nat_le tB
  have wtC := wt_nat_le tC
  have w0x := wt_list3_le (.nat 0) (encPerm x) (.nat 0)
  have w00 : (Val.nat 0).wt = 2 := rfl
  have wA := wt_list3_le (.nat a.1) (encPerm a.2.1) (.nat a.2.2)
  obtain ⟨h01, -, -, hqa, -, -⟩ := vsPWalk_inv ib hxb (I.n - 1)
  have wa1 := wt_nat_le a.1
  have wa2 := wt_nat_le a.2.2
  have eAa : (vsPAccV (vsPWalk (vsPInLB I ws' cs rows) (I.n - 1) x)).wt =
      (Val.list [Val.nat a.1, encPerm a.2.1, Val.nat a.2.2]).wt := rfl
  have ey : (encPerm a.2.1).wt = (encPerm y).wt := rfl
  have es1 : GI.Machine.BinOp.sub.eval I.n 1 = I.n - 1 := rfl
  have es2 : GI.Machine.BinOp.sub.eval (GI.Machine.BinOp.div.eval j r) 1 = j / r - 1 := rfl
  have es3 : GI.Machine.BinOp.div.eval j r = j / r := rfl
  have hjr : j / r ≤ j := Nat.div_le_self _ _
  simp only [es1, es2, es3] at *
  have wW := wt_list3_le C (.nat (I.n - 1)) (.list [.nat 0, encPerm x, .nat 0])
  have wnR : (Val.list (List.map Val.nat (List.range I.n))).wt ≤ 5 * (N + 1) ^ 2 := by
    have := wt_natList_le_sq (xs := List.range I.n) (B := I.n) (fun y hy => by simp at hy; omega)
      (by simp)
    have e : natList (List.range I.n) = Val.list (List.map Val.nat (List.range I.n)) := rfl
    rw [e] at this; omega
  have wjR : (Val.list (List.map Val.nat (List.range j))).wt ≤ 5 * (N + 1) ^ 2 := by
    have := wt_natList_le_sq (xs := List.range j) (B := j) (fun y hy => by simp at hy; omega)
      (by simp)
    have e : natList (List.range j) = Val.list (List.map Val.nat (List.range j)) := rfl
    rw [e] at this; omega
  have wB2 := wt_list2_le (.list [C, encPerm y]) (.list (List.map Val.nat (List.range I.n)))
  have wC2 := wt_list2_le (.nat j) (.list (List.map Val.nat (List.range j)))
  have w4 := wt_list4_le (.nat 0) (encPerm y) (.nat (j / r - 1)) (encPerm y)
  have wO := wt_list2_le (encPerm (vsPOrdX I ws' cs rows x)) (.nat r)
  have hsB : (List.map (fun _ => vsPWStepCost Cφ N W) (List.map Val.nat (List.range I.n))).sum =
      I.n * vsPWStepCost Cφ N W := by
    rw [List.map_map, Function.comp_def, List.map_const', List.sum_replicate, List.length_range,
      smul_eq_mul]
  have hsC : (List.map (fun _ => 100 * (2 * N + 10)) (List.map Val.nat (List.range j))).sum =
      j * (100 * (2 * N + 10)) := by
    rw [List.map_map, Function.comp_def, List.map_const', List.sum_replicate, List.length_range,
      smul_eq_mul]
  have hlB : (List.map Val.nat (List.range I.n)).length = I.n := by simp
  have hlC : (List.map Val.nat (List.range j)).length = j := by simp
  rw [hsB, hsC, hlB, hlC]
  have pB : I.n * vsPWStepCost Cφ N W ≤ (N + 1) * vsPWStepCost Cφ N W :=
    Nat.mul_le_mul_right _ (by omega)
  have pC : j * (100 * (2 * N + 10)) ≤ (N + 1) * (1000 * (N + 1)) :=
    Nat.mul_le_mul (by omega) (by omega)
  have eC2 : (N + 1) * (1000 * (N + 1)) = 1000 * (N + 1) ^ 2 := by ring
  have rB := vsP_rng_le (m := I.n) (N := N) (by omega)
  have rC := vsP_rng_le (m := j) (N := N) (by omega)
  have hK : loopModK = 1000 := rfl
  have lB := vsP_loop_le (m := I.n) (N := N) (W := W)
    (Z := (Val.list [Val.list [C, encPerm y], Val.list (List.map Val.nat (List.range I.n))]).wt +
      2 * I.n + 3) (by omega) (by omega)
  have lC := vsP_loop_le (m := j) (N := N) (W := W)
    (Z := (Val.list [Val.nat j, Val.list (List.map Val.nat (List.range j))]).wt + 2 * j + 3)
    (by omega) (by omega)
  rw [hK]
  have hpc := vsPPowCost_le (n := I.n) (e := j / r - 1) (k := N)
    (by have := vsP_bits_le (j / r - 1); omega)
  have hn3 : (I.n + 1) ^ 3 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hpc' : 10 ^ 6 * (N + 1) ^ 2 * (I.n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 5 := by
    calc 10 ^ 6 * (N + 1) ^ 2 * (I.n + 1) ^ 3 ≤ 10 ^ 6 * (N + 1) ^ 2 * (N + 1) ^ 3 :=
          Nat.mul_le_mul_left _ hn3
      _ = 10 ^ 6 * (N + 1) ^ 5 := by ring
  have eW : vsPWalkCost Cφ N W = (N + 1) * vsPWStepCost Cφ N W +
      2 * 10 ^ 5 * ((N + 1) * W) + 2 * 10 ^ 5 * (N + 1) ^ 3 := by unfold vsPWalkCost; ring
  have hWN : W ≤ (N + 1) * W := Nat.le_mul_of_pos_left _ (by omega)
  have wq := wt_nat_le (j / r - 1)
  have wy' : (encPerm a.2.1).wt ≤ 4 * (I.n + 1) ^ 2 := wt_encPerm_le _
  have ha1 : a.1 ≤ 1 := by show (vsPWalk ib (I.n - 1) x).1 ≤ 1; omega
  have ha2 : a.2.2 ≤ I.n := by show (vsPWalk ib (I.n - 1) x).2.2 ≤ I.n; omega
  have e4 : (Val.list [Val.nat 0, encPerm y, Val.nat (GI.Machine.BinOp.sub.eval (j / r) 1),
      encPerm y]).wt = (Val.list [Val.nat 0, encPerm y, Val.nat (j / r - 1), encPerm y]).wt := rfl
  unfold vsPOrdCost
  omega

end GI.Impl
