import Workspace.Impl.VsPBasic

/-!
# The context of step 4, and tests on permutations

The programs of step 4 share a context value
`vsPCtx I ws' cs rows hs = [Γ, fr, p, rows, 0^(D·D), ⟨hs⟩, n]`: the instance, the frame, the prime,
the echelon rows of the flattened basis of `L`, the zero vector of length `D²`, and the
generators of `H`, and the degree `n`.

* `vsPInLPE`, `vsPInLP_spec`: on `[ctx, g]`, whether the local matrix of `g` lies in the span of
  the rows (`vsPInLB`).
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The context of step 4. -/
def vsPCtx (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (hs : List (Perm (Fin I.n))) : Val :=
  .list [vsQGam I, vsWFrVal I.p I.d ws' cs, .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ (cs.length * cs.length)), encGroup hs, .nat I.n]

/-- Entry `k` of the context, which is entry `0` of the argument. -/
def vsPC (k : ℕ) : Expr := .get (arg 0) (.nat k)

/-- Whether the local matrix of `g` lies in the span of the rows. -/
noncomputable def vsPInLB (I : VecStabInst) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (g : Perm (Fin I.n)) : Bool :=
  decide ((vsSift I.p rows ((vsPLocL I ws' cs g).flatten, [])).1 = vsWZ (cs.length * cs.length))

/-- On `[ctx, g]`: is the local matrix of `g` in the span of the rows? -/
def vsPInLPE (loc inl : ℕ) : Expr :=
  .letE (.call loc (mk3 (vsPC 0) (vsPC 1) (arg 1)))
    (.call inl (mk4 (.get (.get (.var 0) (.nat 0)) (.nat 2)) (.get (.get (.var 0) (.nat 0)) (.nat 3))
      (.get (.get (.var 0) (.nat 0)) (.nat 4)) (.var 1)))

/-- The test at base `b` (59 functions; `phi` is the matrix program). -/
def vsPInLPFuns (b phi : ℕ) : List Expr :=
  [vsPInLPE (b + 1) (b + 2), vsPLocE phi (b + 26)] ++ vsPInLFuns (b + 2) ++ vsWLocFuns (b + 26)

theorem vsPInLPFuns_length (b phi : ℕ) : (vsPInLPFuns b phi).length = 59 := rfl

/-- The size hypotheses of a context. -/
structure VsPCtxOK (I : VecStabInst) (N W : ℕ) (ws' cs : List (List ℕ)) (rows : List VsRow)
    (hs : List (Perm (Fin I.n))) : Prop where
  sz : VsQSz I.p I.d (vsQExp I) N
  gam : (vsQGam I).wt ≤ N
  n : I.n ≤ N
  fr : VsWFrOK I.p N I.d ws' cs
  dd : cs.length * cs.length ≤ N
  rf : ∀ r ∈ rows, VsRowFits N (cs.length * cs.length) 0 r
  rl : rows.length ≤ N
  cw : (vsPCtx I ws' cs rows hs).wt ≤ W

/-- The cost of the test. -/
def vsPInLPCost (Cφ N W : ℕ) : ℕ := vsPLocCost Cφ N + 10 ^ 9 * (N + 1) ^ 4 + 100 * W

set_option maxHeartbeats 1000000 in
/-- **The membership test for a permutation.** -/
theorem vsPInLP_spec {P : Program} {b phi Cφ N W : ℕ} (h : P.HasAt b (vsPInLPFuns b phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {g : Perm (Fin I.n)} (hg : g ∈ gens I.gs) :
    FunDet P b (.list [vsPCtx I ws' cs rows hs, encPerm g]) (boolVal (vsPInLB I ws' cs rows g))
      (vsPInLPCost Cφ N W) := by
  have h0 : P.funs[b]? = some (vsPInLPE (b + 1) (b + 2)) := h.get (j := 0) (by simp [vsPInLPFuns])
  have h1 : P.funs[b + 1]? = some (vsPLocE phi (b + 26)) := h.get (j := 1) (by simp [vsPInLPFuns])
  have hin : P.HasAt (b + 2) (vsPInLFuns (b + 2)) := h.block 2 rfl
  have hlo : P.HasAt (b + 26) (vsWLocFuns (b + 26)) := h.block 26 rfl
  set cv := [vsQGam I, vsWFrVal I.p I.d ws' cs, .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ (cs.length * cs.length)), encGroup hs, .nat I.n] with hcv
  show FunDet P b (.list [.list cv, encPerm g]) _ _
  set A := vsPLocL I ws' cs g with hA
  have a0 : Det P [.list [.list cv, encPerm g]] (arg 0) (.list cv) _ :=
    Det.arg' (P := P) (vs := [.list cv, encPerm g]) (rest := []) (j := 0) rfl
  have a1 : Det P [.list [.list cv, encPerm g]] (arg 1) (encPerm g) _ :=
    Det.arg' (P := P) (vs := [.list cv, encPerm g]) (rest := []) (j := 1) rfl
  have c0 := Det.get' a0 (Det.nat 0) (show cv[0]? = some (vsQGam I) from rfl)
  have c1 := Det.get' a0 (Det.nat 1) (show cv[1]? = some (vsWFrVal I.p I.d ws' cs) from rfl)
  have dL := Det.call (Det.mk3 c0 c1 a1)
    (vsPLoc_spec h1 hlo hphi H.sz H.gam H.n H.fr hg)
  have v0 := Det.get' (Det.var' (P := P) (env := [.list [.list cv, encPerm g], vsWVs A]) (i := 0) rfl)
      (Det.nat 0) (show [Val.list cv, encPerm g][0]? = some (.list cv) from rfl)
  have e2 := Det.get' v0 (Det.nat 2) (show cv[2]? = some (.nat I.p) from rfl)
  have e3 := Det.get' v0 (Det.nat 3) (show cv[3]? = some (.list (rows.map VsRow.val)) from rfl)
  have e4 := Det.get' v0 (Det.nat 4)
    (show cv[4]? = some (natList (vsWZ (cs.length * cs.length))) from rfl)
  have vA := Det.var' (P := P) (env := [.list [.list cv, encPerm g], vsWVs A]) (i := 1) rfl
  have hAsq : VsWSq I.p cs.length A := vsPLocL_sq g
  have dI := Det.call (Det.mk4 e2 e3 e4 vA)
    (vsPInL_spec hin I.prime.pos H.sz.pN H.dd H.rf H.rl hAsq)
  apply FunDet.intro h0
  refine (Det.letE dL dI).mono ?_
  -- the cost
  have hDN : cs.length ≤ N := le_trans (Nat.le_mul_self _) H.dd
  have wR := wt_vsWVs_le (N := N) (us := A) (VsWFit.bnd hAsq.1 H.sz.pN hDN)
    (by rw [hAsq.2]; omega)
  have wCv : (Val.list cv).wt ≤ W := H.cw
  have w2 := wt_list2_le (.list cv) (encPerm g)
  have hm : ∀ v ∈ cv, v.wt < (Val.list cv).wt := fun v hv => wt_le_wt_list hv
  have m0 := hm (vsQGam I) (by simp [hcv])
  have m1 := hm (vsWFrVal I.p I.d ws' cs) (by simp [hcv])
  have m2 := hm (.nat I.p) (by simp [hcv])
  have m3 := hm (.list (rows.map VsRow.val)) (by simp [hcv])
  have m4 := hm (natList (vsWZ (cs.length * cs.length))) (by simp [hcv])
  have wg' := wt_encPerm_le g
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by have := H.n; omega) 2
  have w3 := wt_list3_le (vsQGam I) (vsWFrVal I.p I.d ws' cs) (encPerm g)
  have w4 := wt_list4_le (.nat I.p) (.list (rows.map VsRow.val))
    (natList (vsWZ (cs.length * cs.length))) (vsWVs A)
  have wb := wt_boolVal_le (vsPInLB I ws' cs rows g)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have eB : boolVal (decide ((vsSift I.p rows (A.flatten, [])).1 = vsWZ (cs.length * cs.length))) =
      boolVal (vsPInLB I ws' cs rows g) := rfl
  have wy : (vsWVs (vsPLocL I ws' cs g)).wt = (vsWVs A).wt := rfl
  have wi : (Val.list cv).wt ≤ W := H.cw
  have wz : (boolVal (decide ((vsSift I.p rows (A.flatten, [])).1 =
      vsWZ (cs.length * cs.length)))).wt ≤ 3 := wt_boolVal_le _
  simp only [vsPInLPCost, vsPLocCost] at *
  omega

end GI.Impl
