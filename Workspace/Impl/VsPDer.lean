import Workspace.Impl.VsPOrdP
import Workspace.Proved.VsPDerMath
import Workspace.Lang.Prims.Ops

/-!
# The derived series of `C`

* `vsPBadE`, `vsPBad_spec`: on `[ctx, ⟨gs⟩]`, whether some generator `h` (or `1`) has
  `Λ(h) ∉ L`.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The test "not in `L`", on values. -/
noncomputable def vsPQN {n : ℕ} (ib : Perm (Fin n) → Bool) (v : Val) : Bool := by
  classical exact decide (∃ h : Perm (Fin n), v = encPerm h ∧ ib h = false)

theorem vsPQN_enc {n : ℕ} (ib : Perm (Fin n) → Bool) (h : Perm (Fin n)) :
    vsPQN ib (encPerm h) = !ib h := by
  unfold vsPQN
  cases hb : ib h
  · simp only [Bool.not_false, decide_eq_true_eq]; exact ⟨h, rfl, hb⟩
  · simp only [Bool.not_true, decide_eq_false_iff_not, not_exists, not_and]
    intro h' e; rw [encPerm_injective e] at hb; rw [hb]; decide

/-- On `[ctx, g]`: `1` if `Λ(g) ∉ L`, else `0`. -/
def vsPNotInE (inl : ℕ) : Expr := .ite (.call inl (mk2 (arg 0) (arg 1))) (.nat 0) (.nat 1)

/-- On `[ctx, ⟨gs⟩]`: `1` if some entry of `1 :: gs` is outside `L`. -/
def vsPBadE (fd : ℕ) : Expr :=
  .arith .lt (.call fd (mk2 (arg 0) (.get (arg 1) (.nat 1)))) (.length (.get (arg 1) (.nat 1)))

theorem vsPNotIn_spec {P : Program} {f inl phi Cφ N W : ℕ} (hf : P.funs[f]? = some (vsPNotInE inl))
    (hinl : P.HasAt inl (vsPInLPFuns inl phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {g : Perm (Fin I.n)} (hg : g ∈ gens I.gs) :
    FunDet P f (.list [vsPCtx I ws' cs rows hs, encPerm g])
      (boolVal (vsPQN (vsPInLB I ws' cs rows) (encPerm g))) (vsPInLPCost Cφ N W + 20 * W + 100 +
        100 * (N + 1) ^ 2) := by
  have a0 := Det.arg' (P := P) (vs := [vsPCtx I ws' cs rows hs, encPerm g]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [vsPCtx I ws' cs rows hs, encPerm g]) (rest := []) (j := 1) rfl
  have dI := Det.call (Det.mk2 a0 a1) (vsPInLP_spec hinl hphi H hg)
  rw [vsPQN_enc]
  apply FunDet.intro hf
  have wC : (vsPCtx I ws' cs rows hs).wt ≤ W := H.cw
  have wg := wt_encPerm_le g
  have hn2 : (I.n + 1) ^ 2 ≤ (N + 1) ^ 2 := Nat.pow_le_pow_left (by have := H.n; omega) 2
  have w2 := wt_list2_le (vsPCtx I ws' cs rows hs) (encPerm g)
  cases hb : vsPInLB I ws' cs rows g
  · rw [hb] at dI
    have dI0 : Det P [.list [vsPCtx I ws' cs rows hs, encPerm g]] (.call inl (mk2 (arg 0) (arg 1)))
        (.nat 0) _ := dI
    refine (Det.ite_zero dI0 (Det.nat 1)).mono ?_
    have := wt_boolVal_le true
    have := wt_boolVal_le false
    have := wt_nat_le 0
    have := wt_nat_le 1
    have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  · rw [hb] at dI
    refine (Det.ite_pos dI (by simp) (Det.nat 0)).mono ?_
    have := wt_boolVal_le true
    have := wt_boolVal_le false
    have := wt_nat_le 0
    have := wt_nat_le 1
    have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega

/-- The cost of the test on a group value. -/
def vsPBadCost (Cφ N W : ℕ) : ℕ :=
  (N + 1) ^ 2 * (vsPInLPCost Cφ N W + 20 * W + 100 + 100 * (N + 1) ^ 2) +
    10 ^ 4 * (N + 1) ^ 2 * (W + 400 * (N + 1) ^ 6) + 100 * W + 10 ^ 5 * (N + 1) ^ 6

theorem vsPBad_spec {P : Program} {f fd nt inl phi Cφ N W : ℕ} (hf : P.funs[f]? = some (vsPBadE fd))
    (hfd : P.HasAt fd (findFuns fd nt)) (hnt : P.funs[nt]? = some (vsPNotInE inl))
    (hinl : P.HasAt inl (vsPInLPFuns inl phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {gs : List (Perm (Fin I.n))}
    (hgs : ∀ g ∈ gs, g ∈ gens I.gs) (hl : gs.length ≤ I.n ^ 2) :
    FunDet P f (.list [vsPCtx I ws' cs rows hs, encGroup gs])
      (boolVal (decide (∃ h ∈ 1 :: gs, vsPInLB I ws' cs rows h = false))) (vsPBadCost Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set xs := (1 :: gs).map encPerm with hxs
  have eG : encGroup gs = .list [.nat I.n, .list xs] := rfl
  have a0 := Det.arg' (P := P) (vs := [C, encGroup gs]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [C, encGroup gs]) (rest := []) (j := 1) rfl
  rw [eG] at a1
  have dl := Det.get' a1 (Det.nat 1) (show [Val.nat I.n, .list xs][1]? = some (.list xs) from rfl)
  have hq : ∀ v ∈ xs, FunDet P nt (.list [C, v]) (boolVal (vsPQN (vsPInLB I ws' cs rows) v))
      (vsPInLPCost Cφ N W + 20 * W + 100 + 100 * (N + 1) ^ 2) := by
    intro v hv
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hv
    have hh' : h ∈ gens I.gs := by
      rcases List.mem_cons.mp hh with rfl | hh
      · exact one_mem _
      · exact hgs h hh
    exact vsPNotIn_spec hnt hinl hphi H hh'
  have dF := Det.call (Det.mk2 a0 dl) ((find_spec hfd hq).mono fun w c hw => ⟨hw.1, hw.2⟩)
  have dL := Det.length dl
  have dT := Det.arith' (op := .lt) dF dL rfl
  have ev : Val.nat (GI.Machine.BinOp.eval .lt (xs.findIdx (vsPQN (vsPInLB I ws' cs rows)))
      xs.length) = boolVal (decide (∃ h ∈ 1 :: gs, vsPInLB I ws' cs rows h = false)) := by
    simp only [GI.Machine.BinOp.eval, boolVal]
    have e : (xs.findIdx (vsPQN (vsPInLB I ws' cs rows)) < xs.length) ↔
        ∃ h ∈ 1 :: gs, vsPInLB I ws' cs rows h = false := by
      rw [List.findIdx_lt_length, hxs]
      simp only [List.mem_map, exists_exists_and_eq_and, vsPQN_enc, Bool.not_eq_eq_eq_not,
        Bool.not_true]
    by_cases hc : ∃ h ∈ 1 :: gs, vsPInLB I ws' cs rows h = false
    · rw [if_pos (e.2 hc)]
      have h1 : (decide (∃ h ∈ 1 :: gs, vsPInLB I ws' cs rows h = false)).toNat = 1 := by
        rw [Bool.toNat_eq_one]; simpa only [decide_eq_true_eq] using hc
      rw [h1]
    · rw [if_neg (fun h => hc (e.1 h))]; simp only [hc, decide_false, Bool.toNat_false]
  rw [ev] at dT
  refine FunDet.intro hf (dT.mono ?_)
  -- the cost
  have hn := H.n
  have hxl : xs.length ≤ (N + 1) ^ 2 := by
    rw [hxs, List.length_map, List.length_cons]
    have : I.n ^ 2 ≤ N ^ 2 := Nat.pow_le_pow_left hn 2
    nlinarith
  have wC : C.wt ≤ W := H.cw
  have wG := wt_encGroup_le_sq hl
  have hn6 : (I.n + 1) ^ 6 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have wxs : (Val.list xs).wt ≤ (encGroup gs).wt := by
    rw [eG]; exact (wt_le_wt_list (by simp)).le
  have w2 := wt_list2_le C (encGroup gs)
  have w3 := wt_list2_le C (.list xs)
  have hsum : (xs.map fun _ => vsPInLPCost Cφ N W + 20 * W + 100 + 100 * (N + 1) ^ 2).sum ≤
      (N + 1) ^ 2 * (vsPInLPCost Cφ N W + 20 * W + 100 + 100 * (N + 1) ^ 2) := by
    rw [List.map_const', List.sum_replicate, smul_eq_mul]
    exact Nat.mul_le_mul_right _ hxl
  have hloop : loopModK * (xs.length + 1) * ((Val.list [C, .list xs]).wt + 2 * xs.length + 3) ≤
      10 ^ 4 * (N + 1) ^ 2 * (W + 400 * (N + 1) ^ 6) := by
    have h1 : xs.length + 1 ≤ 2 * (N + 1) ^ 2 := by have := Nat.one_le_pow 2 (N + 1) (by omega); omega
    have h2 : (Val.list [C, .list xs]).wt + 2 * xs.length + 3 ≤ 5 * (W + 400 * (N + 1) ^ 6) := by
      have : (N + 1) ^ 2 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    calc loopModK * (xs.length + 1) * _ ≤ 1000 * (2 * (N + 1) ^ 2) * (5 * (W + 400 * (N + 1) ^ 6)) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ h1) h2
      _ = 10 ^ 4 * (N + 1) ^ 2 * (W + 400 * (N + 1) ^ 6) := by ring
  have wF := wt_nat_le (xs.findIdx (vsPQN (vsPInLB I ws' cs rows)))
  have hFl : xs.findIdx (vsPQN (vsPInLB I ws' cs rows)) ≤ xs.length := List.findIdx_le_length
  have wb := wt_boolVal_le (decide (∃ h ∈ 1 :: gs, vsPInLB I ws' cs rows h = false))
  have ev2 : (Val.list [C, encGroup gs]).wt = (Val.list [C, Val.list [.nat I.n, .list xs]]).wt :=
    rfl
  have w4 := wt_list2_le C (Val.list [.nat I.n, .list xs])
  have wn := wt_nat_le I.n
  have hwl : xs.length ≤ (Val.list xs).wt := (length_lt_wt_list xs).le
  have hN6 : (N + 1) ^ 2 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hN1 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hWW : W ≤ 10 ^ 4 * (N + 1) ^ 2 * (W + 400 * (N + 1) ^ 6) := by
    have : W ≤ (N + 1) ^ 2 * W := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  have h66 : (N + 1) ^ 6 ≤ 10 ^ 4 * (N + 1) ^ 2 * (W + 400 * (N + 1) ^ 6) := by
    have : (N + 1) ^ 6 ≤ (N + 1) ^ 2 * (N + 1) ^ 6 := Nat.le_mul_of_pos_left _ (by omega)
    nlinarith
  have hy : GI.Machine.BinOp.lt.eval (List.findIdx (vsPQN (vsPInLB I ws' cs rows)) xs)
      xs.length ≤ 1 := by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega
  unfold vsPBadCost
  omega

/-! ### One step of the derived series -/

/-- The bound of a call of the derived-subgroup primitive on a group value of weight at most
`320 (N + 1)^6`. -/
noncomputable def vsPDerB (hd : DerivedSubgroup) (N : ℕ) : ℕ :=
  (derivedSubgroupPrim hd).c * (320 * (N + 1) ^ 6 + 2) ^ (derivedSubgroupPrim hd).k

/-- The step, on `[ctx, i, [⟨cur⟩, ⟨last⟩]]`: `nxt = [cur, cur]`, then `[nxt, nxt]` if `nxt` has a
generator outside `L`, else `[nxt, last]`. -/
def vsPDStepE (mkg bad der : ℕ) : Expr :=
  .letE (.call mkg (mk2 (vsPC 6) (.prim der (.get (arg 2) (.nat 0)))))
    (.ite (.call bad (mk2 (arg 0) (.var 1))) (mk2 (.var 1) (.var 1))
      (mk2 (.var 1) (.get (arg 2) (.nat 1))))

/-- The value of an accumulator. -/
def vsPDAcc {n : ℕ} (cur last : List (Perm (Fin n))) : Val := .list [encGroup cur, encGroup last]

/-- The cost of a step. -/
noncomputable def vsPDStepCost (hd : DerivedSubgroup) (Cφ N W : ℕ) : ℕ :=
  vsPDerB hd N + vsPBadCost Cφ N W + 10 ^ 7 * (N + 1) ^ 9 + 100 * W

set_option maxHeartbeats 4000000 in
theorem vsPDStep_spec (hd : DerivedSubgroup) {P : Program}
    {g mkg bad der fd nt inl phi Cφ N W : ℕ} (hg : P.funs[g]? = some (vsPDStepE mkg bad der))
    (hmk : P.HasAt mkg (mkGroupFuns mkg)) (hbad : P.funs[bad]? = some (vsPBadE fd))
    (hfd : P.HasAt fd (findFuns fd nt)) (hnt : P.funs[nt]? = some (vsPNotInE inl))
    (hinl : P.HasAt inl (vsPInLPFuns inl phi))
    (hder : P.prims[der]? = some (derivedSubgroupPrim hd))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) {i : ℕ} (hi : i ≤ N)
    {cur last : List (Perm (Fin I.n))} (hc : gens cur ≤ gens I.gs) (hcl : cur.length ≤ I.n ^ 2)
    (hll : last.length ≤ I.n ^ 2) :
    FunAll P g (.list [vsPCtx I ws' cs rows hs, .nat i, vsPDAcc cur last]) (fun w c =>
      ∃ nxt : List (Perm (Fin I.n)), nxt.length ≤ I.n ^ 2 ∧ gens nxt = ⁅gens cur, gens cur⁆ ∧
        w = (if ∃ h ∈ 1 :: nxt, vsPInLB I ws' cs rows h = false then vsPDAcc nxt nxt
          else vsPDAcc nxt last) ∧ c ≤ vsPDStepCost hd Cφ N W) := by
  set C := vsPCtx I ws' cs rows hs
  set cv := [vsQGam I, vsWFrVal I.p I.d ws' cs, .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ (cs.length * cs.length)), encGroup hs, .nat I.n] with hcv
  set A := Val.list [C, .nat i, vsPDAcc cur last]
  have a0 : Det P [A] (arg 0) (.list cv) _ :=
    Det.arg' (P := P) (vs := [C, .nat i, vsPDAcc cur last]) (rest := []) (j := 0) rfl
  have c6 := Det.get' a0 (Det.nat 6) (show cv[6]? = some (.nat I.n) from rfl)
  have a2 := Det.arg' (P := P) (vs := [C, .nat i, vsPDAcc cur last]) (rest := []) (j := 2) rfl
  have dcur := Det.get' a2 (Det.nat 0)
    (show [encGroup cur, encGroup last][0]? = some (encGroup cur) from rfl)
  have dprim := derivedSubgroup_call hd hder dcur ⟨cur, rfl, rfl⟩
  have dmk := EvalAll.mk2_last c6 dprim
  have hn := H.n
  have wC : C.wt ≤ W := H.cw
  have wcur := wt_encGroup_le_sq hcl
  have wlast := wt_encGroup_le_sq hll
  have hn6 : (I.n + 1) ^ 6 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  have hn9 : (I.n + 1) ^ 9 ≤ (N + 1) ^ 9 := Nat.pow_le_pow_left (by omega) 9
  have hbound : (derivedSubgroupPrim hd).bound (encGroup cur) ≤ vsPDerB hd N := by
    unfold Prim.bound vsPDerB
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    have := (encGroup cur).size_le_wt
    omega
  refine FunAll.intro hg (EvalAll.letE (Ra := fun v c => ∃ nxt : List (Perm (Fin I.n)),
      v = encGroup nxt ∧ nxt.length ≤ I.n ^ 2 ∧ gens nxt = ⁅gens cur, gens cur⁆ ∧
      c ≤ 10 * A.wt + vsPDerB hd N + 10 ^ 6 * (N + 1) ^ 9) ?_ ?_)
  · refine EvalAll.call_funAll dmk fun v ca hv => ?_
    obtain ⟨vb, cb, ⟨hG, hcb⟩, rfl, hca⟩ := hv
    obtain ⟨nxt, rfl, hl, hmkd, -, hwt⟩ := mkGroup_gensVal hmk hG
    refine FunAll.mono hmkd fun w c hw => ⟨nxt, hw.1, hl, ?_, ?_⟩
    · obtain ⟨hs', e, -, hgs⟩ := hG
      simp only [Val.list.injEq, List.map_inj_left] at e
      have : nxt = hs' := by
        have := e; exact (List.map_injective_iff.mpr encPerm_injective) (by simpa using e)
      rw [this, hgs]
    · rw [hw.1]
      have w1 := wt_list_encPerms_le_sq hl
      have w2 := wt_list2_le (.nat I.n) (.list (nxt.map encPerm))
      have wn := wt_nat_le I.n
      have wA := wt_list3_le C (.nat i) (vsPDAcc cur last)
      have wacc := wt_list2_le (encGroup cur) (encGroup last)
      have eacc : (vsPDAcc cur last).wt = (Val.list [encGroup cur, encGroup last]).wt := rfl
      have ecv : (Val.list cv).wt = C.wt := rfl
      have hcA : (Val.list cv).wt ≤ A.wt := by
        rw [ecv]; exact (wt_le_wt_list (show C ∈ [C, .nat i, vsPDAcc cur last] by simp)).le
      have hcurA : (encGroup cur).wt ≤ A.wt := by
        have h1 : (encGroup cur).wt < (vsPDAcc cur last).wt := wt_le_wt_list (by simp)
        have h2 : (vsPDAcc cur last).wt < A.wt := wt_le_wt_list (by simp)
        omega
      have q : (N + 1) ^ 6 ≤ (N + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
      have q2 : 1 ≤ (N + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
      have hmkc : 8 * mkGroupK * (I.n + 1) ^ 9 ≤ 800000 * (N + 1) ^ 9 := by
        rw [show 8 * mkGroupK = 800000 from rfl]; omega
      have eA : A.wt = (Val.list [C, .nat i, vsPDAcc cur last]).wt := rfl
      have q3 : N + 1 ≤ (N + 1) ^ 9 := Nat.le_self_pow (by omega) _
      omega
  · rintro v ca ⟨nxt, rfl, hl, hgn, hca⟩
    have hgs : ∀ g ∈ nxt, g ∈ gens I.gs := fun g hg' =>
      hc (vsP_commutator_le_self _ (hgn ▸ Subgroup.subset_closure (by simpa using hg')))
    set E := [A, encGroup nxt]
    have b0 := Det.arg' (P := P) (vs := [C, .nat i, vsPDAcc cur last]) (rest := [encGroup nxt])
      (j := 0) rfl
    have b2 := Det.arg' (P := P) (vs := [C, .nat i, vsPDAcc cur last]) (rest := [encGroup nxt])
      (j := 2) rfl
    have v1 := Det.var' (P := P) (env := E) (i := 1) rfl
    have dB := Det.call (Det.mk2 b0 v1) (vsPBad_spec hbad hfd hnt hinl hphi H hgs hl)
    have dT := Det.mk2 v1 v1
    have dl := Det.get' b2 (Det.nat 1)
      (show [encGroup cur, encGroup last][1]? = some (encGroup last) from rfl)
    have dF := Det.mk2 v1 dl
    have wn := wt_encGroup_le_sq hl
    have w1 := wt_list2_le (encGroup nxt) (encGroup nxt)
    have w2 := wt_list2_le (encGroup nxt) (encGroup last)
    have w3 := wt_list2_le C (encGroup nxt)
    have wA := wt_list3_le C (.nat i) (vsPDAcc cur last)
    have wacc := wt_list2_le (encGroup cur) (encGroup last)
    have eacc : (vsPDAcc cur last).wt = (Val.list [encGroup cur, encGroup last]).wt := rfl
    have eA : A.wt = (Val.list [C, .nat i, vsPDAcc cur last]).wt := rfl
    have wi := wt_nat_le i
    have wb := wt_boolVal_le (decide (∃ h ∈ 1 :: nxt, vsPInLB I ws' cs rows h = false))
    have q1 : 1 ≤ (N + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have q2 : (N + 1) ^ 6 ≤ (N + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
    have q3 : N + 1 ≤ (N + 1) ^ 9 := Nat.le_self_pow (by omega) _
    have wC : C.wt ≤ W := H.cw
    have hn6' : (I.n + 1) ^ 6 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    by_cases hb : ∃ h ∈ 1 :: nxt, vsPInLB I ws' cs rows h = false
    · have h1 : (decide (∃ h ∈ 1 :: nxt, vsPInLB I ws' cs rows h = false)).toNat = 1 := by
        rw [Bool.toNat_eq_one]; simpa only [decide_eq_true_eq] using hb
      have dB1 := dB
      rw [show boolVal (decide (∃ h ∈ 1 :: nxt, vsPInLB I ws' cs rows h = false)) = .nat 1 by
        simp only [boolVal, h1]] at dB1
      refine (Det.ite_pos dB1 one_ne_zero dT).post fun c' hc' => ⟨nxt, hl, hgn, by rw [if_pos hb]; rfl, ?_⟩
      unfold vsPDStepCost
      have := wt_nat_le 1
      omega
    · have h0 : (decide (∃ h ∈ 1 :: nxt, vsPInLB I ws' cs rows h = false)).toNat = 0 := by
        rw [Bool.toNat_eq_zero]; simpa only [decide_eq_false_iff_not] using hb
      have dB0 := dB
      rw [show boolVal (decide (∃ h ∈ 1 :: nxt, vsPInLB I ws' cs rows h = false)) = .nat 0 by
        simp only [boolVal, h0]] at dB0
      refine (Det.ite_zero dB0 dF).post fun c' hc' => ⟨nxt, hl, hgn, by rw [if_neg hb]; rfl, ?_⟩
      unfold vsPDStepCost
      have := wt_nat_le 0
      omega

/-! ### The series -/

/-- On `[ctx, ⟨C⟩]`: the last term of the derived series of `C` with a generator outside `L`. -/
def vsPDerE (it : ℕ) : Expr :=
  .get (.call it (mk3 (arg 0) (.arith .add (.arith .mul (vsPC 6) (vsPC 6)) (.nat 1))
    (mk2 (arg 1) (arg 1)))) (.nat 1)

/-- The program at base `b` (14 functions + the test; `bad`, `mkg`, `der` external). -/
def vsPDerFuns (b mkg bad der : ℕ) : List Expr :=
  [vsPDerE (b + 1)] ++ iterFuns (b + 1) (b + 4) ++ [vsPDStepE mkg bad der]

theorem vsPDerFuns_length (b mkg bad der : ℕ) : (vsPDerFuns b mkg bad der).length = 5 := rfl

/-- The cost of the series. -/
noncomputable def vsPDerCost (hd : DerivedSubgroup) (Cφ N W : ℕ) : ℕ :=
  (N + 1) ^ 2 * vsPDStepCost hd Cφ N W + 10 ^ 4 * (N + 1) ^ 2 * (W + 2000 * (N + 1) ^ 6) +
    200 * W + 10 ^ 6 * (N + 1) ^ 6

theorem vsP_bad_iff {n : ℕ} {ib : Perm (Fin n) → Bool} {C Sp : Subgroup (Perm (Fin n))}
    (hSp : ∀ g ∈ C, ib g = true ↔ g ∈ Sp) {nxt : List (Perm (Fin n))} (hnC : gens nxt ≤ C) :
    (∃ h ∈ 1 :: nxt, ib h = false) ↔ ¬ gens nxt ≤ Sp := by
  constructor
  · rintro ⟨h, hh, hf⟩ hle
    have hhC : h ∈ gens nxt := by
      rcases List.mem_cons.mp hh with rfl | hh
      · exact one_mem _
      · exact Subgroup.subset_closure (by simpa using hh)
    have := (hSp h (hnC hhC)).2 (hle hhC)
    rw [this] at hf; exact Bool.noConfusion hf
  · intro hn
    by_contra hall
    push Not at hall
    apply hn
    refine (Subgroup.closure_le _).2 fun h hh => ?_
    have hh' : h ∈ nxt := by simpa using hh
    have hhC : h ∈ C := hnC (Subgroup.subset_closure (by simpa using hh'))
    exact (hSp h hhC).1 (by simpa using hall h (List.mem_cons_of_mem _ hh'))

theorem vsP_loop2_le {K N X Y : ℕ} (h1 : K + 1 ≤ 2 * N) (h2 : X ≤ 5 * Y) :
    loopModK * (K + 1) * X ≤ 10 ^ 4 * N * Y := by
  calc loopModK * (K + 1) * X ≤ 1000 * (2 * N) * (5 * Y) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 1000 h1) h2
    _ = 10 ^ 4 * N * Y := by ring

set_option maxHeartbeats 4000000 in
/-- **The derived series.** On `[ctx, ⟨C⟩]` (with `C` not inside `Sp`), the program returns the
generators `ns` of a term `N₀ = C^(j)` of the derived series with `N₀ ⊄ Sp` and
`[N₀, N₀] ≤ Sp`. Here `Sp` is the subgroup that the test describes on `C`. -/
theorem vsPDer_spec (hd : DerivedSubgroup) {P : Program}
    {b mkg bad der fd nt inl phi Cφ N W : ℕ} (h : P.HasAt b (vsPDerFuns b mkg bad der))
    (hmk : P.HasAt mkg (mkGroupFuns mkg)) (hbad : P.funs[bad]? = some (vsPBadE fd))
    (hfd : P.HasAt fd (findFuns fd nt)) (hnt : P.funs[nt]? = some (vsPNotInE inl))
    (hinl : P.HasAt inl (vsPInLPFuns inl phi))
    (hder : P.prims[der]? = some (derivedSubgroupPrim hd))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    {ws' cs : List (List ℕ)} {rows : List VsRow} {hs : List (Perm (Fin I.n))}
    (H : VsPCtxOK I N W ws' cs rows hs) (hnN : I.n * I.n + 1 ≤ N)
    {ccs : List (Perm (Fin I.n))} (hC : gens ccs ≤ gens I.gs) (hcl : ccs.length ≤ I.n ^ 2)
    {Sp : Subgroup (Perm (Fin I.n))}
    (hSp : ∀ g ∈ gens ccs, vsPInLB I ws' cs rows g = true ↔ g ∈ Sp) (hCS : ¬ gens ccs ≤ Sp) :
    FunAll P b (.list [vsPCtx I ws' cs rows hs, encGroup ccs]) (fun w c =>
      ∃ (ns : List (Perm (Fin I.n))) (j : ℕ), w = encGroup ns ∧ ns.length ≤ I.n ^ 2 ∧
        gens ns = vsPDer (gens ccs) j ∧ ¬ vsPDer (gens ccs) j ≤ Sp ∧
        vsPDer (gens ccs) (j + 1) ≤ Sp ∧ c ≤ vsPDerCost hd Cφ N W) := by
  have h0 : P.funs[b]? = some (vsPDerE (b + 1)) := h.get (j := 0) (by simp [vsPDerFuns])
  have hit : P.HasAt (b + 1) (iterFuns (b + 1) (b + 4)) := h.block 1 rfl
  have hst : P.funs[b + 4]? = some (vsPDStepE mkg bad der) :=
    h.get (j := 4) (by rw [vsPDerFuns_length]; omega)
  set C := vsPCtx I ws' cs rows hs
  set G := gens ccs
  set ib := vsPInLB I ws' cs rows
  set K := I.n * I.n + 1
  have hn := H.n
  have hn6 : (I.n + 1) ^ 6 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
  -- the invariant
  set Inv : ℕ → Val → Prop := fun i acc => ∃ (cur last : List (Perm (Fin I.n))) (j : ℕ),
    acc = vsPDAcc cur last ∧ cur.length ≤ I.n ^ 2 ∧ last.length ≤ I.n ^ 2 ∧
    gens cur = vsPDer G i ∧ gens last = vsPDer G j ∧ j ≤ i ∧ ¬ vsPDer G j ≤ Sp ∧
    ∀ j', j < j' → j' ≤ i → vsPDer G j' ≤ Sp
  have hM : ∀ i acc, i ≤ K → Inv i acc → acc.wt ≤ 2000 * (N + 1) ^ 6 := by
    rintro i acc - ⟨cur, last, j, rfl, h1, h2, -⟩
    have := wt_encGroup_le_sq h1
    have := wt_encGroup_le_sq h2
    have := wt_list2_le (encGroup cur) (encGroup last)
    have : 1 ≤ (N + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    unfold vsPDAcc
    omega
  have hInv0 : Inv 0 (vsPDAcc ccs ccs) :=
    ⟨ccs, ccs, 0, rfl, hcl, hcl, rfl, rfl, le_rfl, hCS, fun j' h1 h2 => by omega⟩
  have hstep : ∀ i acc, i < K → Inv i acc →
      FunAll P (b + 4) (.list [C, .nat i, acc]) (fun w cost => Inv (i + 1) w ∧
        cost ≤ vsPDStepCost hd Cφ N W) := by
    rintro i acc hi ⟨cur, last, j, rfl, h1, h2, hcur, hlast, hji, hj, hgood⟩
    have hcG : gens cur ≤ gens I.gs := hcur ▸ (vsPDer_le G i).trans hC
    refine (vsPDStep_spec hd hst hmk hbad hfd hnt hinl hder hphi H (i := i) (by omega) hcG h1 h2).mono
      ?_
    rintro w c ⟨nxt, hl, hgn, rfl, hc⟩
    refine ⟨?_, hc⟩
    have hgn' : gens nxt = vsPDer G (i + 1) := by rw [hgn, hcur]; rfl
    have hnC : gens nxt ≤ G := hgn' ▸ vsPDer_le G (i + 1)
    have hbiff := vsP_bad_iff (ib := ib) hSp hnC
    by_cases hb : ∃ h ∈ 1 :: nxt, ib h = false
    · rw [if_pos hb]
      refine ⟨nxt, nxt, i + 1, rfl, hl, hl, hgn', hgn', le_rfl, hgn' ▸ hbiff.1 hb,
        fun j' h1 h2 => by omega⟩
    · rw [if_neg hb]
      refine ⟨nxt, last, j, rfl, hl, h2, hgn', hlast, by omega, hj, fun j' h1' h2' => ?_⟩
      rcases Nat.lt_or_ge j' (i + 1) with hlt | hge
      · exact hgood j' h1' (by omega)
      · have : j' = i + 1 := by omega
        subst this
        rw [← hgn']
        by_contra hc'
        exact hb (hbiff.2 hc')
  have hiter := iter_spec hit (c := C) (k := K) (acc0 := vsPDAcc ccs ccs) (Inv := Inv)
    (M := 2000 * (N + 1) ^ 6) (B := fun _ => vsPDStepCost hd Cφ N W) hInv0 hM hstep
  set cv := [vsQGam I, vsWFrVal I.p I.d ws' cs, .nat I.p, .list (rows.map VsRow.val),
    natList (vsWZ (cs.length * cs.length)), encGroup hs, .nat I.n] with hcv
  set A := Val.list [C, encGroup ccs]
  have a0 : Det P [A] (arg 0) (.list cv) _ :=
    Det.arg' (P := P) (vs := [C, encGroup ccs]) (rest := []) (j := 0) rfl
  have a0' := Det.arg' (P := P) (vs := [C, encGroup ccs]) (rest := []) (j := 0) rfl
  have a1 := Det.arg' (P := P) (vs := [C, encGroup ccs]) (rest := []) (j := 1) rfl
  have c6 := Det.get' a0 (Det.nat 6) (show cv[6]? = some (.nat I.n) from rfl)
  have dK := Det.arith' (op := .add) (Det.arith' (op := .mul) c6 c6 rfl) (Det.nat 1)
    (show GI.Machine.BinOp.eval .add (GI.Machine.BinOp.eval .mul I.n I.n) 1 = K from rfl)
  have dacc := Det.mk2 a1 a1
  have dargs := Det.mk3 a0' dK dacc
  have wC : C.wt ≤ W := H.cw
  have wG := wt_encGroup_le_sq hcl
  have wA := wt_list2_le C (encGroup ccs)
  have ecv : (Val.list cv).wt = C.wt := rfl
  have wcv6 : (Val.nat I.n).wt ≤ I.n + 2 := wt_nat_le _
  have wK := wt_nat_le K
  have wacc := wt_list2_le (encGroup ccs) (encGroup ccs)
  have eacc : (vsPDAcc ccs ccs).wt = (Val.list [encGroup ccs, encGroup ccs]).wt := rfl
  have w3 := wt_list3_le C (.nat K) (vsPDAcc ccs ccs)
  have hK2 : K ≤ (N + 1) ^ 2 := by
    have : I.n * I.n ≤ N * N := Nat.mul_le_mul hn hn
    nlinarith
  have q1 : 1 ≤ (N + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : N + 1 ≤ (N + 1) ^ 6 := Nat.le_self_pow (by omega) _
  have emul : GI.Machine.BinOp.eval .mul I.n I.n = I.n * I.n := rfl
  have emul' : I.n * I.n ≤ (N + 1) ^ 2 := by omega
  obtain ⟨cd, dargs', hcd⟩ : ∃ cd, Det P [A] (mk3 (arg 0) (.arith .add (.arith .mul (vsPC 6)
      (vsPC 6)) (.nat 1)) (mk2 (arg 1) (arg 1))) (.list [C, .nat K, vsPDAcc ccs ccs]) cd ∧
      cd ≤ 100 * W + 10 ^ 5 * (N + 1) ^ 6 := ⟨_, dargs, by
        have eA : A.wt = (Val.list [C, encGroup ccs]).wt := rfl
        have eu : (Val.list [C, Val.nat K, Val.list [encGroup ccs, encGroup ccs]]).wt =
            (Val.list [C, Val.nat K, vsPDAcc ccs ccs]).wt := rfl
        omega⟩
  set CI := ∑ i ∈ Finset.range K, vsPDStepCost hd Cφ N W +
    loopModK * (K + 1) * ((Val.list [C, .nat K, vsPDAcc ccs ccs]).wt + K + 2000 * (N + 1) ^ 6 + 1)
  apply FunAll.intro h0
  refine EvalAll.get (Ra := fun w c => Inv K w ∧ c ≤ cd + CI + 2000 * (N + 1) ^ 6 + 1)
    (EvalAll.call_funAll dargs' fun v ca hv => ?_) (Det.nat 1) ?_
  · obtain ⟨rfl, hca⟩ := hv
    refine (FunAll.mono hiter fun w c hw => ⟨hw.1, ?_⟩)
    have := hM K w le_rfl hw.1
    omega
  · rintro va ca vb cb ⟨hinv, hc⟩ ⟨rfl, hcb⟩
    obtain ⟨cur, last, j, rfl, h1, h2, hcur, hlast, hjK, hj, hgood⟩ := hinv
    refine ⟨[encGroup cur, encGroup last], 1, rfl, rfl, by simp, last, j, rfl, h2, hlast, hj, ?_, ?_⟩
    · -- `j < K` because the term `K` is trivial
      have hbot := vsPDer_bot I.solvable hC
      have hjK' : j < K := by
        rcases Nat.lt_or_ge j K with h | h
        · exact h
        · exfalso
          have : j = K := by omega
          subst this
          exact hj (by rw [hbot]; exact bot_le)
      exact hgood (j + 1) (by omega) (by omega)
    · have wl := wt_encGroup_le_sq h2
      have hsum : ∑ i ∈ Finset.range K, vsPDStepCost hd Cφ N W ≤
          (N + 1) ^ 2 * vsPDStepCost hd Cφ N W := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        exact Nat.mul_le_mul_right _ hK2
      have hloop : loopModK * (K + 1) * ((Val.list [C, .nat K, vsPDAcc ccs ccs]).wt + K +
          2000 * (N + 1) ^ 6 + 1) ≤ 10 ^ 4 * (N + 1) ^ 2 * (W + 2000 * (N + 1) ^ 6) := by
        have h1 : K + 1 ≤ 2 * (N + 1) ^ 2 := by omega
        have h2 : (Val.list [C, .nat K, vsPDAcc ccs ccs]).wt + K + 2000 * (N + 1) ^ 6 + 1 ≤
            5 * (W + 2000 * (N + 1) ^ 6) := by
          have eu : (Val.list [C, Val.nat K, Val.list [encGroup ccs, encGroup ccs]]).wt =
              (Val.list [C, Val.nat K, vsPDAcc ccs ccs]).wt := rfl
          omega
        exact vsP_loop2_le h1 h2
      have wget := wt_le_wt_list (show encGroup last ∈ [encGroup cur, encGroup last] by simp)
      have wcur := wt_encGroup_le_sq h1
      unfold vsPDerCost
      simp only [List.getElem_cons_succ, List.getElem_cons_zero]
      omega

end GI.Impl
