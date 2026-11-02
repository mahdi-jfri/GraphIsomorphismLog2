import Workspace.Impl.VsQAnaLC
import Workspace.Impl.VsWProgBas
import Workspace.Proved.VsQSplit1

/-!
# Common bounds for the analysis, and the chain split program

* Weight bounds for the local context `vsQLCV s` under the size bound `VsQDSz I S Tm`.
* `vsQSpl_spec`: on `[vsQLCV s, us]` for a local spanning list `us`, the program returns the
  chain split `[1, [1], ⟨hs⟩, [lift us, ws']]` (`vsQ_split1` says when it is correct).
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst} {S Tm : ℕ}

section Bounds

variable (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
include hS hs

theorem vsQ_frOK : VsWFrOK I.p (4 * S) I.d s.ws' (vsQCs s) := by
  have hcl : (vsQCs s).length ≤ s.ws'.length + s.ws.length :=
    vsWComp_length_le I.prime.pos (show I.p ≤ 4 * S by have := hS.p; omega)
      (show I.d ≤ 4 * S by have := hS.d; omega) hs.fit' hs.fit
  have := hs.wl; have := hs.wl'; have := hS.d; have := hS.p
  exact ⟨I.prime.one_lt, by omega, by omega, hs.fit', vsWComp_fit I.prime.pos hs.fit' hs.fit,
    by omega⟩

theorem vsQ_wt_fr : (vsWFrVal I.p I.d s.ws' (vsQCs s)).wt ≤ 100000 * S ^ 3 := by
  have h := wt_vsWFrVal_le (vsQ_frOK hS hs)
  have := vsQ_four_pow 3 hS.one_le
  norm_num at this
  omega

theorem vsQ_wt_loc {us : List (List ℕ)} (hu : VsWFit I.p (vsQD s) us) (hl : us.length ≤ I.d) :
    (vsWVs us).wt ≤ 100 * S ^ 3 := by
  have hD := vsQD_le hs
  have h1 := wt_vsWVs_le (N := S) (VsWFit.bnd hu hS.p (by have := hS.d; omega))
    (by have := hS.d; omega)
  have : (S + 1) ^ 3 ≤ 8 * S ^ 3 := by
    have := hS.one_le
    calc (S + 1) ^ 3 ≤ (2 * S) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * S ^ 3 := by ring
  have := hS.pow_le (show 0 ≤ 3 by omega)
  simp at this
  omega

theorem vsQ_wt_mats {Ms : List (List (List ℕ))} (hM : ∀ M ∈ Ms, VsWSq I.p (vsQD s) M)
    (hl : Ms.length ≤ S ^ 2) : (vsFMatsVal Ms).wt ≤ 1000 * S ^ 5 := by
  have hD := vsQD_le hs
  have h1 := vs_wt_list_le_of (Ms.map fun M => Val.list (M.map natList)) (c := 100 * S ^ 3) (by
    intro v hv
    obtain ⟨M, hM', rfl⟩ := List.mem_map.mp hv
    exact vsQ_wt_loc hS hs (hM M hM').1 (by rw [(hM M hM').2]; exact hD))
  rw [List.length_map] at h1
  have h2 : Ms.length * (2 * (100 * S ^ 3) + 1) ≤ S ^ 2 * (201 * S ^ 3) :=
    Nat.mul_le_mul hl (by have := hS.pow_le (show 0 ≤ 3 by omega); simp at this; omega)
  have e : S ^ 2 * (201 * S ^ 3) = 201 * S ^ 5 := by ring
  have := hS.pow_le (show 0 ≤ 5 by omega); simp at this
  unfold vsFMatsVal
  omega

theorem vsQ_hsl : (1 :: s.hs).length ≤ S ^ 2 := by
  have h1 := hs.hsl
  have h2 : (I.n + 1) ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hS.n 2
  have h3 : (I.n + 1) ^ 2 = I.n ^ 2 + 2 * I.n + 1 := by ring
  simp only [List.length_cons]; omega

theorem vsQ_wt_Ms : (vsFMatsVal (vsQMs s)).wt ≤ 1000 * S ^ 5 :=
  vsQ_wt_mats hS hs (vsQMs_sq s) (by simp only [vsQMs, List.length_map]; exact vsQ_hsl hS hs)

theorem vsQ_wt_LC : (vsQLCV s).wt ≤ 10 ^ 6 * S ^ 6 := by
  have h1 := wt_list4_le (vsQStV I s) (vsWFrVal I.p I.d s.ws' (vsQCs s)) (.nat (vsQD s))
    (vsFMatsVal (vsQMs s))
  have := hS.wt_st hs
  have := vsQ_wt_fr hS hs
  have := vsQ_wt_Ms hS hs
  have hD := vsQD_le hs
  have := wt_nat_le (vsQD s)
  have := hS.d
  have := hS.pow_le (show 3 ≤ 6 by omega)
  have := hS.pow_le (show 5 ≤ 6 by omega)
  have := hS.pow_le (show 1 ≤ 6 by omega)
  simp only [pow_one] at *
  unfold vsQLCV
  omega

end Bounds

/-! ### The chain split program -/

/-- The state, inside the local context in argument 0. -/
def vsQLx (k : ℕ) : Expr := .get (arg 0) (.nat k)

/-- On `[lc, us]`: the split `[1, [1], ⟨hs⟩, [basis of lift us, ws']]`. -/
def vsQSplE (lift bas : ℕ) : Expr :=
  mk4 (.nat 1) (mk1 (.get (.get (.get (vsQLx 0) (.nat 1)) (.nat 1)) (.nat 0)))
    (.get (vsQLx 0) (.nat 1))
    (mk2 (.call bas (mk2 (.get (.get (vsQLx 1) (.nat 0)) (.nat 0))
        (.call lift (mk2 (vsQLx 1) (arg 1)))))
      (.get (vsQLx 0) (.nat 2)))

/-- The chain split program at base `b` (60 functions). -/
def vsQSplFuns (b : ℕ) : List Expr :=
  [vsQSplE (b + 1) (b + 21)] ++ vsWLiftFuns (b + 1) ++ vsWBasFuns (b + 21)

theorem vsQSplFuns_length (b : ℕ) : (vsQSplFuns b).length = 60 := by
  simp [vsQSplFuns, vsWLiftFuns_length, vsWBasFuns_length]

/-- The lows of the chain split by `us`. -/
noncomputable def vsQSplLows (s : VsQSt I) (us : List (List ℕ)) : List (List (List ℕ)) :=
  [vsWBas I.p (vsWLift I.p I.d s.ws' (vsQCs s) us), s.ws']

set_option maxHeartbeats 1000000 in
/-- **The chain split program.** -/
theorem vsQSpl_spec {P : Program} {b : ℕ} (h : P.HasAt b (vsQSplFuns b)) (hS : VsQDSz I S Tm)
    {s : VsQSt I} (hs : VsQStOK s) {us : List (List ℕ)} (hus : VsWFit I.p (vsQD s) us)
    (hul : us.length ≤ I.d) :
    FunDet P b (.list [vsQLCV s, vsWVs us]) (vsQSplitV [1] s.hs (vsQSplLows s us))
      (10 ^ 13 * S ^ 6) := by
  have h0 : P.funs[b]? = some (vsQSplE (b + 1) (b + 21)) := h.get (j := 0) (by simp [vsQSplFuns])
  have hl : P.HasAt (b + 1) (vsWLiftFuns (b + 1)) := h.block 1 rfl
  have hb : P.HasAt (b + 21) (vsWBasFuns (b + 21)) := h.block 21 rfl
  set N := 4 * S with hN
  have hFr := vsQ_frOK hS hs
  have hD := vsQD_le hs
  have hwl' := hs.wl'
  have hSd := hS.d
  have hSp := hS.p
  set st := vsQStV I s with hst
  set frV := vsWFrVal I.p I.d s.ws' (vsQCs s) with hfrV
  set lc := vsQLCV s with hlc
  set X := Val.list [lc, vsWVs us] with hX
  have a0 := Det.arg' (P := P) (rest := []) (vs := [lc, vsWVs us]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [lc, vsWVs us]) (j := 1) rfl
  have g0 : Det P [X] (vsQLx 0) st _ := Det.get' a0 (Det.nat 0)
    (show [st, frV, .nat (vsQD s), vsFMatsVal (vsQMs s)][0]? = some st from rfl)
  have g1 : Det P [X] (vsQLx 1) frV _ := Det.get' a0 (Det.nat 1)
    (show [st, frV, .nat (vsQD s), vsFMatsVal (vsQMs s)][1]? = some frV from rfl)
  have gH := Det.get' g0 (Det.nat 1) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
    natList s.x, natList s.y][1]? = some (encGroup s.hs) from rfl)
  have gW := Det.get' g0 (Det.nat 2) (show [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws,
    natList s.x, natList s.y][2]? = some (vsWVs s.ws') from rfl)
  have gL := Det.get' gH (Det.nat 1) (show [Val.nat I.n, .list ((1 :: s.hs).map encPerm)][1]? =
    some (.list ((1 :: s.hs).map encPerm)) from rfl)
  have g1p := Det.get' gL (Det.nat 0) (show ((1 :: s.hs).map encPerm)[0]? = some (encPerm 1) from rfl)
  have gF0 := Det.get' g1 (Det.nat 0) (show [Val.list [.nat I.p, .nat I.d, natList (vsWZ I.d),
    natList (vsWZ (vsQCs s).length)], vsWVs s.ws', vsWVs (vsQCs s),
    .list ((vsWFrRows I.p s.ws' (vsQCs s)).map VsRow.val)][0]? =
      some (.list [.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ (vsQCs s).length)])
        from rfl)
  have gp := Det.get' gF0 (Det.nat 0) (show [Val.nat I.p, .nat I.d, natList (vsWZ I.d),
    natList (vsWZ (vsQCs s).length)][0]? = some (.nat I.p) from rfl)
  have dlift := Det.call (Det.mk2 g1 a1) (vsWLift_spec hl hFr hus (by omega))
  have hlf : VsWFit I.p I.d (vsWLift I.p I.d s.ws' (vsQCs s) us) :=
    vsWLift_fit I.prime.pos hs.fit' _ _
  have hll : (vsWLift I.p I.d s.ws' (vsQCs s) us).length = s.ws'.length + us.length := by
    simp [vsWLift]
  have dbas := Det.call (Det.mk2 gp dlift) (vsWBas_spec hb I.prime.pos (N := N) (by omega)
    (by omega) hlf (by omega))
  have dres := Det.mk4 (Det.nat 1) (Det.mk1 g1p) gH (Det.mk2 dbas gW)
  refine FunDet.intro h0 (dres.mono ?_)
  -- the cost
  have wLC := vsQ_wt_LC hS hs
  have elc : lc.wt = (vsQLCV s).wt := rfl
  have wX := wt_list2_le lc (vsWVs us)
  have wus := vsQ_wt_loc hS hs hus hul
  have hE : ∀ v ∈ [st, frV, Val.nat (vsQD s), vsFMatsVal (vsQMs s)], v.wt < lc.wt :=
    fun v hv => wt_le_wt_list hv
  have wst := hE st (by simp)
  have wfr := hE frV (by simp)
  have hEs : ∀ v ∈ [vsQGam I, encGroup s.hs, vsWVs s.ws', vsWVs s.ws, natList s.x, natList s.y],
      v.wt < st.wt := fun v hv => wt_le_wt_list hv
  have wH := hEs (encGroup s.hs) (by simp)
  have wW := hEs (vsWVs s.ws') (by simp)
  have wL : (Val.list ((1 :: s.hs).map encPerm)).wt < (encGroup s.hs).wt :=
    wt_le_wt_list (show Val.list ((1 :: s.hs).map encPerm) ∈ [Val.nat I.n,
      .list ((1 :: s.hs).map encPerm)] by simp)
  have w1 : (encPerm 1).wt < (Val.list ((1 :: s.hs).map encPerm)).wt :=
    wt_le_wt_list (show encPerm (1 : Perm (Fin I.n)) ∈ (1 :: s.hs).map encPerm by simp)
  have wF0 : (Val.list [.nat I.p, .nat I.d, natList (vsWZ I.d),
      natList (vsWZ (vsQCs s).length)]).wt < frV.wt := wt_le_wt_list (by simp [hfrV, vsWFrVal])
  have wpv : (Val.nat I.p).wt < (Val.list [.nat I.p, .nat I.d, natList (vsWZ I.d),
      natList (vsWZ (vsQCs s).length)]).wt := wt_le_wt_list (by simp)
  have wlift := vsQ_wt_loc hS hs (s := s) (us := []) (by intro u hu; simp at hu) (by simp)
  have wliftV := wt_vsWVs_le (N := N) (VsWFit.bnd hlf (by omega) (by omega)) (by omega)
  have hbf := vsWBas_fit I.prime.pos hlf
  haveI : Fact I.p.Prime := ⟨I.prime⟩
  have hbl : (vsWBas I.p (vsWLift I.p I.d s.ws' (vsQCs s) us)).length ≤ I.d := by
    rw [vsWBas_length I.prime hlf]
    exact (Submodule.finrank_le _).trans (by simp)
  have wbas := hS.wt_bas hbf hbl
  have w2 := wt_list2_le (Val.nat I.p) (vsWVs (vsWLift I.p I.d s.ws' (vsQCs s) us))
  have w2' := wt_list2_le frV (vsWVs us)
  have w2'' := wt_list2_le (vsWVs (vsWBas I.p (vsWLift I.p I.d s.ws' (vsQCs s) us))) (vsWVs s.ws')
  have w1' := wt_list1_le (encPerm (1 : Perm (Fin I.n)))
  have w4 := wt_list4_le (.nat 1) (.list [encPerm (1 : Perm (Fin I.n))]) (encGroup s.hs)
    (.list [vsWVs (vsWBas I.p (vsWLift I.p I.d s.ws' (vsQCs s) us)), vsWVs s.ws'])
  have wn := wt_nat_le 1
  have wn0 := wt_nat_le 0
  have wn2 := wt_nat_le 2
  have e5 : (N + 1) ^ 5 = (4 * S + 1) ^ 5 := rfl
  have e3 : (N + 1) ^ 3 = (4 * S + 1) ^ 3 := rfl
  have p5 := vsQ_four_pow 5 hS.one_le
  have p3 := vsQ_four_pow 3 hS.one_le
  norm_num at p5 p3
  have q36 := hS.pow_le (show 3 ≤ 6 by omega)
  have q56 := hS.pow_le (show 5 ≤ 6 by omega)
  have eX : X.wt = (Val.list [lc, vsWVs us]).wt := rfl
  have eO : (vsQSplitV [1] s.hs (vsQSplLows s us)).wt = (Val.list [.nat 1, .list [encPerm 1],
    encGroup s.hs, .list [vsWVs (vsWBas I.p (vsWLift I.p I.d s.ws' (vsQCs s) us)),
      vsWVs s.ws']]).wt := rfl
  rw [e5] at *
  rw [e3] at wliftV
  omega

end GI.Impl
