module

public import Workspace.Impl.GMPGraphRows
public import Workspace.Lang.Prims.Blocks

@[expose] public section

/-! # The kernel of conjugation on a listed coset space -/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

/-- Input `[n, gv, reps, hs]`. Compute the graph, encode both groups,
then take the preimage of the identity subgroup on the coset labels. -/
def gmpListedKernelEntryF (graph mg jpre : ℕ) : Expr :=
  .letE (.call graph (mk2 (mk2 (arg 1) (arg 2)) (arg 3)))
  (.letE (.call mg (mk2 (.arith .add (arg 0) (.length (arg 2))) (.var 1)))
  (.letE (.call mg (mk2 (.length (arg 2)) .nil))
    (.prim jpre (mk3 (arg 0) (.var 2) (.var 3)))))

def gmpListedKernelFuns (b jm jpre : ℕ) : List Expr :=
  [gmpListedKernelEntryF (b + 1) (b + 42) jpre] ++
    gmpGraphRowsFuns (b + 1) jm ++ mkGroupFuns (b + 42)

structure GmpListedKernelAt (P : Program) (hm : Membership) (hp : Preimage)
    (b jm jpre : ℕ) : Prop where
  entry : P.funs[b]? = some (gmpListedKernelEntryF (b + 1) (b + 42) jpre)
  graph : GmpGraphRowsAt P hm (b + 1) jm
  mg : P.HasAt (b + 42) (mkGroupFuns (b + 42))
  pre : P.prims[jpre]? = some (preimagePrim hp)

theorem gmpListedKernelAt_of {P : Program} {hm : Membership} {hp : Preimage} {b jm jpre : ℕ}
    (h : P.HasAt b (gmpListedKernelFuns b jm jpre))
    (hj : P.prims[jm]? = some (membershipPrim hm))
    (hpre : P.prims[jpre]? = some (preimagePrim hp)) : GmpListedKernelAt P hm hp b jm jpre :=
  ⟨(h.block 0 (gs := [gmpListedKernelEntryF (b + 1) (b + 42) jpre]) rfl).single,
    gmpGraphRowsAt_of (h.block 1 rfl) hj, h.block 42 rfl, hpre⟩

noncomputable def gmpListedKernelCost (hm : Membership) (hp : Preimage) (Y L S : ℕ) : ℕ :=
  let T := (S + 2) * (Y + L + 1)
  gmpGraphRowsCost hm (100 * Y) L S + mkGroupK * T ^ 3 +
    mkGroupK * (2 * (L + 1)) ^ 3 + tmPrimC (preimagePrim hp) (10000 * T ^ 2) +
      10 ^ 9 * T ^ 6

/-- The executable graph construction and preimage call compute the
kernel of conjugation on the enumerated right cosets. -/
theorem gmpListedKernel_spec {P : Program} {hm : Membership} {hp : Preimage} {b jm jpre n : ℕ}
    (ha : GmpListedKernelAt P hm hp b jm jpre)
    {H U V : Subgroup (Perm (Fin n))} {gv : Val} (hgv : GroupVal n gv V)
    {rs : List (Perm (Fin n))} (hrs : GmpCosetReps U V rs)
    (hU : GI.Multicoset.Normalizes H U) (hV : GI.Multicoset.Normalizes H V)
    (hs : List (Perm (Fin n))) (hhs : ∀ h ∈ hs, h ∈ H)
    {Y : ℕ} (hY : (n + 1) ^ 4 ≤ Y)
    (hin : (Val.list [.nat n, gv, .list (rs.map encPerm), .list (hs.map encPerm)]).wt ≤ Y) :
    FunAll P b (.list [.nat n, gv, .list (rs.map encPerm), .list (hs.map encPerm)])
      (fun w c => GensVal n w (GI.CitedChecks.preimageSubgroup
        (gmpGraphKernelInst H (gmpConjLabelAction hrs hU hV) hs hhs)) ∧
        c ≤ gmpListedKernelCost hm hp Y rs.length hs.length) := by
  let ds := hs.map (gmpGraphPerm H (gmpConjLabelAction hrs hU hV))
  let gs := ds.map sumToFin
  let I := gmpGraphKernelInst H (gmpConjLabelAction hrs hU hV) hs hhs
  let a := Val.list [.nat n, gv, .list (rs.map encPerm), .list (hs.map encPerm)]
  let T := (hs.length + 2) * (Y + rs.length + 1)
  have hn1 : n + 1 ≤ Y := (Nat.le_self_pow (by decide) (n + 1)).trans hY
  have hY1 : 1 ≤ Y := by omega
  have hv : gv.wt ≤ Y := (wt_le_wt_list (by simp) : gv.wt < a.wt).le.trans hin
  have hr : (Val.list (rs.map encPerm)).wt ≤ Y :=
    (wt_le_wt_list (by simp) : (Val.list (rs.map encPerm)).wt < a.wt).le.trans hin
  have hh : (Val.list (hs.map encPerm)).wt ≤ Y :=
    (wt_le_wt_list (by simp) : (Val.list (hs.map encPerm)).wt < a.wt).le.trans hin
  have hw2 := wt_list2_le gv (.list (rs.map encPerm))
  have hw3 := wt_list2_le (.list [gv, .list (rs.map encPerm)]) (.list (hs.map encPerm))
  have hgraph : (Val.list [.list [gv, .list (rs.map encPerm)], .list (hs.map encPerm)]).wt ≤ 100 * Y := by omega
  have hg := gmpGraphRows_spec ha.graph hgv hrs hU hV hs hhs
    (hY.trans (Nat.le_mul_of_pos_left _ (by decide))) hgraph
  have darg (rest : List Val) (j : Fin 4) := Det.arg' (P := P)
    (vs := [.nat n, gv, .list (rs.map encPerm), .list (hs.map encPerm)])
    (rest := rest) (j := j.val)
    (v := ([.nat n, gv, .list (rs.map encPerm), .list (hs.map encPerm)] : List Val)[j.val]'(by simpa using j.isLt))
    (by exact List.getElem?_eq_getElem (by simpa using j.isLt))
  have hg' : FunDet P (b + 1) (.list [.list [gv, .list (rs.map encPerm)], .list (hs.map encPerm)])
      (.list (gs.map encPerm)) (gmpGraphRowsCost hm (100 * Y) rs.length hs.length) := by
    simpa only [gs, ds, List.map_map, Function.comp_def] using hg
  have dg := Det.call (Det.mk2 (Det.mk2 (darg [] 1) (darg [] 2)) (darg [] 3)) hg'
  have dlen (rest : List Val) := Det.length (darg rest 2)
  simp only [List.length_map] at dlen
  have ddeg := Det.arith' (op := .add) (darg [.list (gs.map encPerm)] 0)
    (dlen [.list (gs.map encPerm)]) (z := n + rs.length) rfl
  have dgg := Det.call (Det.mk2 ddeg (Det.var' (P := P) (env := [a, .list (gs.map encPerm)]) (i := 1) rfl))
    (mkGroup_spec ha.mg gs)
  have de := Det.call (Det.mk2 (dlen [.list (gs.map encPerm), encGroup gs]) Det.nil)
    (mkGroup_spec ha.mg ([] : List (Perm (Fin rs.length))))
  have di := Det.mk3 (darg [.list (gs.map encPerm), encGroup gs, encGroup ([] : List (Perm (Fin rs.length)))] 0)
    (Det.var' (P := P) (env := [a, .list (gs.map encPerm), encGroup gs,
      encGroup ([] : List (Perm (Fin rs.length)))]) (i := 2) rfl)
    (Det.var' (P := P) (env := [a, .list (gs.map encPerm), encGroup gs,
      encGroup ([] : List (Perm (Fin rs.length)))]) (i := 3) rfl)
  have di' : Det P [a, .list (gs.map encPerm), encGroup gs, encGroup ([] : List (Perm (Fin rs.length)))]
      (mk3 (arg 0) (.var 2) (.var 3)) (preimageEnc I) _ := di
  have dp := preimage_call hp I ha.pre di'
  refine FunAll.intro ha.entry (EvalAll.letE dg fun w c hw => ?_)
  obtain ⟨rfl, cg⟩ := hw
  refine EvalAll.letE dgg fun w c hw => ?_
  obtain ⟨rfl, cgg⟩ := hw
  refine EvalAll.letE de fun w c hw => ?_
  obtain ⟨rfl, ce⟩ := hw
  refine dp.mono fun w c ⟨hw, hc⟩ => ⟨hw, ?_⟩
  have hww : w.wt ≤ 13 * (n + 1) ^ 6 := GensVal.wt_le hw
  have hgslen : gs.length = hs.length := by simp [gs, ds]
  have hdeg : n + rs.length + 1 ≤ Y + rs.length + 1 := by omega
  have hT1 : 1 ≤ T := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  have hYT : Y ≤ T := by
    have := Nat.le_mul_of_pos_left (Y + rs.length + 1) (by omega : 0 < hs.length + 2)
    dsimp [T]; omega
  have hLT : rs.length + 1 ≤ T := by
    have := Nat.le_mul_of_pos_left (Y + rs.length + 1) (by omega : 0 < hs.length + 2)
    dsimp [T]; omega
  have hST : hs.length + 2 ≤ T := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hwtg : (encGroup gs).wt ≤ 200 * T ^ 2 := by
    have hw := wt_encGroup_le gs
    rw [hgslen] at hw
    have ht : (hs.length + 2) * (n + rs.length + 1) ≤ T := Nat.mul_le_mul_left _ hdeg
    have hb := Nat.mul_le_mul_left 40 (Nat.pow_le_pow_left ht 2)
    exact hw.trans (hb.trans (by omega))
  have hwte : (encGroup ([] : List (Perm (Fin rs.length)))).wt ≤ 200 * T ^ 2 := by
    have hw := wt_encGroup_le ([] : List (Perm (Fin rs.length)))
    simp only [List.length_nil] at hw
    calc
      (encGroup ([] : List (Perm (Fin rs.length)))).wt ≤ 40 * (2 * (rs.length + 1)) ^ 2 := hw
      _ ≤ 40 * (2 * T) ^ 2 := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 hLT) 2)
      _ = 160 * T ^ 2 := by ring
      _ ≤ 200 * T ^ 2 := by omega
  have hwtgs : (Val.list (gs.map encPerm)).wt ≤ 200 * T ^ 2 := by
    have ht : (gs.length + 1) * (n + rs.length + 1) ≤ T := by
      rw [hgslen]
      exact Nat.mul_le_mul (by omega) hdeg
    have hb := (wt_list_encPerms_le gs).trans (Nat.mul_le_mul_left 13 (Nat.pow_le_pow_left ht 2))
    omega
  have wn : (Val.nat n).wt ≤ T + 2 := (wt_nat_le n).trans (by omega)
  have hprewt : (preimageEnc I).wt ≤ 10000 * T ^ 2 := by
    have hw := wt_list3_le (.nat n) (encGroup gs) (encGroup ([] : List (Perm (Fin rs.length))))
    change (Val.list [.nat n, encGroup gs, encGroup ([] : List (Perm (Fin rs.length)))]).wt ≤ _
    have hxx : T ≤ T ^ 2 := Nat.le_self_pow (by decide) T
    omega
  have hpre := (preimagePrim hp).bound_le ((preimageEnc I).size_le_wt.trans hprewt)
  have hpre' : (preimagePrim hp).boundSize (10000 * T ^ 2) = tmPrimC (preimagePrim hp) (10000 * T ^ 2) := rfl
  rw [hpre'] at hpre
  have hmkg : mkGroupK * ((gs.length + 2) * (n + rs.length + 1)) ^ 3 ≤ mkGroupK * T ^ 3 := by
    rw [hgslen]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ hdeg) 3)
  have heq : (Val.list [.nat n, gv, .list (rs.map encPerm), .list (hs.map encPerm)]).wt = a.wt := rfl
  have w0 := wt_list2_le (.nat (n + rs.length)) (.list (gs.map encPerm))
  have w1 := wt_list2_le (.nat rs.length) (.list [])
  have w2 := wt_nat_le (n + rs.length)
  have w3 := wt_nat_le rs.length
  have wnil : (Val.list []).wt = 4 := rfl
  have htw : (Val.nat (n + rs.length)).wt ≤ T + 2 := w2.trans (by
    have := Nat.le_mul_of_pos_left (Y + rs.length + 1) (by omega : 0 < hs.length + 2)
    dsimp [T] at *; omega)
  have htl : (Val.nat rs.length).wt ≤ T + 2 := w3.trans (by omega)
  have htx : T ≤ T ^ 6 := Nat.le_self_pow (by decide) T
  have ht2 : T ^ 2 ≤ T ^ 6 := Nat.pow_le_pow_right hT1 (by decide)
  have hn6 : (n + 1) ^ 6 ≤ T ^ 6 := Nat.pow_le_pow_left (hn1.trans hYT) 6
  simp only [List.length_nil, zero_add] at ce
  unfold gmpListedKernelCost
  change _ ≤ gmpGraphRowsCost hm (100 * Y) rs.length hs.length + mkGroupK * T ^ 3 +
    mkGroupK * (2 * (rs.length + 1)) ^ 3 + tmPrimC (preimagePrim hp) (10000 * T ^ 2) + 10 ^ 9 * T ^ 6
  have hIn : (I.n + 1) ^ 6 = (n + 1) ^ 6 := rfl
  have hep : (preimageEnc I).wt =
      (Val.list [.nat n, encGroup gs, encGroup ([] : List (Perm (Fin rs.length)))]).wt := rfl
  have wr2 : (Val.list [
      ([.nat n, gv, .list (rs.map encPerm), .list (hs.map encPerm)] : List Val)[(1 : Fin 4).val]'(by change 1 < 4; decide),
      ([.nat n, gv, .list (rs.map encPerm), .list (hs.map encPerm)] : List Val)[(2 : Fin 4).val]'(by change 2 < 4; decide)]).wt ≤ 100 * Y := hw2.trans (by omega)
  have wr3 : (Val.list [.list [
      ([.nat n, gv, .list (rs.map encPerm), .list (hs.map encPerm)] : List Val)[(1 : Fin 4).val]'(by change 1 < 4; decide),
      ([.nat n, gv, .list (rs.map encPerm), .list (hs.map encPerm)] : List Val)[(2 : Fin 4).val]'(by change 2 < 4; decide)],
      ([.nat n, gv, .list (rs.map encPerm), .list (hs.map encPerm)] : List Val)[(3 : Fin 4).val]'(by change 3 < 4; decide)]).wt ≤ 100 * Y := hgraph
  have wrp : (Val.list [
      ([.nat n, gv, .list (rs.map encPerm), .list (hs.map encPerm)] : List Val)[(0 : Fin 4).val]'(by change 0 < 4; decide),
      encGroup gs, encGroup ([] : List (Perm (Fin rs.length)))]).wt ≤ 10000 * T ^ 2 := hprewt
  omega

theorem gmpListedKernelCost_poly (hm : Membership) (hp : Preimage) :
    PBU (fun L Y S => gmpListedKernelCost hm hp Y L S) := by
  have hT := (PBU.B.addc 2).mul ((PBU.W.add PBU.k).addc 1)
  have hg := gmpPBU_comp (gmpGraphRowsCost_poly hm) PBU.k (PBU.W.smul 100) PBU.B
  exact (((hg.add ((hT.pow 3).smul mkGroupK)).add
    ((((PBU.k.addc 1).smul 2).pow 3).smul mkGroupK)).add
      (((((hT.pow 2).smul 10000).addc 2).pow (preimagePrim hp).k).smul (preimagePrim hp).c)).add
        ((hT.pow 6).smul (10 ^ 9))

end GI.Impl
