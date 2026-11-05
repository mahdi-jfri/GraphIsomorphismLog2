module

public import Workspace.Impl.LinWreathInputCost

@[expose] public section

/-! Compose the already verified table constructors. This lemma records only
ordinary function specifications; it introduces no task or oracle hypothesis. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linWreathInputComposeCost (W n d Ct Cp Cg Cm Cv : ℕ) : ℕ :=
  100000 * (W + n + d + Ct + Cp + Cg + Cm + Cv + 1)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 6000 in
theorem linWreathInputCompose_spec {P : Program} {b n Ct Cp Cg Cm Cv : ℕ}
    (h : linWreathInputAt P b) (id pv ms perms group mats vec : Val) (gs vs ws : List Val)
    (ht : FunDet P (b + 1) (.list (id :: gs)) (.list gs) Ct)
    (hp : FunDet P (b + 4) (.list [id, .list gs]) perms Cp)
    (hg : FunDet P (b + 32) (.list [.nat (n + n), perms]) group Cg)
    (hm : FunDet P (b + 39) (.list [ms, .nat vs.length]) mats Cm)
    (hv : FunDet P (b + 68) (.list [.list vs, .list ws]) vec Cv) :
    let src := Val.list [.list [.nat n, .list (id :: gs)], pv, ms, .list vs]
    let a := Val.list [src, .list ws]
    FunDet P b a (.list [group, pv, mats, vec])
      (linWreathInputComposeCost a.wt n vs.length Ct Cp Cg Cm Cv) := by
  let src := Val.list [.list [.nat n, .list (id :: gs)], pv, ms, .list vs]
  let a := Val.list [src, .list ws]
  let W := a.wt
  let S := W + n + vs.length + Ct + Cp + Cg + Cm + Cv + 1
  let T := 100 * S
  have hT : W + n + vs.length + Ct + Cp + Cg + Cm + Cv + 10 ≤ T := by dsimp [T, S]; omega
  have wsrc : src.wt < W := wt_le_wt_list (by simp [W, a])
  have wws : (Val.list ws).wt < W := wt_le_wt_list (by simp [W, a])
  have wH : (Val.list [.nat n, .list (id :: gs)]).wt < src.wt := wt_le_wt_list (by simp [src])
  have wpv : pv.wt < src.wt := wt_le_wt_list (by simp [src])
  have wms : ms.wt < src.wt := wt_le_wt_list (by simp [src])
  have wvs : (Val.list vs).wt < src.wt := wt_le_wt_list (by simp [src])
  have wraw : (Val.list (id :: gs)).wt < (Val.list [.nat n, .list (id :: gs)]).wt :=
    wt_le_wt_list (by simp)
  have wn : (Val.nat n).wt < (Val.list [.nat n, .list (id :: gs)]).wt := wt_le_wt_list (by simp)
  have wid : id.wt < (Val.list (id :: gs)).wt := wt_le_wt_list (by simp)
  have wgs : (Val.list gs).wt ≤ (Val.list (id :: gs)).wt :=
    wt_list_sublist (List.sublist_cons_self _ _)
  have wperms := hp.wt_lt.le
  have wgroup := hg.wt_lt.le
  have wmats := hm.wt_lt.le
  have wvec := hv.wt_lt.le
  have wout : (Val.list [group, pv, mats, vec]).wt ≤ T := by
    have hh := wt_list4_le group pv mats vec
    omega
  have wparg : (Val.list [id, .list gs]).wt ≤ T := by
    have hh := wt_list2_le id (.list gs)
    omega
  have wgarg : (Val.list [.nat (n + n), perms]).wt ≤ T := by
    have hh := wt_list2_le (.nat (n + n)) perms
    have ww := wt_nat_le (n + n)
    omega
  have wmarg : (Val.list [ms, .nat vs.length]).wt ≤ T := by
    have hh := wt_list2_le ms (.nat vs.length)
    have ww := wt_nat_le vs.length
    omega
  have wvarg : (Val.list [.list vs, .list ws]).wt ≤ T := by
    have hh := wt_list2_le (.list vs) (.list ws)
    omega
  have dsrc (rest : List Val) := StDC.arg (P := P) (vs := [src, .list ws]) (rest := rest)
    (j := 0) rfl (show a.wt ≤ T by change W ≤ T; omega) (by omega) (show src.wt ≤ T by omega)
  have dH (rest : List Val) := StDC.get (dsrc rest) (StDC.nat 0 (by omega)) rfl
    (show (Val.list [.nat n, .list (id :: gs)]).wt ≤ T by omega)
  have draw (rest : List Val) := StDC.get (dH rest) (StDC.nat 1 (by omega)) rfl
    (show (Val.list (id :: gs)).wt ≤ T by omega)
  have did (rest : List Val) := StDC.get (draw rest) (StDC.nat 0 (by omega)) rfl
    (show id.wt ≤ T by omega)
  have dn (rest : List Val) := StDC.get (dH rest) (StDC.nat 0 (by omega)) rfl
    (show (Val.nat n).wt ≤ T by omega)
  have dp (rest : List Val) := StDC.get (dsrc rest) (StDC.nat 1 (by omega)) rfl
    (show pv.wt ≤ T by omega)
  have dms (rest : List Val) := StDC.get (dsrc rest) (StDC.nat 2 (by omega)) rfl
    (show ms.wt ≤ T by omega)
  have dvs (rest : List Val) := StDC.get (dsrc rest) (StDC.nat 3 (by omega)) rfl
    (show (Val.list vs).wt ≤ T by omega)
  have dws (rest : List Val) := StDC.arg (P := P) (vs := [src, .list ws]) (rest := rest)
    (j := 1) rfl (show a.wt ≤ T by change W ≤ T; omega) (by omega)
    (show (Val.list ws).wt ≤ T by omega)
  have dt := StDC.call (draw []) ht (show (Val.list gs).wt ≤ T by omega)
  have dperms := StDC.call (StDC.mk2 (did [.list gs])
    (StDC.var' (P := P) (env := [a, .list gs]) (i := 1) rfl (by omega)) wparg (by omega)) hp (by omega : perms.wt ≤ T)
  have dgroup := StDC.call (StDC.mk2
    (StDC.arith (op := .add) (dn [.list gs, perms]) (dn [.list gs, perms]) rfl
      ((wt_nat_le (n + n)).trans (by omega)))
    (StDC.var' (P := P) (env := [a, .list gs, perms]) (i := 2) rfl (by omega)) wgarg (by omega)) hg
    (by omega : group.wt ≤ T)
  have dmats := StDC.call (StDC.mk2 (dms [.list gs, perms, group])
    (StDC.length (dvs [.list gs, perms, group]) (by omega)) wmarg (by omega)) hm
    (by omega : mats.wt ≤ T)
  have dvec := StDC.call (StDC.mk2 (dvs [.list gs, perms, group, mats])
    (dws [.list gs, perms, group, mats]) wvarg (by omega)) hv (by omega : vec.wt ≤ T)
  have dout := StDC.mk4
    (StDC.var' (P := P) (env := [a, .list gs, perms, group, mats, vec]) (i := 3) rfl (by omega))
    (dp [.list gs, perms, group, mats, vec])
    (StDC.var' (P := P) (env := [a, .list gs, perms, group, mats, vec]) (i := 4) rfl (by omega))
    (StDC.var' (P := P) (env := [a, .list gs, perms, group, mats, vec]) (i := 5) rfl (by omega))
    wout (by omega)
  have db := StDC.letE dt (StDC.letE dperms (StDC.letE dgroup
    (StDC.letE dmats (StDC.letE dvec dout wout) wout) wout) wout) wout
  apply FunDet.intro h.entry
  refine db.det.mono ?_
  change _ ≤ linWreathInputComposeCost W n vs.length Ct Cp Cg Cm Cv
  dsimp only [linWreathInputComposeCost]
  norm_num only [Nat.reduceAdd, Nat.add_zero, Nat.zero_add]
  dsimp only [T, S]
  omega

end GI.Impl
