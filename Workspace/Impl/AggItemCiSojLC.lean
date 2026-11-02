import Workspace.Impl.AggItemHvLift
import Workspace.Impl.RowKer
import Workspace.Impl.GenNormPoly
import Workspace.Impl.AggItemCiSojWt

/-!
# Constructing the stored context for physical-to-label projection

Swap the representation graph and construct the existing lift context with its
two degrees exchanged. All group-context construction uses the established
`it_hvLc_spec` program; no new group algorithm is introduced.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val)

variable {k q : ℕ}

/-- On `[[k,q], graph pairs]`, construct the lift context of the swapped graph. -/
def itcsSwapLcF (sw lc : ℕ) : Expr :=
  .letE (.call sw (mk2 (.nat 0) (arg 1)))
    (.call lc (mk2 (mk2 (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 0))) (.var 1)))

/-- Common budget including the existing context constructor's output. -/
def itcsSwapLcW (M : ℕ) : ℕ := 1000 * (itHvLcC M + M ^ 3 + 10)

/-- Cost of swapping and constructing the graph context. -/
def itcsSwapLcC (M : ℕ) : ℕ :=
  100 * (itcsSwapLcW M + 1) + swapMapK * (1000 * M ^ 3) ^ 2 + itHvLcC M

/-- Every installed callee and intermediate weight is accounted for. -/
theorem itcs_swap_lc_spec {Pg : Program} {f sw lc rng gr fm en mk : ℕ}
    (hf : Pg.funs[f]? = some (itcsSwapLcF sw lc)) (hsw : Pg.HasAt sw (swapMapFuns sw))
    (hlc : Pg.funs[lc]? = some (itHvLcF rng gr fm)) (hr : Pg.HasAt rng (rangeFuns rng))
    (hg : Pg.funs[gr]? = some (grpF en mk)) (he : Pg.HasAt en (pEncMapFuns en))
    (hm : Pg.HasAt mk (mkGroupFuns mk)) (hfm : Pg.HasAt fm (fstMapFuns fm))
    (ps : List (Perm (Fin k) × Perm (Fin q))) :
    FunDet Pg f (.list [.list [.nat k, .nat q], .list (ps.map pairV)])
      (liftLabCtx q k (ps.map Prod.swap)) (itcsSwapLcC (pM k q ps)) := by
  let M := pM k q ps
  let Bw := itcsSwapLcW M
  have hM : k + q + ps.length + 2 = M := rfl
  have h1 : 1 ≤ M := by omega
  have hpow : M ≤ M ^ 3 := Nat.le_self_pow (by omega) _
  have budget : 100 * itHvLcC M + 1000 * M ^ 3 + 1000 ≤ Bw := by
    dsimp only [Bw]; unfold itcsSwapLcW; omega
  have wps : (Val.list (ps.map pairV)).wt ≤ 50 * M ^ 3 := wt_pairList_le ps
  have wsw : (Val.list ((ps.map Prod.swap).map pairV)).wt ≤ 50 * M ^ 3 := by rw [wt_pairList_swap]; exact wps
  have wk := wt_nat_le k
  have wq := wt_nat_le q
  have wd := wt_list2_le (.nat k) (.nat q)
  have wd' := wt_list2_le (.nat q) (.nat k)
  have wi : (Val.list [.list [.nat k, .nat q], .list (ps.map pairV)]).wt ≤ Bw := by
    have h := wt_list2_le (.list [.nat k, .nat q]) (.list (ps.map pairV))
    omega
  have wsi : (Val.list [.nat 0, .list (ps.map pairV)]).wt + 1 ≤ 1000 * M ^ 3 := by
    have h := wt_list2_le (.nat 0) (.list (ps.map pairV))
    have hz := wt_nat_le 0
    omega
  have wci : (Val.list [.list [.nat q, .nat k], .list ((ps.map Prod.swap).map pairV)]).wt ≤ Bw := by
    have h := wt_list2_le (.list [.nat q, .nat k]) (.list ((ps.map Prod.swap).map pairV))
    omega
  have hcost : pM q k (ps.map Prod.swap) = M := by simp only [pM, List.length_map, M]; omega
  have callLC := it_hvLc_spec hlc hr hg he hm hfm (ps.map Prod.swap)
  rw [hcost] at callLC
  have wout : (liftLabCtx q k (ps.map Prod.swap)).wt ≤ Bw := (itcs_det_weight callLC).trans (by omega)
  have get {rest : List Val} {i : ℕ} {w : Val}
      (hi : [Val.list [.nat k, .nat q], .list (ps.map pairV)][i]? = some w) (hii : i + 2 ≤ Bw) :
      StDC Pg (.list [.list [.nat k, .nat q], .list (ps.map pairV)] :: rest) (arg i) w 3 0 Bw :=
    StDC.arg hi wi hii ((st_wt_mem (List.mem_of_getElem? hi)).trans wi)
  have swcall := StDC.call (StDC.mk2 (StDC.nat 0 (by omega)) (get (rest := []) (i := 1) rfl (by omega))
    (by omega) (by omega)) (swapMap_spec hsw (.nat 0) ps) (wsw.trans (by omega))
  let env : List Val := [.list [.list [.nat k, .nat q], .list (ps.map pairV)],
      .list ((ps.map Prod.swap).map pairV)]
  have dim := get (rest := [.list ((ps.map Prod.swap).map pairV)]) (i := 0) rfl (by omega)
  have qv := StDC.get dim (StDC.nat 1 (by omega)) rfl (wq.trans (by omega))
  have kv := StDC.get dim (StDC.nat 0 (by omega)) rfl (wk.trans (by omega))
  have pair := StDC.mk2 qv kv (by omega) (by omega)
  have s1 : StDC Pg env (.var 1) (.list ((ps.map Prod.swap).map pairV)) 1 0 Bw := StDC.var' rfl (wsw.trans (by omega))
  have res := StDC.call (StDC.mk2 pair s1 wci (by omega)) callLC wout
  have body := StDC.letE swcall res wout
  have hsc := Nat.mul_le_mul_left swapMapK (Nat.pow_le_pow_left wsi 2)
  clear budget wps wsw wk wq wd wd' wi wsi wci callLC wout get swcall dim qv kv pair s1 res
  exact StDC.funDet hf body (by unfold itcsSwapLcC; dsimp only [Bw, M] at *; omega)

/-- Polynomial context-building cost when generator length is bounded by the square degree. -/
theorem itcs_swap_lc_pbu : PBU fun _ W _ => itcsSwapLcC (W + (2 * W + 3) + W ^ 2 + 2) := by
  simp only [itcsSwapLcC, itcsSwapLcW, itHvLcC, swapMapK]
  norm_poly

end GI.Impl
