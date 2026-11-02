import Workspace.Impl.LinPrimaryTransport
import Workspace.Lang.Lib.NatList

/-! The numeric number of primary levels is bounded by the bit weight of the
stored cyclic orders. Compute it by a bounded list maximum. -/
namespace GI.Impl
open GI.Cited GI.Lang

theorem linPrimaryExponent_lt (p j : ℕ) (hp : 2 ≤ p) : j < (encInt (p ^ j : ℤ)).wt := by
  have ha := linEncIntAbs (p ^ j : ℤ)
  simp only [Int.natAbs_pow, Int.natAbs_natCast] at ha
  have hlo : 2 ^ j ≤ p ^ j := Nat.pow_le_pow_left hp _
  by_contra hh
  have he : 2 ^ (encInt (p ^ j : ℤ)).wt ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem linPrimaryExponent_moduli_lt {p d : ℕ} (hp : p.Prime) (ν : Fin d → ℕ) (i : Fin d) :
    ν i < (linVecVal (linFiniteModuli (linPrimaryOrders p ν))).wt := by
  have hh := linVecEntryWt (linFiniteModuli (linPrimaryOrders p ν)) i.castSucc
  simp only [linFiniteModuli, linExtend_castSucc, linPrimaryOrders] at hh
  exact (linPrimaryExponent_lt p (ν i) hp.two_le).trans hh

def linPrimaryHeight {d : ℕ} (ν : Fin d → ℕ) : ℕ := ((List.finRange d).map ν).foldl max 0

theorem linPrimaryHeight_le {p d : ℕ} (hp : p.Prime) (ν : Fin d → ℕ) :
    linPrimaryHeight ν ≤ (linVecVal (linFiniteModuli (linPrimaryOrders p ν))).wt := by
  apply foldl_max_le (Nat.zero_le _)
  intro v hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
  exact (linPrimaryExponent_moduli_lt hp ν i).le

theorem linPrimaryHeight_ge {d : ℕ} (ν : Fin d → ℕ) (i : Fin d) : ν i ≤ linPrimaryHeight ν :=
  (le_foldl_max ((List.finRange d).map ν) 0).2 (ν i) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

def linPrimaryHeightF (max : ℕ) : Expr := .call max (arg 0)
def linPrimaryHeightFuns (b : ℕ) : List Expr := [linPrimaryHeightF (b + 1)] ++ maxFuns (b + 1)

theorem linPrimaryHeightFuns_length (b : ℕ) : (linPrimaryHeightFuns b).length = 6 := rfl

def linPrimaryHeightCost (W : ℕ) : ℕ := 10000 * (W + maxK * (W + 1) ^ 3 + 1)

set_option maxHeartbeats 1000000 in
theorem linPrimaryHeight_spec {P : Program} {b p d : ℕ} (h : P.HasAt b (linPrimaryHeightFuns b))
    (hp : p.Prime) (ν : Fin d → ℕ) :
    FunDet P b (.list [encFun ν, linVecVal (linFiniteModuli (linPrimaryOrders p ν))])
      (.nat (linPrimaryHeight ν))
      (linPrimaryHeightCost (Val.list [encFun ν, linVecVal (linFiniteModuli (linPrimaryOrders p ν))]).wt) := by
  let orders := linVecVal (linFiniteModuli (linPrimaryOrders p ν))
  let a := Val.list [encFun ν, orders]
  let W := a.wt
  have wo : orders.wt < W := wt_le_wt_list (by simp [W, a])
  have wν : (encFun ν).wt < W := wt_le_wt_list (by simp [W, a])
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => Val.nat (ν i))
    simp only [List.length_map, List.length_finRange] at hh
    change d < (encFun ν).wt at hh
    omega
  have hm := max_spec (h.block 1 rfl) (xs := (List.finRange d).map ν) (B := W) (by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    exact (linPrimaryExponent_moduli_lt hp ν i).le.trans wo.le) (by simpa using hd)
  simp only [natList, List.map_map, Function.comp_def] at hm
  have dn := Det.arg' (P := P) (vs := [encFun ν, orders]) (rest := []) (j := 0) rfl
  have dd := Det.call dn hm
  apply FunDet.intro ((h.block (gs := [linPrimaryHeightF (b + 1)]) 0 rfl).single)
  refine dd.mono ?_
  have wh := hm.wt_lt.le
  change _ ≤ linPrimaryHeightCost W
  unfold linPrimaryHeightCost
  dsimp only [W, a, orders, natList, encFun] at *
  omega

theorem linPrimaryHeightCost_poly : PBU (fun _ W _ => linPrimaryHeightCost W) := by
  unfold linPrimaryHeightCost
  norm_poly

end GI.Impl
