module

public import Workspace.Impl.LinIntBasis
public import Workspace.Impl.LinCoordinateSlp

@[expose] public section

/-! Append the first i unit exponent vectors to an already encoded table. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linAssignUnitStep (basis : ℕ) : Expr :=
  .snoc (arg 2) (.call basis (mk3 (arg 1) linIntOneE (.get (arg 0) (.nat 0))))

def linAssignUnitFuns (b basis : ℕ) : List Expr :=
  loopFuns b (arg 1) (arg 2) (linAssignUnitStep basis)

def linAssignUnitBasisArg (W t : ℕ) : ℕ := 10 * (W + t + 100)
def linAssignUnitBasisCost (W t : ℕ) : ℕ := linBasisCost (linAssignUnitBasisArg W t) t
def linAssignUnitAccWt (W t : ℕ) : ℕ := linVectorAccWt (W + t) (W + linAssignUnitBasisCost W t)
def linAssignUnitStepCost (W t : ℕ) : ℕ :=
  1000 * (W + t + linAssignUnitBasisCost W t + linAssignUnitAccWt W t + 1)
def linAssignUnitCost (W t i : ℕ) : ℕ :=
  i * linAssignUnitStepCost W t + loopModK * (i + 1) * (W + i + linAssignUnitAccWt W t + 1)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
theorem linAssignUnit_spec {P : Program} {b basis t : ℕ}
    (hp : P.HasAt b (linAssignUnitFuns b basis)) (hb : P.HasAt basis (linBasisFuns basis))
    (i : ℕ) (hi : i ≤ t) (xs : List Val) :
    FunDet P b (.list [.nat t, .nat i, .list xs])
      (.list (xs ++ (((List.finRange t).take i).map fun j => linVecVal (Pi.single j (1 : ℤ)))))
      (linAssignUnitCost (Val.list [.nat t, .nat i, .list xs]).wt t i) := by
  let a := Val.list [.nat t, .nat i, .list xs]
  let W := a.wt
  let M := linAssignUnitAccWt W t
  let us := (List.finRange t).map fun j => linVecVal (Pi.single j (1 : ℤ))
  have wx : (Val.list xs).wt < W := wt_le_wt_list (by simp)
  have wlen : xs.length < W := (length_lt_wt_list xs).trans wx
  have wt : (Val.nat t).wt < W := wt_le_wt_list (by simp)
  have basisSpec (j : Fin t) : FunDet P basis (.list [.nat j.val, encInt 1, .nat t])
      (linVecVal (Pi.single j (1 : ℤ))) (linAssignUnitBasisCost W t) := by
    have wa := wt_list3_le (.nat j.val) (encInt 1) (.nat t)
    have wj := wt_nat_le j.val
    have wn : (encInt 1).wt ≤ 100 := by decide
    have hj := j.isLt
    have win : (Val.list [.nat j.val, encInt 1, .nat t]).wt ≤ linAssignUnitBasisArg W t := by
      unfold linAssignUnitBasisArg
      omega
    exact (linBasis_spec hb j 1).mono (by
      unfold linAssignUnitBasisCost linBasisCost
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3))
  have wacc (k : ℕ) (hk : k ≤ i) : (Val.list (xs ++ us.take k)).wt ≤ M := by
    have hmem : ∀ v ∈ xs ++ us.take k, v.wt ≤ W + linAssignUnitBasisCost W t := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact (wt_le_wt_list hv).le.trans wx.le |>.trans (by omega)
      · obtain ⟨j, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hv)
        exact (basisSpec j).wt_lt.le.trans (by omega)
    have hh := linWtList hmem
    have hl : (xs ++ us.take k).length ≤ W + t := by
      simp only [List.length_append, List.length_take]
      omega
    have hm := Nat.mul_le_mul_right (W + linAssignUnitBasisCost W t) hl
    unfold M linAssignUnitAccWt linVectorAccWt
    omega
  have di := Det.arg' (P := P) (vs := [.nat t, .nat i, .list xs]) (rest := []) (j := 1) rfl
  have dx := Det.arg' (P := P) (vs := [.nat t, .nat i, .list xs]) (rest := []) (j := 2) rfl
  have hloop := loopBdd_spec hp di dx (by
    have := a.two_le_size
    have := a.size_le_wt
    simp only [a, W] at *
    omega)
    (Inv := fun k acc => acc = .list (xs ++ us.take k)) (M := M)
    (D := fun _ => linAssignUnitStepCost W t) (by simp)
    (fun k acc hk he => he ▸ wacc k hk) (fun k acc hk he => ?_)
  · refine hloop.mono fun out cost ho => ⟨?_, ?_⟩
    · simpa only [us, ← List.map_take] using ho.1
    · simpa only [Finset.sum_const, Finset.card_range, smul_eq_mul, linAssignUnitCost] using ho.2
  · subst acc
    let j : Fin t := ⟨k, hk.trans_le hi⟩
    have dctx := Det.arg' (P := P) (vs := [a, .nat k, .list (xs ++ us.take k)]) (rest := []) (j := 0) rfl
    have dt := Det.get' dctx (Det.nat 0) rfl
    have dk := Det.arg' (P := P) (vs := [a, .nat k, .list (xs ++ us.take k)]) (rest := []) (j := 1) rfl
    have done : Det P [.list [a, .nat k, .list (xs ++ us.take k)]] linIntOneE (encInt 1) _ :=
      Det.mk2 (Det.nat 0) (Det.mk1 (Det.nat 1))
    have dc := Det.call (Det.mk3 dk done dt) (basisSpec j)
    have da := Det.arg' (P := P) (vs := [a, .nat k, .list (xs ++ us.take k)]) (rest := []) (j := 2) rfl
    have dn := Det.snoc da dc
    have htake : us.take (k + 1) = us.take k ++ [linVecVal (Pi.single j (1 : ℤ))] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by simp [us]; omega)]
      simp only [us, List.getElem_map, Option.toList_some]
      congr 3
      rw [List.getElem_finRange]
      congr 1
    refine dn.post fun cost hc => ⟨?_, ?_⟩
    · rw [htake, List.append_assoc]
    · have wn := wt_nat_le k
      have wa := wt_list3_le a (.nat k) (.list (xs ++ us.take k))
      have wcur := wacc k hk.le
      have wnext := wacc (k + 1) (by omega)
      rw [htake, ← List.append_assoc] at wnext
      have wb := (basisSpec j).wt_lt.le
      have warg := wt_list3_le (.nat k) (encInt 1) (.nat t)
      have w1 : (encInt 1).wt ≤ 100 := by decide
      have w0 : (Val.nat 0).wt = 2 := rfl
      have wnat1 : (Val.nat 1).wt = 3 := rfl
      have wnil : (Val.list []).wt = 4 := rfl
      have wone : (Val.list [.nat 1]).wt ≤ 20 := by decide
      change cost ≤ linAssignUnitStepCost W t + 100 * (W + i + M + 1)
      unfold linAssignUnitStepCost
      simp only [j, W, a] at *
      norm_num [encInt, Nat.bits] at *
      omega

end GI.Impl
