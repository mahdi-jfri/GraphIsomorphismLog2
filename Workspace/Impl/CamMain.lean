module

public import Workspace.Impl.CamProgTail

@[expose] public section

/-!
# The main function of `camProg`

`camMain_spec`: on `encGroup gs` for a primitive group `⟨gs⟩` of degree `n ≥ 25`, the main function
answers as `CameronOut` requires. It asks `GroupOrder` for `|G|` (the input is a group, the
precondition of the call). If `|G| < n^(1 + ⌊log₂ n⌋)` it answers `[0]`. Otherwise Maróti's theorem
gives an identification `e` with `m ≥ 5`, `1 ≤ k` and `2k < m` (`cam_normal_form`), and the tail
does the rest (`camTail_spec`).
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv
open GI.Machine (BinOp len len_le_self)

variable {n : ℕ}

/-- The cost bound of the main function. -/
noncomputable def camMainCost (ho : GroupOrder) (hp : PointwiseStab) (hncl : NormalClosure)
    (hd : DerivedSubgroup) (hqc : GMPNormalCentralizer)
    (hj : JohnsonIdentification) (X : ℕ) : ℕ :=
  5 * camTailCost ho hp hncl hd hqc hj X + camS4 ho hp hncl hd hqc hj X + 10 ^ 10 * X ^ 4

/-- The cost of the order test. -/
theorem cam_test_cost {X o c t a : ℕ} (ht : t ≤ 3) (ha : a ≤ X) (hX : 26 ≤ X) (hn2 : n ^ 2 ≤ X ^ 2) (hnX : n + 1 ≤ X)
    (ho : (Val.nat o).wt ≤ n ^ 2 + 3)
    (hc : c ≤ (Val.nat o).wt + 1 + (a + 3 + (Val.nat n).wt + 1) +
      2 * (Val.list [.nat o, .nat n]).wt + 7 +
      camSmallK * ((Val.list [.nat o, .nat n]).wt + 2 * n + 11) ^ 2 + t + 1) :
    c ≤ 10 ^ 9 * X ^ 4 := by
  have w1 := wt_nat_le n
  have w2 := wt_list2_le (.nat o) (.nat n)
  have hin : (Val.list [.nat o, .nat n]).wt + 2 * n + 11 ≤ 10 * X ^ 2 := by
    have : X ≤ X ^ 2 := by nlinarith
    omega
  have hsq := Nat.pow_le_pow_left hin 2
  have e : (10 * X ^ 2) ^ 2 = 100 * X ^ 4 := by ring
  rw [e] at hsq
  have kk := Nat.mul_le_mul_left camSmallK hsq
  have h24 : X ^ 2 ≤ X ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h14 : X ≤ X ^ 2 := by nlinarith
  clear * - hc w1 w2 hin kk h24 h14 ho hn2 hnX ht ha
  simp only [camSmallK] at *
  omega

/-- **The main function.** -/
theorem camMain_spec (hMa : MarotiPrimitive) {ho : GroupOrder} {hp : PointwiseStab}
    {hncl : NormalClosure} {hd : DerivedSubgroup}
    {hqc : GMPNormalCentralizer} {hj : JohnsonIdentification}
    {P : Program} {b jo jp jn jd jq jj : ℕ}
    (hP : CamAt P b jo jp jn jd jq jj ho hp hncl hd hqc hj) (gs : List (Perm (Fin n))) (hn : 25 ≤ n)
    (hprim : MulAction.IsPreprimitive (gens gs) (Fin n)) :
    FunAll P b (encGroup gs) (fun v c => CameronOut (gens gs) v ∧
      c ≤ camMainCost ho hp hncl hd hqc hj ((encGroup gs).wt + 1)) := by
  set x := encGroup gs with hx
  set X := x.wt + 1 with hX
  have hxS : (gs.length + 2) * (n + 1) ≤ x.wt := S_le_wt_encGroup gs
  have hnX : n + 1 ≤ X := by
    have : n + 1 ≤ (gs.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hX26 : 26 ≤ X := by omega
  have hn2 : n ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hX12 : X ≤ X ^ 12 := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ X ^ 12 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hxw : (encGroup gs).wt + 1 = X := by rw [hX]
  clear_value X
  have dx : Det P [x] (.var 0) x (x.wt + 1) := Det.var' rfl
  -- step 1: the order of `G`; the input is a group, as the call needs
  refine FunAll.intro hP.main (EvalAll.letE (groupOrder_call ho hP.po dx ⟨gs, rfl, rfl⟩)
    fun vo co hO => ?_)
  obtain ⟨rfl, hco⟩ := hO
  have hco1 : co ≤ (groupOrderPrim ho).boundSize (camPB X) + 2 * X ^ 2 := by
    have hb := (groupOrderPrim ho).bound_le (v := x) (B := camPB X)
      ((Val.size_le_wt x).trans (by unfold camPB; omega))
    have h2 : x.wt + n ^ 2 + 5 ≤ 2 * X ^ 2 := by
      have : X + 4 ≤ X ^ 2 := by nlinarith
      omega
    clear * - hco hb h2
    omega
  set o := Nat.card (gens gs) with hoe
  set E := [x, Val.nat o] with hE
  have dn := Det.encPerms_size (gs := 1 :: gs) (Det.var' (P := P) (env := E) (i := 0) rfl)
  have dT := Det.call (Det.mk2 (Det.var' (P := P) (env := E) (i := 1) rfl) dn)
    (camSmall_spec hP.small o n)
  have hwo := wt_card_le (gens gs)
  have hS4 : (groupOrderPrim ho).boundSize (camPB X) ≤ camS4 ho hp hncl hd hqc hj X := by
    unfold camS4; omega
  by_cases hs : o < n ^ (1 + Nat.log 2 n)
  · -- the group is small: the answer `[0]`
    rw [show boolVal (decide (o < n ^ (1 + Nat.log 2 n))) = .nat 1 by simp [hs]] at dT
    refine EvalAll.ite dT (fun _ _ h => ⟨_, h.1⟩) fun xt ct hxt => ?_
    obtain ⟨h1, hct⟩ := hxt
    cases h1
    rw [if_neg one_ne_zero]
    refine (Det.snoc (Det.nil (P := P) (env := E)) (Det.nat 0)).post fun cc hcc =>
      ⟨Or.inl ⟨by simp, hs⟩, ?_⟩
    have hct1 := cam_test_cost (t := (Val.nat 1).wt) (show (Val.nat 1).wt = 3 from rfl).le hX.ge hX26 hn2 hnX hwo hct
    have hW : (Val.list ([] ++ [Val.nat 0])).wt ≤ 30 := by decide
    have hW1 : (Val.nat 1).wt = 3 := rfl
    have h4 : 1 ≤ X ^ 4 := Nat.one_le_pow _ _ (by omega)
    have h24 : X ^ 2 ≤ X ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    unfold camMainCost
    clear * - hco1 hct1 hcc hW hW1 h4 h24 hS4
    omega
  · -- the group is large: Maróti's theorem, then the tail
    rw [show boolVal (decide (o < n ^ (1 + Nat.log 2 n))) = .nat 0 by simp [hs]] at dT
    obtain ⟨m, k, r, e, hM, h5, hk1, hk⟩ := cam_normal_form hMa hn hprim (by omega)
    refine EvalAll.ite dT (fun _ _ h => ⟨_, h.1⟩) fun xt ct hxt => ?_
    obtain ⟨h1, hct⟩ := hxt
    cases h1
    rw [if_pos rfl]
    refine EvalAll.call_funAll (Det.var' (P := P) (env := E) (i := 0) rfl) fun v ca hv => ?_
    obtain ⟨rfl, hca⟩ := hv
    refine (camTail_spec hP gs e hM hprim hn h5 hk1 hk).wt_lt.mono fun w cb hw => ?_
    obtain ⟨⟨hout, hcb⟩, hwl⟩ := hw
    refine ⟨hout, ?_⟩
    have hct1 := cam_test_cost (t := (Val.nat 0).wt) (show (Val.nat 0).wt ≤ 3 from (show (Val.nat 0).wt = 2 from rfl).trans_le (by norm_num)) hX.ge hX26 hn2 hnX hwo hct
    have hW1 : (Val.nat 0).wt = 2 := rfl
    have h4 : X ≤ X ^ 4 := by
      calc X = X ^ 1 := (pow_one X).symm
        _ ≤ X ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h24 : X ^ 2 ≤ X ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    rw [hxw] at hcb
    unfold camMainCost
    clear * - hco1 hct1 hca hcb hwl hW1 h4 h24 hS4 hX
    omega

end GI.Impl
