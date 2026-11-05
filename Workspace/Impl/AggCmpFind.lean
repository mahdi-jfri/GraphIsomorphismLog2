module

public import Workspace.Impl.AggCmpMoves
public import Workspace.Impl.AggCacheProg

@[expose] public section

/-!
# The pick cache lookup, in `GI.Lang`

The comparison program keeps the pick cache as a list of values `cmEntV (hs, b)`: a lifted group
and the representative chosen for its coset. For a new coset `(gs, a)` it looks for the first
value with the same coset (`cmTest`, `cm_entSet_eq_iff`): two subgroup tests (`le_spec`) and one
**Membership** call on `b⁻¹ a` (`member_det`, with `inv_spec` and `compose_spec`).

* `cmTestF`, `cmTest_spec`: the test of one value, on `[key, value]` with the key
  `cmKeyV gs a = [encGroup gs, encPerm a]`.
* `cmFindFuns b jm` (25 functions), `cmFind_spec`: on `[key, ⟨values⟩]` the index of the first
  value that passes the test (`find_spec`), at cost at most `cmFindCost h M` for an argument of
  weight at most `M`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens Membership)

variable {k : ℕ}

/-- The key of a new coset `(gs, a)`. -/
def cmKeyV (gs : List (Perm (Fin k))) (a : Perm (Fin k)) : Val := .list [encGroup gs, encPerm a]

/-- **The test of one value**, on `[key, value]`, with the subgroup test at `le`, inverse at
`inv`, composition at `comp` and membership at primitive `jm`. -/
def cmTestF (le inv comp jm : ℕ) : Expr :=
  .ite (.call le (mk2 (.get (arg 1) (.nat 0)) (.get (arg 0) (.nat 0))))
    (.ite (.call le (mk2 (.get (arg 0) (.nat 0)) (.get (arg 1) (.nat 0))))
      (.prim jm (mk2 (.get (arg 1) (.nat 0))
        (.call comp (mk2 (.call inv (.get (arg 1) (.nat 1))) (.get (arg 0) (.nat 1))))))
      (.nat 0))
    (.nat 0)

/-- The cost of one test on an argument of weight at most `W`. -/
noncomputable def cmTestCost (h : Membership) (W : ℕ) : ℕ :=
  3 * ((4 * W + 20) * (membershipPrim h).boundSize (4 * W + 20) + 20000 * (4 * W + 20) ^ 3) +
    2 * (invK * (W + 1) ^ 4) + 2 * (permK * (W + 1) ^ 3) + 400 * W + 800

theorem cmTestCost_mono (h : Membership) {W W' : ℕ} (hW : W ≤ W') :
    cmTestCost h W ≤ cmTestCost h W' := by
  unfold cmTestCost
  have h1 : (membershipPrim h).boundSize (4 * W + 20) ≤ (membershipPrim h).boundSize (4 * W' + 20) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  have h2 := Nat.mul_le_mul (show 4 * W + 20 ≤ 4 * W' + 20 by omega) h1
  have h3 : (4 * W + 20) ^ 3 ≤ (4 * W' + 20) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h4 : (W + 1) ^ 4 ≤ (W' + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have h5 : (W + 1) ^ 3 ≤ (W' + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have h6 := Nat.mul_le_mul_left invK h4
  have h7 := Nat.mul_le_mul_left permK h5
  omega

theorem cm_k_lt_wt_perm (a : Perm (Fin k)) : k < (encPerm a).wt := by
  have := length_lt_wt_list ((List.finRange k).map fun i => Val.nat (a i))
  simpa [encPerm_eq_encFun, encFun] using this

open Classical in
/-- **The test of one value.** -/
theorem cmTest_spec (h : Membership) {P : Program} {f le inv comp jm : ℕ}
    (hf : P.funs[f]? = some (cmTestF le inv comp jm)) (hle : P.HasAt le (leFuns le jm))
    (hinv : P.HasAt inv (invFuns inv)) (hcomp : P.HasAt comp (composeFuns comp))
    (hj : P.prims[jm]? = some (membershipPrim h)) (gs : List (Perm (Fin k))) (a : Perm (Fin k))
    (p : List (Perm (Fin k)) × Perm (Fin k)) :
    FunDet P f (.list [cmKeyV gs a, cmEntV p]) (boolVal (cmTest gs a p))
      (cmTestCost h (Val.list [cmKeyV gs a, cmEntV p]).wt) := by
  set W := (Val.list [cmKeyV gs a, cmEntV p]).wt with hW
  set vs : List Val := [cmKeyV gs a, cmEntV p]
  have gk := Det.arg' (P := P) (vs := vs) (rest := []) (j := 0) (v := cmKeyV gs a) rfl
  have ge := Det.arg' (P := P) (vs := vs) (rest := []) (j := 1) (v := cmEntV p) rfl
  have hkW : (cmKeyV gs a).wt < W := wt_le_wt_list (by simp)
  have heW : (cmEntV p).wt < W := wt_le_wt_list (by simp)
  have wK0 : (encGroup gs).wt < (cmKeyV gs a).wt := wt_le_wt_list (by simp)
  have wK1 : (encPerm a).wt < (cmKeyV gs a).wt := wt_le_wt_list (by simp)
  have wE0 : (encGroup p.1).wt < (cmEntV p).wt := wt_le_wt_list (by simp)
  have wE1 : (encPerm p.2).wt < (cmEntV p).wt := wt_le_wt_list (by simp)
  have dK0 := Det.get' gk (Det.nat 0) (v := encGroup gs) rfl
  have dK1 := Det.get' gk (Det.nat 1) (v := encPerm a) rfl
  have dE0 := Det.get' ge (Det.nat 0) (v := encGroup p.1) rfl
  have dE1 := Det.get' ge (Det.nat 1) (v := encPerm p.2) rfl
  have t1 := ckLe_det h hle hj (W := W) dE0 dK0 (by omega) (by omega)
  have t2 := ckLe_det h hle hj (W := W) dK0 dE0 (by omega) (by omega)
  -- the element `p.2⁻¹ a`
  have di := Det.call dE1 (inv_spec hinv p.2)
  have dc := Det.call (Det.mk2 di dK1) (compose_spec hcomp p.2⁻¹ a)
  have dm := member_det h hj (Det.mk2 dE0 dc) (G := gens p.1) ⟨p.1, rfl, rfl⟩
  have i2 := Det.ite' t2 dm (Det.nat (P := P) (env := [Val.list vs]) 0)
  rw [ckIte] at i2
  have i1 := Det.ite' t1 i2 (Det.nat (P := P) (env := [Val.list vs]) 0)
  rw [ckIte] at i1
  have hv : (decide (gens gs ≤ gens p.1) && (decide (gens p.1 ≤ gens gs) &&
      decide (p.2⁻¹ * a ∈ gens p.1))) = cmTest gs a p := by
    unfold cmTest; congr
  rw [hv] at i1
  refine FunDet.intro hf (i1.mono ?_)
  -- the cost
  have hkn : k < W := by have := cm_k_lt_wt_perm a; omega
  have b1 := wt_boolVal_le (cmTest gs a p)
  have b2 := wt_nat_le 0
  have b3 := wt_boolVal_le (decide (gens p.1 ≤ gens gs))
  have b4 := wt_boolVal_le (decide (gens gs ≤ gens p.1))
  have b5 := wt_boolVal_le (decide (p.2⁻¹ * a ∈ gens p.1))
  have b6 := wt_boolVal_le (decide (gens p.1 ≤ gens gs) && decide (p.2⁻¹ * a ∈ gens p.1))
  have w1 := wt_encPerm_le p.2⁻¹
  have w2 := wt_encPerm_le (p.2⁻¹ * a)
  have w3 := wt_list2_le (encGroup p.1) (encPerm (p.2⁻¹ * a))
  have w4 := wt_list2_le (encPerm p.2⁻¹) (encPerm a)
  -- the membership bound at the size of the argument
  have hsz : (Val.list [encGroup p.1, encPerm (p.2⁻¹ * a)]).size ≤ 4 * W + 20 := by
    have e := size_list2_encPerm (encGroup p.1) (p.2⁻¹ * a) p.2
    have s1 := (Val.list [encGroup p.1, encPerm p.2]).size_le_wt
    have s2 := wt_list2_le (encGroup p.1) (encPerm p.2)
    omega
  have hmb := (membershipPrim h).bound_le hsz
  have k1 : invK * (k + 1) ^ 4 ≤ invK * (W + 1) ^ 4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have k2 : permK * (k + 1) ^ 3 ≤ permK * (W + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have k3 : 4 * (k + 1) ^ 2 ≤ 4 * (W + 1) ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have k4 : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have k5 : 100 * (W + 1) ^ 3 ≤ permK * (W + 1) ^ 3 :=
    Nat.mul_le_mul_right _ (by simp [permK])
  have hvs : (Val.list vs).wt = W := rfl
  have hX : (membershipPrim h).boundSize (4 * W + 20) ≤
      (4 * W + 20) * (membershipPrim h).boundSize (4 * W + 20) := Nat.le_mul_of_pos_left _ (by omega)
  unfold cmTestCost
  clear_value W vs
  generalize (4 * W + 20) * (membershipPrim h).boundSize (4 * W + 20) = X at hX ⊢
  generalize 20000 * (4 * W + 20) ^ 3 = Y
  omega

/-! ### The lookup -/

/-- The lookup module at base `b` (25 functions), with membership at primitive `jm`. -/
def cmFindFuns (b jm : ℕ) : List Expr :=
  findFuns b (b + 3) ++ [cmTestF (b + 4) (b + 9) (b + 21) jm] ++ leFuns (b + 4) jm ++
    invFuns (b + 9) ++ composeFuns (b + 21)

/-- The cost of the lookup on an argument of weight at most `M`. -/
noncomputable def cmFindCost (h : Membership) (M : ℕ) : ℕ :=
  M * cmTestCost h (4 * M + 6) + loopModK * (M + 1) * (3 * M + 3)

theorem cmEntV_injective : Function.Injective (cmEntV (k := k)) := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ h
  simp only [cmEntV, Val.list.injEq, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [encGroup_injective h1, encPerm_injective h2]

open Classical in
/-- The test on values. -/
noncomputable def cmTestV (gs : List (Perm (Fin k))) (a : Perm (Fin k)) (v : Val) : Bool :=
  decide (∃ p, cmEntV p = v ∧ cmTest gs a p = true)

theorem cmTestV_ent (gs : List (Perm (Fin k))) (a : Perm (Fin k))
    (p : List (Perm (Fin k)) × Perm (Fin k)) : cmTestV gs a (cmEntV p) = cmTest gs a p := by
  rw [Bool.eq_iff_iff]
  unfold cmTestV
  rw [@decide_eq_true_iff _ (Classical.propDecidable _)]
  constructor
  · rintro ⟨p', he, hm⟩
    rwa [← cmEntV_injective he]
  · intro hm; exact ⟨p, rfl, hm⟩

/-- **The pick cache lookup**: the index of the first value with the coset of `(gs, a)`. -/
theorem cmFind_spec (h : Membership) {P : Program} {b jm : ℕ} (hb : P.HasAt b (cmFindFuns b jm))
    (hj : P.prims[jm]? = some (membershipPrim h)) (gs : List (Perm (Fin k))) (a : Perm (Fin k))
    (c : List (List (Perm (Fin k)) × Perm (Fin k))) {M : ℕ}
    (hM : (Val.list [cmKeyV gs a, .list (c.map cmEntV)]).wt ≤ M) :
    FunDet P b (.list [cmKeyV gs a, .list (c.map cmEntV)]) (.nat (c.findIdx (cmTest gs a)))
      (cmFindCost h M) := by
  have hfind : P.HasAt b (findFuns b (b + 3)) := hb.left.left.left.left
  have htest : P.funs[b + 3]? = some (cmTestF (b + 4) (b + 9) (b + 21) jm) := by
    simpa [findFuns, loopFuns] using hb.left.left.left.right.single
  have hle : P.HasAt (b + 4) (leFuns (b + 4) jm) := by simpa [findFuns, loopFuns] using hb.left.left.right
  have hinv : P.HasAt (b + 9) (invFuns (b + 9)) := by
    simpa [findFuns, leFuns, allFuns, loopFuns, Nat.add_assoc] using hb.left.right
  have hcomp : P.HasAt (b + 21) (composeFuns (b + 21)) := by
    simpa [leFuns, allFuns, loopFuns, invFuns, mapFuns, rangeFuns, findFuns, Nat.add_assoc]
      using hb.right
  have hkM : (cmKeyV gs a).wt < M := lt_of_lt_of_le (wt_le_wt_list (by simp)) hM
  have hcM : (Val.list (c.map cmEntV)).wt < M := lt_of_lt_of_le (wt_le_wt_list (by simp)) hM
  have hT : ∀ x ∈ c.map cmEntV, FunDet P (b + 3) (.list [cmKeyV gs a, x])
      (boolVal (cmTestV gs a x)) (cmTestCost h (4 * M + 6)) := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
    rw [cmTestV_ent]
    refine (cmTest_spec h htest hle hinv hcomp hj gs a p).mono ?_
    have h1 := wt_list2_le (cmKeyV gs a) (cmEntV p)
    have h2 : (cmEntV p).wt < (Val.list (c.map cmEntV)).wt := wt_le_wt_list hx
    exact cmTestCost_mono h (by omega)
  refine (find_spec hfind hT).mono fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1, List.findIdx_map]
    congr 2
    funext p
    exact cmTestV_ent gs a p
  · have hc := hw.2
    rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map] at hc
    have hl : c.length < M := by
      have := length_lt_wt_list (c.map cmEntV); simp only [List.length_map] at this; omega
    have a1 : c.length * cmTestCost h (4 * M + 6) ≤ M * cmTestCost h (4 * M + 6) :=
      Nat.mul_le_mul_right _ hl.le
    have a2 : loopModK * (c.length + 1) *
        ((Val.list [cmKeyV gs a, .list (c.map cmEntV)]).wt + 2 * c.length + 3) ≤
        loopModK * (M + 1) * (3 * M + 3) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    unfold cmFindCost
    omega

end GI.Impl
