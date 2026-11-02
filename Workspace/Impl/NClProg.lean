import Workspace.Impl.NClMath
import Workspace.Lang.Prims.BlockHom

/-!
# The normal closure loop as a program

The program `nclFuns b j` (36 functions at base `b`, membership primitive at index `j`) computes
the list `nclResult gs hs` of `Workspace.Impl.NClMath` on the value `[encGroup gs, encGroup hs]`.

* `b`: the entry. It appends the two generator lists (`A = (1 :: gs) ++ (1 :: hs)`), reduces
  `hs` by the doubling filter, runs `n² + 1` rounds and drops the identity in front.
* `b + 1 … b + 5`: the doubling filter `reduceFuns`; its step `keepStepE j` sits at `b + 5`.
* `b + 6 … b + 8`: append. `b + 9 … b + 11`: iterate the round `b + 12`.
* `b + 12`: one round (`nclProcF`): the conjugation fold `b + 13 … b + 15` over `A`, whose step
  `b + 16` (`nclConjF`) adds `g l g⁻¹` by the filter step.
* `b + 17 … b + 20`: composition. `b + 21 … b + 32`: inverse. `b + 33 … b + 35`: tail.
-/

namespace GI.Impl

open GI.Cited GI.Lang Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The conjugation step, on `[encPerm l, encGroup L, encPerm g]`: the filter step on
`g l g⁻¹`. -/
def nclConjF (b : ℕ) : Expr :=
  .call (b + 5) (mk3 (arg 0) (arg 1)
    (.call (b + 17) (mk2 (.call (b + 17) (mk2 (arg 2) (arg 0))) (.call (b + 21) (arg 2)))))

/-- One round, on `[A, i, encGroup L]`: if `i < |1 :: L|`, fold the conjugation step over `A`
with context entry `i` of `1 :: L`; else keep `L`. -/
def nclProcF (b : ℕ) : Expr :=
  .ite (.arith .lt (arg 1) (.length (.get (arg 2) (.nat 1))))
    (.call (b + 13) (mk3 (.get (.get (arg 2) (.nat 1)) (arg 1)) (arg 0) (arg 2)))
    (arg 2)

/-- The number of rounds, `n * n + 1`, from the group value in entry 0 of the argument. -/
def nclRoundsE : Expr :=
  .arith .add (.arith .mul (.get (arg 0) (.nat 0)) (.get (arg 0) (.nat 0))) (.nat 1)

/-- The entry, on `[encGroup gs, encGroup hs]`. -/
def nclEntry (b : ℕ) : Expr :=
  .letE (.call (b + 6) (mk2 (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 1))))
    (.letE (.call (b + 1) (arg 1))
      (.letE (.call (b + 9) (mk3 (.var 1) nclRoundsE (.var 2)))
        (.call (b + 33) (.get (.var 3) (.nat 1)))))

/-- **The program of the normal closure.** -/
def nclFuns (b j : ℕ) : List Expr :=
  [nclEntry b] ++ reduceFuns (b + 1) j ++ appendFuns (b + 6) ++ iterFuns (b + 9) (b + 12) ++
    [nclProcF b] ++ foldlFuns (b + 13) (b + 16) ++ [nclConjF b] ++ composeFuns (b + 17) ++
    invFuns (b + 21) ++ tailFuns (b + 33)

/-- The pieces of the program at their places. -/
structure NclAt (P : Program) (b j : ℕ) (h : Membership) : Prop where
  entry : P.funs[b]? = some (nclEntry b)
  red : P.HasAt (b + 1) (reduceFuns (b + 1) j)
  ks : P.funs[b + 5]? = some (keepStepE j)
  app : P.HasAt (b + 6) (appendFuns (b + 6))
  iter : P.HasAt (b + 9) (iterFuns (b + 9) (b + 12))
  proc : P.funs[b + 12]? = some (nclProcF b)
  fold : P.HasAt (b + 13) (foldlFuns (b + 13) (b + 16))
  conj : P.funs[b + 16]? = some (nclConjF b)
  comp : P.HasAt (b + 17) (composeFuns (b + 17))
  inv : P.HasAt (b + 21) (invFuns (b + 21))
  tail : P.HasAt (b + 33) (tailFuns (b + 33))
  mem : P.prims[j]? = some (membershipPrim h)

theorem nclAt_of {P : Program} {b j : ℕ} {h : Membership} (hP : P.HasAt b (nclFuns b j))
    (hj : P.prims[j]? = some (membershipPrim h)) : NclAt P b j h := by
  simp only [nclFuns] at hP
  have r := hP.left.left.left.left.left.left.left.left.right
  refine ⟨hP.left.left.left.left.left.left.left.left.left.single, r, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hj⟩
  · simpa [reduceFuns, foldlFuns, loopFuns, Nat.add_assoc] using r.right.single
  · simpa [reduceFuns, foldlFuns, loopFuns, Nat.add_assoc] using
      hP.left.left.left.left.left.left.left.right
  · simpa [reduceFuns, appendFuns, foldlFuns, loopFuns, Nat.add_assoc] using
      hP.left.left.left.left.left.left.right
  · simpa [reduceFuns, appendFuns, iterFuns, foldlFuns, loopFuns, Nat.add_assoc] using
      hP.left.left.left.left.left.right.single
  · simpa [reduceFuns, appendFuns, iterFuns, foldlFuns, loopFuns, Nat.add_assoc] using
      hP.left.left.left.left.right
  · simpa [reduceFuns, appendFuns, iterFuns, foldlFuns, loopFuns, Nat.add_assoc] using
      hP.left.left.left.right.single
  · simpa [reduceFuns, appendFuns, iterFuns, foldlFuns, loopFuns, Nat.add_assoc] using
      hP.left.left.right
  · simpa [reduceFuns, appendFuns, iterFuns, foldlFuns, composeFuns, mapFuns, loopFuns,
      Nat.add_assoc] using hP.left.right
  · simpa [reduceFuns, appendFuns, iterFuns, foldlFuns, composeFuns, mapFuns, invFuns,
      rangeFuns, findFuns, loopFuns, Nat.add_assoc] using hP.right

/-! ### The conjugation step -/

/-- The cost of one conjugation step. -/
noncomputable def nclConjCost (h : Membership) (n : ℕ) : ℕ := memCost h n + 10 ^ 6 * (n + 1) ^ 6

theorem nclConj_spec {P : Program} {b j : ℕ} {h : Membership} (hP : NclAt P b j h)
    (l : Perm (Fin n)) {L : List (Perm (Fin n))} (hl : L.length ≤ n ^ 2) (g : Perm (Fin n)) :
    FunDet P (b + 16) (.list [encPerm l, encGroup L, encPerm g]) (encGroup (nclConj l L g))
      (nclConjCost h n) := by
  set V : List Val := [encPerm l, encGroup L, encPerm g] with hV
  have d0 := Det.arg' (P := P) (vs := V) (rest := []) (j := 0) (v := encPerm l) rfl
  have d1 := Det.arg' (P := P) (vs := V) (rest := []) (j := 1) (v := encGroup L) rfl
  have d2 := Det.arg' (P := P) (vs := V) (rest := []) (j := 2) (v := encPerm g) rfl
  have dc1 := Det.call (Det.mk2 d2 d0) (compose_spec hP.comp g l)
  have di := Det.call d2 (inv_spec hP.inv g)
  have dc2 := Det.call (Det.mk2 dc1 di) (compose_spec hP.comp (g * l) g⁻¹)
  have dk := Det.call (Det.mk3 d0 d1 dc2) (keepStep_spec h hP.ks hP.mem (encPerm l) hl (g * l * g⁻¹))
  refine FunDet.intro hP.conj (dk.mono ?_)
  clear dk dc2 di dc1 d0 d1 d2
  have wl := wt_encPerm_le l
  have wg := wt_encPerm_le g
  have wgi := wt_encPerm_le g⁻¹
  have wgl := wt_encPerm_le (g * l)
  have wx := wt_encPerm_le (g * l * g⁻¹)
  have wL := wt_encGroup_sq hl
  have wK := wt_encGroup_succ (nclGood_length_keepStep_le hl (g * l * g⁻¹))
  have wV := wt_list3_le (encPerm l) (encGroup L) (encPerm g)
  have wV' := wt_list3_le (encPerm l) (encGroup L) (encPerm (g * l * g⁻¹))
  have w21 := wt_list2_le (encPerm g) (encPerm l)
  have w22 := wt_list2_le (encPerm (g * l)) (encPerm g⁻¹)
  have eV : (Val.list V).wt = (Val.list [encPerm l, encGroup L, encPerm g]).wt := rfl
  have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h36 : (n + 1) ^ 3 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h46 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold nclConjCost
  simp only [permK, invK]
  omega

/-! ### The conjugation fold -/

/-- The cost of the conjugation fold over a generator list of weight `W`. -/
noncomputable def nclFoldCost (h : Membership) (n W : ℕ) : ℕ :=
  (W + 1) * nclConjCost h n + 1000 * ((W + 1) * (3 * W + 1000 * (n + 1) ^ 6))

theorem nclFold_spec {P : Program} {b j : ℕ} {h : Membership} (hP : NclAt P b j h)
    (A : List (Perm (Fin n))) (l : Perm (Fin n)) {L : List (Perm (Fin n))} (hg : NclGood L) :
    FunDet P (b + 13) (.list [encPerm l, .list (A.map encPerm), encGroup L])
      (encGroup (A.foldl (nclConj l) L)) (nclFoldCost h n (Val.list (A.map encPerm)).wt) := by
  set xs := A.map encPerm with hxs
  have hlen : xs.length = A.length := by simp [hxs]
  have hf := foldl_spec hP.fold (c := encPerm l) (xs := xs) (acc0 := encGroup L)
    (Inv := fun k acc => acc = encGroup ((A.take k).foldl (nclConj l) L))
    (M := 160 * (n + 1) ^ 6) (B := fun _ => nclConjCost h n) (by simp)
    (fun k acc _ hacc => by
      rw [hacc]
      exact wt_encGroup_sq (nclGood_foldl l _ hg).length_le)
    (fun k acc hk hacc => by
      have hk' : k < A.length := by omega
      have hx : xs[k] = encPerm A[k] := by simp only [hxs, List.getElem_map]
      rw [hacc, hx]
      refine FunAll.mono (nclConj_spec hP l (nclGood_foldl l _ hg).length_le A[k])
        fun w cost hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, List.take_add_one, List.getElem?_eq_getElem hk', Option.toList_some,
        List.foldl_append]
      rfl)
  refine FunAll.mono hf fun w cost hw => ⟨?_, ?_⟩
  · rw [hw.1, hlen, List.take_length]
  · have hc := hw.2
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
    set W := (Val.list xs).wt
    have hxW : xs.length < W := length_lt_wt_list xs
    have w3 := wt_list3_le (encPerm l) (.list xs) (encGroup L)
    have wl := wt_encPerm_le l
    have wL := wt_encGroup_sq hg.length_le
    have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
    have k1 : xs.length * nclConjCost h n ≤ (W + 1) * nclConjCost h n :=
      Nat.mul_le_mul_right _ (by omega)
    have k2 : (xs.length + 1) * ((Val.list [encPerm l, .list xs, encGroup L]).wt + xs.length +
        160 * (n + 1) ^ 6 + 1) ≤ (W + 1) * (3 * W + 1000 * (n + 1) ^ 6) :=
      Nat.mul_le_mul (by omega) (by omega)
    unfold nclFoldCost
    simp only [loopModK] at hc
    rw [Nat.mul_assoc] at hc
    omega

/-! ### One round -/

/-- The cost of one round. -/
noncomputable def nclProcCost (h : Membership) (n W : ℕ) : ℕ :=
  nclFoldCost h n W + 10 ^ 5 * (W + (n + 1) ^ 6)

theorem nclProc_spec {P : Program} {b j : ℕ} {h : Membership} (hP : NclAt P b j h)
    (A : List (Perm (Fin n))) {L : List (Perm (Fin n))} (hg : NclGood L) {i : ℕ}
    (hi : i ≤ n * n) :
    FunDet P (b + 12) (.list [.list (A.map encPerm), .nat i, encGroup L])
      (encGroup (nclProc A L i)) (nclProcCost h n (Val.list (A.map encPerm)).wt) := by
  set V : List Val := [.list (A.map encPerm), .nat i, encGroup L] with hV
  set ys := (1 :: L).map encPerm with hys
  have eG : encGroup L = .list [.nat n, .list ys] := rfl
  have d0 := Det.arg' (P := P) (vs := V) (rest := []) (j := 0) (v := .list (A.map encPerm)) rfl
  have d1 := Det.arg' (P := P) (vs := V) (rest := []) (j := 1) (v := .nat i) rfl
  have d2 := Det.arg' (P := P) (vs := V) (rest := []) (j := 2) (v := encGroup L) rfl
  rw [eG] at d2
  have dy := Det.get' d2 (Det.nat 1) (show [Val.nat n, .list ys][1]? = some (.list ys) from rfl)
  have hyl : ys.length = L.length + 1 := by simp [hys]
  have wV := wt_list3_le (.list (A.map encPerm)) (.nat i) (encGroup L)
  have eV : (Val.list V).wt = (Val.list [.list (A.map encPerm), .nat i, encGroup L]).wt := rfl
  have wi := wt_nat_le i
  have wL := wt_encGroup_sq hg.length_le
  have wys : (Val.list ys).wt < (encGroup L).wt := by rw [eG]; exact wt_le_wt_list (by simp)
  have hyW : ys.length < (Val.list ys).wt := length_lt_wt_list ys
  have h26 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hnn : n * n ≤ (n + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  by_cases hlt : i < (1 :: L).length
  · have dt := Det.arith' (op := BinOp.lt) (z := 1) d1 (Det.length dy)
      (by simp only [BinOp.eval, hyl]; rw [if_pos (by simpa using hlt)])
    have hyi : ys[i]? = some (encPerm (1 :: L)[i]) := by
      rw [hys, List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
    have dl := Det.get' dy d1 hyi
    rw [← eG] at d2
    have dc := Det.call (Det.mk3 dl d0 d2) (nclFold_spec hP A (1 :: L)[i] hg)
    have e : nclProc A L i = A.foldl (nclConj (1 :: L)[i]) L := by
      unfold nclProc; rw [dif_pos hlt]
    rw [e]
    refine FunDet.intro hP.proc ((Det.ite_pos dt one_ne_zero dc).mono ?_)
    clear dc dl dt
    have wP := wt_encPerm_le (1 :: L)[i]
    have wF := wt_encGroup_sq (nclGood_foldl (1 :: L)[i] A hg).length_le
    have w3 := wt_list3_le (encPerm (1 :: L)[i]) (.list (A.map encPerm)) (encGroup L)
    unfold nclProcCost
    omega
  · have dt := Det.arith' (op := BinOp.lt) (z := 0) d1 (Det.length dy)
      (by simp only [BinOp.eval, hyl]; rw [if_neg (by simpa using hlt)])
    have e : nclProc A L i = L := by unfold nclProc; rw [dif_neg hlt]
    rw [e]
    rw [← eG] at d2
    refine FunDet.intro hP.proc ((Det.ite_zero dt d2).mono ?_)
    unfold nclProcCost nclFoldCost
    omega

/-! ### The rounds -/

/-- The cost of the `n * n + 1` rounds. -/
noncomputable def nclIterCost (h : Membership) (n W : ℕ) : ℕ :=
  (n * n + 1) * nclProcCost h n W + 1000 * ((n * n + 2) * (3 * W + 10 ^ 4 * (n + 1) ^ 6))

theorem nclIter_spec {P : Program} {b j : ℕ} {h : Membership} (hP : NclAt P b j h)
    (A : List (Perm (Fin n))) {L : List (Perm (Fin n))} (hg : NclGood L) :
    FunDet P (b + 9) (.list [.list (A.map encPerm), .nat (n * n + 1), encGroup L])
      (encGroup (nclLoop A L (n * n + 1))) (nclIterCost h n (Val.list (A.map encPerm)).wt) := by
  have hf := iter_spec hP.iter (c := .list (A.map encPerm)) (k := n * n + 1) (acc0 := encGroup L)
    (Inv := fun i acc => acc = encGroup (nclLoop A L i)) (M := 160 * (n + 1) ^ 6)
    (B := fun _ => nclProcCost h n (Val.list (A.map encPerm)).wt) rfl
    (fun i acc _ hacc => by
      rw [hacc]; exact wt_encGroup_sq (nclGood_nclLoop A hg i).length_le)
    (fun i acc hi hacc => by
      rw [hacc]
      refine FunAll.mono (nclProc_spec hP A (nclGood_nclLoop A hg i) (by omega))
        fun w cost hw => ⟨?_, hw.2⟩
      beta_reduce
      rw [hw.1, nclLoop_succ])
  refine FunAll.mono hf fun w cost hw => ⟨hw.1, ?_⟩
  have hc := hw.2
  beta_reduce at hc
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at hc
  unfold loopModK at hc
  have h16 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  have w3 := wt_list3_le (.list (A.map encPerm)) (.nat (n * n + 1)) (encGroup L)
  have wk := wt_nat_le (n * n + 1)
  have wL := wt_encGroup_sq hg.length_le
  have hnn : n * n ≤ (n + 1) ^ 6 := by
    have : n * n ≤ (n + 1) ^ 2 := by rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
    exact this.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have k2 : (n * n + 1 + 1) * ((Val.list [.list (A.map encPerm), .nat (n * n + 1),
      encGroup L]).wt + (n * n + 1) + 160 * (n + 1) ^ 6 + 1) ≤
      (n * n + 2) * (3 * (Val.list (A.map encPerm)).wt + 10 ^ 4 * (n + 1) ^ 6) :=
    Nat.mul_le_mul (by omega) (by omega)
  unfold nclIterCost
  rw [Nat.mul_assoc] at hc
  omega

/-! ### The costs as monomials in `Y` -/

section Poly

variable (h : Membership) {Y W : ℕ} (hW : W ≤ 4 * Y) (hn : n + 1 ≤ Y)
include hW hn

theorem nclFoldCost_le : nclFoldCost h n W ≤ 5 * (Y * memCost h n) + 2 * 10 ^ 7 * Y ^ 7 := by
  have p6 : (n + 1) ^ 6 ≤ Y ^ 6 := Nat.pow_le_pow_left hn 6
  have a1 : (W + 1) * nclConjCost h n ≤ (5 * Y) * (memCost h n + 10 ^ 6 * Y ^ 6) :=
    Nat.mul_le_mul (by omega) (by unfold nclConjCost; omega)
  have a2 : (W + 1) * (3 * W + 1000 * (n + 1) ^ 6) ≤ (5 * Y) * (12 * Y + 1000 * Y ^ 6) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e1 : (5 * Y) * (memCost h n + 10 ^ 6 * Y ^ 6) = 5 * (Y * memCost h n) + 5 * 10 ^ 6 * Y ^ 7 := by
    ring
  have e2 : (5 * Y) * (12 * Y + 1000 * Y ^ 6) = 60 * Y ^ 2 + 5000 * Y ^ 7 := by ring
  have y27 : Y ^ 2 ≤ Y ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold nclFoldCost
  omega

theorem nclProcCost_le : nclProcCost h n W ≤ 5 * (Y * memCost h n) + 3 * 10 ^ 7 * Y ^ 7 := by
  have := nclFoldCost_le h hW hn
  have p6 : (n + 1) ^ 6 ≤ Y ^ 6 := Nat.pow_le_pow_left hn 6
  have y17 : Y ≤ Y ^ 7 := Nat.le_self_pow (by omega) _
  have y67 : Y ^ 6 ≤ Y ^ 7 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold nclProcCost
  omega

theorem nclIterCost_le : nclIterCost h n W ≤ 5 * (Y ^ 3 * memCost h n) + 10 ^ 8 * Y ^ 9 := by
  have hp := nclProcCost_le h hW hn
  have p6 : (n + 1) ^ 6 ≤ Y ^ 6 := Nat.pow_le_pow_left hn 6
  have hnn : n * n + 1 ≤ Y ^ 2 := by
    have : (n + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hn 2
    have e : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    omega
  have b1 : (n * n + 1) * nclProcCost h n W ≤
      Y ^ 2 * (5 * (Y * memCost h n) + 3 * 10 ^ 7 * Y ^ 7) := Nat.mul_le_mul hnn hp
  have b2 : (n * n + 2) * (3 * W + 10 ^ 4 * (n + 1) ^ 6) ≤ (2 * Y ^ 2) * (12 * Y + 10 ^ 4 * Y ^ 6) :=
    Nat.mul_le_mul (by have : 1 ≤ Y ^ 2 := Nat.one_le_pow _ _ (by omega); omega) (by omega)
  have e1 : Y ^ 2 * (5 * (Y * memCost h n) + 3 * 10 ^ 7 * Y ^ 7) =
      5 * (Y ^ 3 * memCost h n) + 3 * 10 ^ 7 * Y ^ 9 := by ring
  have e2 : (2 * Y ^ 2) * (12 * Y + 10 ^ 4 * Y ^ 6) = 24 * Y ^ 3 + 2 * 10 ^ 4 * Y ^ 8 := by ring
  have y39 : Y ^ 3 ≤ Y ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  have y89 : Y ^ 8 ≤ Y ^ 9 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold nclIterCost
  omega

end Poly

end GI.Impl
