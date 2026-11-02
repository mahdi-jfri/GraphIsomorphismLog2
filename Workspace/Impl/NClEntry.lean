import Workspace.Impl.NClProg

/-!
# The entry of the normal closure program

`nclEntry_spec`: on `[encGroup gs, encGroup hs]` the program returns the list
`nclResult gs hs` (without the identity in front), at cost at most
`6 Y³ memCost + 10⁹ Y¹²`, where `Y` is the weight of the input plus one.
-/

namespace GI.Impl

open GI.Cited GI.Lang Equiv
open GI.Machine (BinOp)

variable {n : ℕ}

/-- The degree is below the weight of a group value. -/
theorem ncl_deg_lt_wt (gs : List (Perm (Fin n))) : n < (encGroup gs).wt := by
  have h1 : n < (encPerm (1 : Perm (Fin n))).wt := by
    have := length_lt_wt_list ((List.finRange n).map fun i => Val.nat ((1 : Perm (Fin n)) i))
    simpa [encPerm] using this
  have h2 : (encPerm (1 : Perm (Fin n))).wt < (Val.list ((1 :: gs).map encPerm)).wt :=
    wt_le_wt_list (by simp)
  have h3 : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
    wt_le_wt_list (by simp [encGroup, encPerms])
  omega

theorem ncl_listWt_lt (gs : List (Perm (Fin n))) :
    (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt :=
  wt_le_wt_list (by simp [encGroup, encPerms])

/-- **The entry.** -/
theorem nclEntry_spec {P : Program} {b j : ℕ} {h : Membership} (hP : NclAt P b j h)
    (gs hs : List (Perm (Fin n))) :
    FunDet P b (.list [encGroup gs, encGroup hs]) (.list ((nclResult gs hs).map encPerm))
      (6 * (((Val.list [encGroup gs, encGroup hs]).wt + 1) ^ 3 * memCost h n) +
        10 ^ 9 * ((Val.list [encGroup gs, encGroup hs]).wt + 1) ^ 12) := by
  set a0 : List Val := [encGroup gs, encGroup hs] with ha0
  set xs := (1 :: gs).map encPerm with hxs
  set ys := (1 :: hs).map encPerm with hys
  set Lf := nclResult gs hs with hLf
  have eA : xs ++ ys = (nclGens gs hs).map encPerm := by simp [hxs, hys, nclGens]
  set Av := Val.list ((nclGens gs hs).map encPerm) with hAv
  -- the append
  have dG := Det.arg' (P := P) (vs := a0) (rest := []) (j := 0)
    (v := .list [.nat n, .list xs]) rfl
  have dH := Det.arg' (P := P) (vs := a0) (rest := []) (j := 1)
    (v := .list [.nat n, .list ys]) rfl
  have dX := Det.get' dG (Det.nat 1) (show [Val.nat n, .list xs][1]? = some (.list xs) from rfl)
  have dY := Det.get' dH (Det.nat 1) (show [Val.nat n, .list ys][1]? = some (.list ys) from rfl)
  have hApp : FunDet P (b + 6) (.list [.list xs, .list ys]) Av
      (loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length + Av.wt + 1)) :=
    (append_spec hP.app xs ys).mono fun w c hw => by
      obtain ⟨e, hc⟩ := hw
      rw [eA] at e
      subst e
      exact ⟨rfl, hc⟩
  have dA := Det.call (Det.mk2 dX dY) hApp
  -- the reduction of `hs`
  have d1 := Det.arg' (P := P) (vs := a0) (rest := [Av]) (j := 1) (v := encGroup hs) rfl
  have dR := Det.call d1 (reduce_spec h hP.red hP.mem hs)
  -- the rounds
  have dG' := Det.arg' (P := P) (vs := a0) (rest := [Av, encGroup (keepList hs)]) (j := 0)
    (v := .list [.nat n, .list xs]) rfl
  have dn := Det.get' dG' (Det.nat 0) (show [Val.nat n, .list xs][0]? = some (.nat n) from rfl)
  have dk := Det.arith' (op := BinOp.add) (z := n * n + 1)
    (Det.arith' (op := BinOp.mul) (z := n * n) dn dn rfl) (Det.nat 1) rfl
  have dI := Det.call (Det.mk3 (Det.var' (env := [Val.list a0, Av, encGroup (keepList hs)])
    (P := P) (i := 1) rfl) dk (Det.var' (i := 2) rfl))
    (nclIter_spec hP (nclGens gs hs) (nclGood_keepList hs))
  -- the tail
  have eL : encGroup Lf = .list [.nat n, .list (encPerm 1 :: Lf.map encPerm)] := rfl
  have dT := Det.call (Det.get' (Det.var' (P := P)
    (env := [Val.list a0, Av, encGroup (keepList hs), encGroup Lf]) (i := 3) rfl) (Det.nat 1)
    (show [Val.nat n, .list (encPerm 1 :: Lf.map encPerm)][1]? =
      some (.list (encPerm 1 :: Lf.map encPerm)) from rfl))
    (tail_spec hP.tail (encPerm 1) (Lf.map encPerm))
  have dE := Det.letE dA (Det.letE dR (Det.letE dI dT))
  refine FunDet.intro hP.entry (dE.mono ?_)
  clear dE dT dI dk dn dG' dR d1 dA hApp dX dY dG dH
  -- the weights
  have hres := ncl_correct gs hs
  rw [← hLf] at hres
  set X := (Val.list a0).wt with hX
  have wa : (encGroup gs).wt + (encGroup hs).wt < X := by
    have := sum_wt_lt_wt_list a0; simpa [ha0] using this
  have wx : (Val.list xs).wt < (encGroup gs).wt := ncl_listWt_lt gs
  have wy : (Val.list ys).wt < (encGroup hs).wt := ncl_listWt_lt hs
  have hnG := ncl_deg_lt_wt gs
  have hyl : ys.length < (Val.list ys).wt := length_lt_wt_list ys
  have hxl : xs.length < (Val.list xs).wt := length_lt_wt_list xs
  have hyl' : ys.length = hs.length + 1 := by simp [hys]
  have wAv : Av.wt ≤ 4 * (X + 1) := by
    have e1 : Av = Val.list (xs ++ ys) := by rw [hAv, eA]
    have h1 := wt_list_le (xs ++ ys)
    have h2 := sum_wt_lt_wt_list xs
    have h3 := sum_wt_lt_wt_list ys
    simp only [List.map_append, List.sum_append, List.length_append] at h1
    rw [e1]; omega
  have eAv : (Val.list (List.map encPerm (nclGens gs hs))).wt = Av.wt := rfl
  have hn : n + 1 ≤ X + 1 := by omega
  have hit := nclIterCost_le h wAv hn
  rw [← eAv] at hit
  set Y := X + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  have p6 : (n + 1) ^ 6 ≤ Y ^ 6 := Nat.pow_le_pow_left hn 6
  have hnn : n * n ≤ Y ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  have y26 : Y ^ 2 ≤ Y ^ 6 := Nat.pow_le_pow_right hY1 (by omega)
  have y6 : Y ^ 6 ≤ Y ^ 12 := Nat.pow_le_pow_right hY1 (by omega)
  have y8 : Y ^ 8 ≤ Y ^ 12 := Nat.pow_le_pow_right hY1 (by omega)
  have y9 : Y ^ 9 ≤ Y ^ 12 := Nat.pow_le_pow_right hY1 (by omega)
  have y1 : Y ≤ Y ^ 2 := Nat.le_self_pow (by omega) _
  have ym : Y * memCost h n ≤ Y ^ 3 * memCost h n :=
    Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) _)
  -- the reduction
  have hred : reduceCost h n hs.length ≤ Y * memCost h n + 10 ^ 7 * Y ^ 12 := by
    unfold reduceCost reduceK
    have r1 : (hs.length + 1) * memCost h n ≤ Y * memCost h n := Nat.mul_le_mul_right _ (by omega)
    have r2 : ((hs.length + 2) * (n + 1)) ^ 6 ≤ (Y * Y) ^ 6 :=
      Nat.pow_le_pow_left (Nat.mul_le_mul (by omega) (by omega)) 6
    have e : (Y * Y) ^ 6 = Y ^ 12 := by ring
    omega
  -- the append
  have w2 := wt_list2_le (.list xs) (.list ys)
  have happ : loopModK * (ys.length + 1) * ((Val.list [.list xs, .list ys]).wt + ys.length +
      Av.wt + 1) ≤ 20000 * Y ^ 2 := by
    unfold loopModK
    rw [Nat.mul_assoc]
    have := Nat.mul_le_mul (show ys.length + 1 ≤ Y by omega)
      (show (Val.list [.list xs, .list ys]).wt + ys.length + Av.wt + 1 ≤ 20 * Y by omega)
    have e : Y * (20 * Y) = 20 * Y ^ 2 := by ring
    omega
  -- the tail
  have hLl := hres.1
  have wLf := wt_encGroup_sq hLl
  have eLf : (Val.list [Val.nat n, Val.list (List.map encPerm (1 :: Lf))]).wt = (encGroup Lf).wt :=
    rfl
  have eLf' : (encGroup (nclLoop (nclGens gs hs) (keepList hs) (n * n + 1))).wt =
    (encGroup Lf).wt := rfl
  have e1L : (Val.list (encPerm (1 : Perm (Fin n)) :: List.map encPerm Lf)).wt =
    (Val.list (List.map encPerm (1 :: Lf))).wt := rfl
  have w1L : (Val.list (List.map encPerm (1 :: Lf))).wt < (encGroup Lf).wt := ncl_listWt_lt Lf
  have wLs : (Val.list (List.map encPerm Lf)).wt ≤ (Val.list (encPerm (1 : Perm (Fin n)) :: List.map encPerm Lf)).wt :=
    wt_list_sublist (List.sublist_cons_self (encPerm (1 : Perm (Fin n))) (List.map encPerm Lf))
  have htail : loopModK * ((List.map encPerm Lf).length + 1) *
      (3 * (Val.list (encPerm (1 : Perm (Fin n)) :: List.map encPerm Lf)).wt + 1) ≤ 500000 * Y ^ 8 := by
    unfold loopModK
    rw [Nat.mul_assoc, List.length_map]
    have h2 : Lf.length + 1 ≤ Y ^ 2 := by
      have : (n + 1) ^ 2 ≤ Y ^ 2 := Nat.pow_le_pow_left hn 2
      have e : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by ring
      omega
    have := Nat.mul_le_mul h2
      (show 3 * (Val.list (encPerm (1 : Perm (Fin n)) :: List.map encPerm Lf)).wt + 1 ≤ 500 * Y ^ 6 by
        have : 1 ≤ Y ^ 6 := Nat.one_le_pow _ _ (by omega)
        omega)
    have e : Y ^ 2 * (500 * Y ^ 6) = 500 * Y ^ 8 := by ring
    omega
  -- the rounds
  have wK := wt_encGroup_sq (length_keepList_le hs)
  have w3 := wt_list3_le Av (.nat (n * n + 1)) (encGroup (keepList hs))
  have wnn := wt_nat_le (n * n + 1)
  have wn := wt_nat_le n
  omega

end GI.Impl
