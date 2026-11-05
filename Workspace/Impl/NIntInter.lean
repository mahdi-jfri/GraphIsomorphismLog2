module

public import Workspace.Impl.NIntFac

@[expose] public section

/-!
# Intersection with a normalized subgroup, as a program

Source: [LM] = Luks–Miyazaki, DMTCS 13:4 (2011), Theorem 3.1(viii)(b); Luks 1993, Prop. 7.1.
The task is `GI.Cited.NormalizedIntersectionTask`: `G = ⟨gs⟩` normalizes `N = ⟨ns⟩`; output at
most `n²` generators of `G ∩ N`.

The program `nintInterProgram hp` calls the pointwise stabilizer (`hp`) twice:

1. On `Fin (n + n)`, form the generators `g ⊕ g` (`g ∈ 1 :: gs`) and `1 ⊕ m` (`m ∈ 1 :: ns`) of
   the group `K` (`GI.Proved.nintPairs`).
2. Compute generators `hs` of the pointwise stabilizer of the points `n, …, 2n - 1` in `K`.
3. Each `h ∈ hs` is `a ⊕ 1`, and these `a` generate `G ∩ N` (`GI.Proved.nint_inter`). The
   program reads `a` as the first `n` entries of `h`.
4. The list of the `a` may have up to `(2n)²` entries. A second call, the pointwise stabilizer
   of no points in `⟨a, …⟩`, returns the same group by at most `n²` generators.

The functions (base 0): the entry; `a ⊕ b` (`shiftAppF`) at 1 with `append` at 2, a map at 5
and `addKF` at 8 (as in `Workspace/Impl/Lift.lean`); `g ↦ g ⊕ g` at 9 and its map at 10;
`m ↦ 1 ⊕ m` at 13 and its map at 14; `range` at 17; `take` at 20 and its map at 23.
-/

namespace GI.Impl

open GI.Cited GI.Lang GI.Proved Equiv

/-- On `[n, g]`: `g ⊕ g`. -/
def nintDblF : Expr := .call 1 (mk3 (arg 1) (arg 1) (arg 0))

/-- On `[[1, n], m]`: `1 ⊕ m`. -/
def nintPrF : Expr := .call 1 (mk3 (.get (arg 0) (.nat 0)) (arg 1) (.get (arg 0) (.nat 1)))

/-- The entry, on `[encGroup gs, encGroup ns]`. The environment after the `let`s:
`[input, n, encPerm 1, generators of K, generators of the stabilizer, their restrictions]`. -/
def nintInterEntry : Expr :=
  .letE (.get (arg 0) (.nat 0))
  (.letE (.get (.get (arg 0) (.nat 1)) (.nat 0))
  (.letE (.call 2 (mk2 (.call 10 (mk2 (.var 1) (.get (arg 0) (.nat 1))))
    (.call 14 (mk2 (mk2 (.var 2) (.var 1)) (.get (arg 1) (.nat 1))))))
  (.letE (.prim 0 (mk2 (mk2 (.arith .add (.var 1) (.var 1)) (.var 3))
    (.call 5 (mk2 (.var 1) (.call 17 (.var 1))))))
  (.letE (.call 23 (mk2 (.var 1) (.var 4)))
  (.prim 0 (mk2 (mk2 (.var 1) (.call 2 (mk2 (mk1 (.var 2)) (.var 5)))) .nil))))))

/-- The functions of the program. -/
def nintInterFuns : List Expr :=
  [nintInterEntry] ++ [shiftAppF 2 5] ++ appendFuns 2 ++ mapFuns 5 8 ++ [addKF] ++ [nintDblF] ++
    mapFuns 10 9 ++ [nintPrF] ++ mapFuns 14 13 ++ rangeFuns 17 ++ linTakeFuns 20 ++
    mapFuns 23 20

/-- **The intersection program**, with the pointwise stabilizer as primitive `0`. -/
noncomputable def nintInterProgram (hp : PointwiseStab) : Program :=
  ⟨nintInterFuns, [pointwiseStabPrim hp]⟩

section Layout

variable (hp : PointwiseStab)

theorem nintInter_hasAt : (nintInterProgram hp).HasAt 0 nintInterFuns := by
  simpa [nintInterProgram] using Program.hasAt_append [] nintInterFuns [] [pointwiseStabPrim hp]

theorem nintInter_entry : (nintInterProgram hp).funs[0]? = some nintInterEntry := rfl
theorem nintInter_shift : (nintInterProgram hp).funs[1]? = some (shiftAppF 2 5) := rfl
theorem nintInter_append : (nintInterProgram hp).HasAt 2 (appendFuns 2) :=
  (nintInter_hasAt hp).block 2 rfl
theorem nintInter_addMap : (nintInterProgram hp).HasAt 5 (mapFuns 5 8) :=
  (nintInter_hasAt hp).block 5 rfl
theorem nintInter_addK : (nintInterProgram hp).funs[8]? = some addKF := rfl
theorem nintInter_dbl : (nintInterProgram hp).funs[9]? = some nintDblF := rfl
theorem nintInter_dblMap : (nintInterProgram hp).HasAt 10 (mapFuns 10 9) :=
  (nintInter_hasAt hp).block 10 rfl
theorem nintInter_pr : (nintInterProgram hp).funs[13]? = some nintPrF := rfl
theorem nintInter_prMap : (nintInterProgram hp).HasAt 14 (mapFuns 14 13) :=
  (nintInter_hasAt hp).block 14 rfl
theorem nintInter_range : (nintInterProgram hp).HasAt 17 (rangeFuns 17) :=
  (nintInter_hasAt hp).block 17 rfl
theorem nintInter_take : (nintInterProgram hp).HasAt 20 (linTakeFuns 20) :=
  (nintInter_hasAt hp).block 20 rfl
theorem nintInter_takeMap : (nintInterProgram hp).HasAt 23 (mapFuns 23 20) :=
  (nintInter_hasAt hp).block 23 rfl
theorem nintInter_prim : (nintInterProgram hp).prims[0]? = some (pointwiseStabPrim hp) := rfl

/-- `a ⊕ c`, in this program. -/
theorem nintInter_shift_spec {n n' : ℕ} (a : Perm (Fin n)) (c : Perm (Fin n')) :
    FunDet (nintInterProgram hp) 1 (.list [encPerm a, encPerm c, .nat n])
      (encPerm (sumToFin (Perm.sumCongr a c))) (shiftK * (n + n' + 1) ^ 3) :=
  shiftApp_spec (b := 0) (nintInter_shift hp) (nintInter_append hp) (nintInter_addMap hp)
    (nintInter_addK hp) a c

end Layout

/-! ### Encodings -/

theorem nint_encPerm_injective {n : ℕ} : Function.Injective (encPerm (n := n)) := by
  intro a b h
  exact encPerm_injective h

/-- The first `n` entries of `a ⊕ c` are those of `a`. -/
theorem nint_encPerm_sum_take {n : ℕ} (a c : Perm (Fin n)) :
    encPerm (nintSum (a, c)) = .list ((List.finRange n).map (fun i => Val.nat (a i)) ++
      (List.finRange n).map (fun j => Val.nat (n + c j))) :=
  encPerm_sumToFin a c

theorem nint_encPts (n : ℕ) :
    encPts (nintPts n) = .list ((List.range n).map fun j => Val.nat (n + j)) := by
  rw [encPts_eq, nintPts, ← List.map_coe_finRange_eq_range, List.map_map, List.map_map]
  rfl

theorem nintSum_one {n : ℕ} : nintSum ((1, 1) : Perm (Fin n) × Perm (Fin n)) = 1 :=
  map_one nintSum

/-- The generators of `K` given to the first call, without the identity. -/
def nintKGens {n : ℕ} (gs ns : List (Perm (Fin n))) : List (Perm (Fin (n + n))) :=
  gs.map (fun g => nintSum (g, g)) ++ (1 :: ns).map (fun m => nintSum (1, m))

theorem nint_encGroup_K {n : ℕ} (gs ns : List (Perm (Fin n))) :
    encGroup (nintKGens gs ns) = .list [.nat (n + n),
      .list ((1 :: gs).map (fun g => encPerm (nintSum (g, g))) ++
        (1 :: ns).map (fun m => encPerm (nintSum (1, m))))] := by
  simp only [encGroup, encPerms, nintKGens, List.map_cons, List.map_append, List.map_map,
    List.cons_append, Function.comp_def]
  rw [nintSum_one]

theorem nint_gens_K {n : ℕ} (gs ns : List (Perm (Fin n))) :
    gens ((nintPairGens (1 :: gs) (1 :: ns)).map nintSum) = gens (nintKGens gs ns) := by
  have : (nintPairGens (1 :: gs) (1 :: ns)).map nintSum = 1 :: nintKGens gs ns := by
    simp only [nintPairGens, nintKGens, List.map_cons, List.map_append, List.map_map,
      List.cons_append, Function.comp_def]
    rw [show nintSum (nintDiag (1 : Perm (Fin n))) = 1 from by rw [map_one, map_one]]
    rfl
  rw [this, nint_gens_cons_one]

/-! ### The specification: the steps -/

/-- The weight facts of the input. -/
structure NIntInterW {n : ℕ} (gs ns : List (Perm (Fin n))) (X : ℕ) : Prop where
  wG : (encGroup gs).wt + (encGroup ns).wt < X
  wA : (Val.list ((1 :: gs).map encPerm)).wt < (encGroup gs).wt
  wB : (Val.list ((1 :: ns).map encPerm)).wt < (encGroup ns).wt
  we1 : (encPerm (1 : Perm (Fin n))).wt < (Val.list ((1 :: gs).map encPerm)).wt
  hn : n < (encPerm (1 : Perm (Fin n))).wt
  hAl : ((1 :: gs).map encPerm).length < (Val.list ((1 :: gs).map encPerm)).wt
  hBl : ((1 :: ns).map encPerm).length < (Val.list ((1 :: ns).map encPerm)).wt
  wn : (Val.nat n).wt ≤ n + 2

theorem nintInterW_of {n : ℕ} (gs ns : List (Perm (Fin n))) :
    NIntInterW gs ns (Val.list [encGroup gs, encGroup ns]).wt where
  wG := by
    have := sum_wt_lt_wt_list [encGroup gs, encGroup ns]
    simp at this; omega
  wA := wt_le_wt_list (by simp [encGroup, encPerms])
  wB := wt_le_wt_list (by simp [encGroup, encPerms])
  we1 := wt_le_wt_list (by simp)
  hn := by
    have := length_lt_wt_list ((List.finRange n).map fun i => Val.nat ((1 : Perm (Fin n)) i))
    simpa [encPerm] using this
  hAl := length_lt_wt_list _
  hBl := length_lt_wt_list _
  wn := wt_nat_le n

section Spec

variable (hp : PointwiseStab) {n : ℕ} (gs ns : List (Perm (Fin n)))

theorem nintInter_d1 {X : ℕ} (hX : (Val.list [encGroup gs, encGroup ns]).wt = X) (hw : NIntInterW gs ns X) :
    Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns])] (.get (arg 0) (.nat 0)) (.nat n) (10 * (X + 1)) := by
  refine (Det.encPerms_size (gs := 1 :: gs) (Det.arg' (P := nintInterProgram hp)
    (vs := [encGroup gs, encGroup ns]) (rest := []) (j := 0) rfl)).mono ?_
  have := hw.wG; have := hw.wn; have := hw.hn; have := hw.we1; have := hw.wA
  omega

theorem nintInter_d2 {X : ℕ} (hX : (Val.list [encGroup gs, encGroup ns]).wt = X) (hw : NIntInterW gs ns X) :
    Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n] (.get (.get (arg 0) (.nat 1)) (.nat 0)) (encPerm (1 : Perm (Fin n)))
      (20 * (X + 1)) := by
  have h2 := Det.getPerm (gs := 1 :: gs) (t := 0) (by simp)
    (Det.encPerms_gens (gs := 1 :: gs) (Det.arg' (P := nintInterProgram hp)
      (vs := [encGroup gs, encGroup ns]) (rest := [.nat n]) (j := 0) rfl)) (Det.nat 0)
  refine h2.mono ?_
  have := hw.wG; have := hw.wA; have := hw.we1
  simp only [List.getElem_cons_zero]
  omega

/-- `g ↦ g ⊕ g`. -/
theorem nintInter_dbl_spec {n : ℕ} (g : Perm (Fin n)) :
    FunDet (nintInterProgram hp) 9 (.list [.nat n, encPerm g]) (encPerm (nintSum (g, g)))
      (10 ^ 9 * (n + 1) ^ 3) := by
  have g0 := Det.arg' (P := nintInterProgram hp) (vs := [.nat n, encPerm g]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := nintInterProgram hp) (vs := [.nat n, encPerm g]) (rest := []) (j := 1) rfl
  refine FunDet.intro (nintInter_dbl hp) ((Det.call (Det.mk3 g1 g1 g0)
    (nintInter_shift_spec hp g g)).mono ?_)
  have w1 := wt_encPerm_le g
  have w2 := wt_encPerm_le (nintSum (g, g))
  have w3 := wt_list2_le (.nat n) (encPerm g)
  have w4 := wt_list3_le (encPerm g) (encPerm g) (.nat n)
  have w5 := wt_nat_le n
  have p1 := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 3
  have p2 := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 2
  have q1 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := nint_pow_mono (by omega) (by norm_num)
  change (encPerm (sumToFin (Perm.sumCongr g g))).wt ≤ _ at w2
  unfold shiftK
  omega

/-- `m ↦ 1 ⊕ m`. -/
theorem nintInter_pr_spec {n : ℕ} (m : Perm (Fin n)) :
    FunDet (nintInterProgram hp) 13 (.list [.list [encPerm (1 : Perm (Fin n)), .nat n], encPerm m])
      (encPerm (nintSum (1, m))) (10 ^ 9 * (n + 1) ^ 3) := by
  have g0 := Det.arg' (P := nintInterProgram hp)
    (vs := [.list [encPerm (1 : Perm (Fin n)), .nat n], encPerm m]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := nintInterProgram hp)
    (vs := [.list [encPerm (1 : Perm (Fin n)), .nat n], encPerm m]) (rest := []) (j := 1) rfl
  have ge := Det.get' g0 (Det.nat 0) (v := encPerm (1 : Perm (Fin n))) rfl
  have gn := Det.get' g0 (Det.nat 1) (v := .nat n) rfl
  refine FunDet.intro (nintInter_pr hp) ((Det.call (Det.mk3 ge g1 gn)
    (nintInter_shift_spec hp 1 m)).mono ?_)
  have w0 := wt_encPerm_le (1 : Perm (Fin n))
  have w1 := wt_encPerm_le m
  have w2 := wt_encPerm_le (nintSum (1, m))
  have w3 := wt_list2_le (.list [encPerm (1 : Perm (Fin n)), .nat n]) (encPerm m)
  have w3' := wt_list2_le (encPerm (1 : Perm (Fin n))) (.nat n)
  have w4 := wt_list3_le (encPerm (1 : Perm (Fin n))) (encPerm m) (.nat n)
  have w5 := wt_nat_le n
  have p1 := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 3
  have p2 := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 2
  have q1 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 := nint_pow_mono (by omega) (by norm_num)
  change (encPerm (sumToFin (Perm.sumCongr (1 : Perm (Fin n)) m))).wt ≤ _ at w2
  unfold shiftK
  omega

/-- Step 3: the generators of `K`. -/
theorem nintInter_d3 {X : ℕ} (hX : (Val.list [encGroup gs, encGroup ns]).wt = X) (hw : NIntInterW gs ns X) :
    Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n, (encPerm (1 : Perm (Fin n)))]
      (.call 2 (mk2 (.call 10 (mk2 (.var 1) (.get (arg 0) (.nat 1))))
        (.call 14 (mk2 (mk2 (.var 2) (.var 1)) (.get (arg 1) (.nat 1))))))
      (.list (((1 :: gs).map (fun g => encPerm (nintSum (g, g)))) ++ ((1 :: ns).map (fun m => encPerm (nintSum (1, m)))))) (10 ^ 12 * (X + 1) ^ 6) := by
  have := hw.wG; have := hw.wA; have := hw.wB; have := hw.we1; have := hw.hn; have := hw.wn
  have := hw.hAl; have := hw.hBl
  have hv1 : Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n, (encPerm (1 : Perm (Fin n)))] (.var 1) (.nat n) _ := Det.var' rfl
  have hv2 : Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n, (encPerm (1 : Perm (Fin n)))] (.var 2) (encPerm (1 : Perm (Fin n))) _ := Det.var' rfl
  have hA := Det.encPerms_gens (gs := 1 :: gs) (Det.arg' (P := nintInterProgram hp)
    (vs := [encGroup gs, encGroup ns]) (rest := [.nat n, (encPerm (1 : Perm (Fin n)))]) (j := 0) rfl)
  have hB := Det.encPerms_gens (gs := 1 :: ns) (Det.arg' (P := nintInterProgram hp)
    (vs := [encGroup gs, encGroup ns]) (rest := [.nat n, (encPerm (1 : Perm (Fin n)))]) (j := 1) rfl)
  have inj : ∀ (f : Perm (Fin n) → Val) (l : List (Perm (Fin n))), ∀ a ∈ l, ∀ a' ∈ l,
      encPerm a = encPerm a' → f a = f a' := fun f l a _ a' _ h => by
    rw [nint_encPerm_injective h]
  have md := mapList_spec (nintInter_dblMap hp) (1 :: gs) encPerm (fun g => encPerm (nintSum (g, g)))
    (c := .nat n) (inj _ _) (fun g _ => nintInter_dbl_spec hp g)
  have mp := mapList_spec (nintInter_prMap hp) (1 :: ns) encPerm (fun m => encPerm (nintSum (1, m)))
    (c := .list [(encPerm (1 : Perm (Fin n))), .nat n]) (inj _ _) (fun m _ => nintInter_pr_spec hp m)
  refine (Det.call (Det.mk2 (Det.call (Det.mk2 hv1 hA) md) (Det.call (Det.mk2 (Det.mk2 hv2 hv1) hB) mp))
    (nint_append (nintInter_append hp) ((1 :: gs).map (fun g => encPerm (nintSum (g, g)))) ((1 :: ns).map (fun m => encPerm (nintSum (1, m)))))).mono ?_
  -- weights of the two lists
  have wd : (Val.list ((1 :: gs).map (fun g => encPerm (nintSum (g, g))))).wt ≤ (1 :: gs).length * (2 * (16 * (n + 1) ^ 2) + 1) + 4 :=
    wt_list_map_le _ _ fun g _ => by
      have := wt_encPerm_le (nintSum (g, g))
      have := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 2
      omega
  have wp : (Val.list ((1 :: ns).map (fun m => encPerm (nintSum (1, m))))).wt ≤ (1 :: ns).length * (2 * (16 * (n + 1) ^ 2) + 1) + 4 :=
    wt_list_map_le _ _ fun m _ => by
      have := wt_encPerm_le (nintSum (1, m))
      have := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 2
      omega
  simp only [List.length_map] at *
  have hn2 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hn3 : (n + 1) ^ 3 ≤ (X + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hn1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have la : (1 :: gs).length * (2 * (16 * (n + 1) ^ 2) + 1) ≤ 33 * (X + 1) ^ 3 := by
    have : (1 :: gs).length * (2 * (16 * (n + 1) ^ 2) + 1) ≤ (X + 1) * (33 * (X + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (X + 1) * (33 * (X + 1) ^ 2) = 33 * (X + 1) ^ 3 := by ring
    omega
  have lb : (1 :: ns).length * (2 * (16 * (n + 1) ^ 2) + 1) ≤ 33 * (X + 1) ^ 3 := by
    have : (1 :: ns).length * (2 * (16 * (n + 1) ^ 2) + 1) ≤ (X + 1) * (33 * (X + 1) ^ 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (X + 1) * (33 * (X + 1) ^ 2) = 33 * (X + 1) ^ 3 := by ring
    omega
  have ca : (1 :: gs).length * (10 ^ 9 * (n + 1) ^ 3) ≤ 10 ^ 9 * (X + 1) ^ 4 := by
    have : (1 :: gs).length * (10 ^ 9 * (n + 1) ^ 3) ≤ (X + 1) * (10 ^ 9 * (X + 1) ^ 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (X + 1) * (10 ^ 9 * (X + 1) ^ 3) = 10 ^ 9 * (X + 1) ^ 4 := by ring
    omega
  have cb : (1 :: ns).length * (10 ^ 9 * (n + 1) ^ 3) ≤ 10 ^ 9 * (X + 1) ^ 4 := by
    have : (1 :: ns).length * (10 ^ 9 * (n + 1) ^ 3) ≤ (X + 1) * (10 ^ 9 * (X + 1) ^ 3) :=
      Nat.mul_le_mul (by omega) (by omega)
    have e : (X + 1) * (10 ^ 9 * (X + 1) ^ 3) = 10 ^ 9 * (X + 1) ^ 4 := by ring
    omega
  have w6 := wt_list2_le (.nat n) (.list ((1 :: gs).map encPerm))
  have w7 := wt_list2_le (.list [(encPerm (1 : Perm (Fin n))), .nat n]) (.list ((1 :: ns).map encPerm))
  have w7' := wt_list2_le (encPerm (1 : Perm (Fin n))) (.nat n)
  have w8 := wt_list2_le (.list ((1 :: gs).map (fun g => encPerm (nintSum (g, g))))) (.list ((1 :: ns).map (fun m => encPerm (nintSum (1, m)))))
  have w9 := nint_wt_append ((1 :: gs).map (fun g => encPerm (nintSum (g, g)))) ((1 :: ns).map (fun m => encPerm (nintSum (1, m))))
  have q1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := nint_pow_mono (by omega) (by norm_num)
  have q3 : (X + 1) ^ 3 ≤ (X + 1) ^ 4 := nint_pow_mono (by omega) (by norm_num)
  have q4 : (X + 1) ^ 4 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by norm_num)
  have ma : mapK * ((1 :: gs).length + 1) * ((Val.list [.nat n, .list ((1 :: gs).map encPerm)]).wt + (Val.list ((1 :: gs).map (fun g => encPerm (nintSum (g, g))))).wt + 1)
      ≤ mapK * (X + 2) * (100 * (X + 1) ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have mb : mapK * ((1 :: ns).length + 1) *
      ((Val.list [.list [(encPerm (1 : Perm (Fin n))), .nat n], .list ((1 :: ns).map encPerm)]).wt + (Val.list ((1 :: ns).map (fun m => encPerm (nintSum (1, m))))).wt + 1)
      ≤ mapK * (X + 2) * (100 * (X + 1) ^ 3) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have e1 : mapK * (X + 2) * (100 * (X + 1) ^ 3) ≤ 200000 * (X + 1) ^ 4 := by
    have : mapK * (X + 2) * (100 * (X + 1) ^ 3) ≤ 1000 * (2 * (X + 1)) * (100 * (X + 1) ^ 3) :=
      Nat.mul_le_mul (by unfold mapK; omega) le_rfl
    have e : 1000 * (2 * (X + 1)) * (100 * (X + 1) ^ 3) = 200000 * (X + 1) ^ 4 := by ring
    omega
  have p := nint_pow_le (W := (Val.list [.list ((1 :: gs).map (fun g => encPerm (nintSum (g, g)))), .list ((1 :: ns).map (fun m => encPerm (nintSum (1, m))))]).wt) (c := 200) (Y := (X + 1) ^ 3)
    (by omega) 2
  have e2 : ((X + 1) ^ 3) ^ 2 = (X + 1) ^ 6 := by rw [← pow_mul]
  rw [e2] at p
  omega

/-- Step 4: the argument of the first stabilizer call. -/
theorem nintInter_d4 {X : ℕ} (hX : (Val.list [encGroup gs, encGroup ns]).wt = X) (hw : NIntInterW gs ns X) :
    Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n, (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map (fun g => encPerm (nintSum (g, g)))) ++ ((1 :: ns).map (fun m => encPerm (nintSum (1, m)))))]
      (mk2 (mk2 (.arith .add (.var 1) (.var 1)) (.var 3)) (.call 5 (mk2 (.var 1) (.call 17 (.var 1)))))
      (.list [encGroup (nintKGens gs ns), encPts (nintPts n)]) (10 ^ 14 * (X + 1) ^ 6) := by
  have := hw.wG; have := hw.wA; have := hw.we1; have := hw.hn; have := hw.wn
  have wK : (Val.list (((1 :: gs).map (fun g => encPerm (nintSum (g, g)))) ++ ((1 :: ns).map (fun m => encPerm (nintSum (1, m)))))).wt < 10 ^ 12 * (X + 1) ^ 6 := (nintInter_d3 hp gs ns hX hw).wt_lt
  rw [nint_encGroup_K, nint_encPts]
  have hv1 : Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n, (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map (fun g => encPerm (nintSum (g, g)))) ++ ((1 :: ns).map (fun m => encPerm (nintSum (1, m)))))] (.var 1) (.nat n) _ :=
    Det.var' rfl
  have hv3 : Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n, (encPerm (1 : Perm (Fin n))), .list (((1 :: gs).map (fun g => encPerm (nintSum (g, g)))) ++ ((1 :: ns).map (fun m => encPerm (nintSum (1, m)))))] (.var 3)
    (.list (((1 :: gs).map (fun g => encPerm (nintSum (g, g)))) ++ ((1 :: ns).map (fun m => encPerm (nintSum (1, m)))))) _ := Det.var' rfl
  have hadd := Det.arith' (op := .add) hv1 hv1 (z := n + n) (by simp only [GI.Machine.BinOp.eval])
  have hr : FunDet (nintInterProgram hp) 17 (.nat n) (natList (List.range n))
      (loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1)) :=
    (range_spec (nintInter_range hp) n).mono fun w c ⟨hw, hc⟩ => ⟨hw, hw ▸ hc⟩
  have hm := mapList_spec (nintInter_addMap hp) (List.range n) Val.nat (fun j => .nat (n + j))
    (c := .nat n) (B := 100 * (n + 1)) (fun j _ j' _ h => by
      simp only [Val.nat.injEq] at h ⊢; omega) (fun j hj => by
      have hj' := List.mem_range.mp hj
      have g0 := Det.arg' (P := nintInterProgram hp) (vs := [.nat n, .nat j]) (rest := []) (j := 0) rfl
      have g1 := Det.arg' (P := nintInterProgram hp) (vs := [.nat n, .nat j]) (rest := []) (j := 1) rfl
      refine FunDet.intro (nintInter_addK hp) ((Det.arith' (op := .add) g1 g0 (z := n + j)
        (by simp only [GI.Machine.BinOp.eval]; omega)).mono ?_)
      have := wt_list2_le (.nat n) (.nat j)
      have := wt_nat_le n
      have := wt_nat_le j
      omega)
  refine (Det.mk2 (Det.mk2 hadd hv3) (Det.call (Det.mk2 hv1 (Det.call hv1 hr)) hm)).mono ?_
  have e1 : natList (List.range n) = (encPerm (1 : Perm (Fin n))) := range_eq_encPerm_one
  have e1' : (natList (List.range n)).wt = (encPerm (1 : Perm (Fin n))).wt := by rw [e1]
  have e1'' : (Val.list ((List.range n).map Val.nat)).wt = (encPerm (1 : Perm (Fin n))).wt := e1'
  have w1 := wt_encPerm_le (1 : Perm (Fin n))
  have w2 : (Val.list ((List.range n).map fun j => Val.nat (n + j))).wt ≤
      (List.range n).length * (2 * (2 * n + 2) + 1) + 4 :=
    wt_list_map_le _ _ fun j hj => by
      have := List.mem_range.mp hj; have := wt_nat_le (n + j); omega
  simp only [List.length_range] at w2
  have w3 := wt_list2_le (.nat n) (encPerm (1 : Perm (Fin n)))
  have w3' := wt_list2_le (.nat n) (.list ((List.range n).map Val.nat))
  have w3'' := wt_list2_le (.nat n) (natList (List.range n))
  have w4 := wt_list2_le (.nat (n + n)) (.list (((1 :: gs).map (fun g => encPerm (nintSum (g, g)))) ++ ((1 :: ns).map (fun m => encPerm (nintSum (1, m))))))
  have w5 := wt_list2_le (.list [.nat (n + n), .list (((1 :: gs).map (fun g => encPerm (nintSum (g, g)))) ++ ((1 :: ns).map (fun m => encPerm (nintSum (1, m)))))])
    (.list ((List.range n).map fun j => Val.nat (n + j)))
  have w6 := wt_nat_le (n + n)
  have hn2 : (n + 1) ^ 2 ≤ (X + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q1 : X + 1 ≤ (X + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (X + 1) ^ 2 ≤ (X + 1) ^ 3 := nint_pow_mono (by omega) (by norm_num)
  have q3 : (X + 1) ^ 3 ≤ (X + 1) ^ 6 := nint_pow_mono (by omega) (by norm_num)
  have b1 : n * (2 * (2 * n + 2) + 1) ≤ 5 * (X + 1) ^ 2 := by
    have : n * (2 * (2 * n + 2) + 1) ≤ (X + 1) * (5 * (X + 1)) := Nat.mul_le_mul (by omega) (by omega)
    have e : (X + 1) * (5 * (X + 1)) = 5 * (X + 1) ^ 2 := by ring
    omega
  have b2 : n * (100 * (n + 1)) ≤ 100 * (X + 1) ^ 2 := by
    have : n * (100 * (n + 1)) ≤ (X + 1) * (100 * (X + 1)) := Nat.mul_le_mul (by omega) (by omega)
    have e : (X + 1) * (100 * (X + 1)) = 100 * (X + 1) ^ 2 := by ring
    omega
  have b3 : loopModK * (n + 1) * ((Val.nat n).wt + n + (natList (List.range n)).wt + 1) ≤ 1000 * (X + 1) * (20 * (X + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul (by unfold loopModK; omega) (by omega)) (by omega)
  have b4 : mapK * ((List.range n).length + 1) * ((Val.list [.nat n, .list ((List.range n).map Val.nat)]).wt +
      (Val.list ((List.range n).map fun j => Val.nat (n + j))).wt + 1) ≤
      1000 * (X + 1) * (30 * (X + 1) ^ 2) := by
    simp only [List.length_range]
    exact Nat.mul_le_mul (Nat.mul_le_mul (by unfold mapK; omega) (by omega)) (by omega)
  have e3 : 1000 * (X + 1) * (20 * (X + 1) ^ 2) = 20000 * (X + 1) ^ 3 := by ring
  have e4 : 1000 * (X + 1) * (30 * (X + 1) ^ 2) = 30000 * (X + 1) ^ 3 := by ring
  simp only [List.length_range] at *
  omega

/-- The restriction `a ⊕ 1 ↦ a`: the first `n` entries. -/
theorem nintInter_restr_spec {n : ℕ} (a : Perm (Fin n)) :
    FunDet (nintInterProgram hp) 20 (.list [.nat n, encPerm (nintSum (a, 1))]) (encPerm a)
      (10 ^ 10 * (n + 1) ^ 6) := by
  have hb : (Val.list [.nat n, encPerm (nintSum (a, 1))]).wt + 1 ≤ 50 * (n + 1) ^ 2 := by
    have := wt_encPerm_le (nintSum (a, 1))
    have := wt_list2_le (.nat n) (encPerm (nintSum (a, 1)))
    have := wt_nat_le n
    have := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 2
    have : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  rw [nint_encPerm_sum_take] at hb ⊢
  have ht := linTake_spec (nintInter_take hp) ((List.finRange n).map (fun i => Val.nat (a i)) ++
      (List.finRange n).map (fun j => Val.nat (n + (1 : Perm (Fin n)) j))) n (by simp)
  rw [List.take_left' (by simp)] at ht
  refine ht.mono ?_
  have p3 := nint_pow_le (W := (Val.list [.nat n, .list ((List.finRange n).map (fun i => Val.nat (a i)) ++
      (List.finRange n).map (fun j => Val.nat (n + (1 : Perm (Fin n)) j)))]).wt) (c := 50)
    (Y := (n + 1) ^ 2) hb 3
  have e : ((n + 1) ^ 2) ^ 3 = (n + 1) ^ 6 := by rw [← pow_mul]
  rw [e] at p3
  unfold linTakeCost
  omega

/-- Step 5: the restrictions of the stabilizer generators. -/
theorem nintInter_d5 {X : ℕ} (hX : (Val.list [encGroup gs, encGroup ns]).wt = X) (hw : NIntInterW gs ns X) (Kv : Val)
    (as : List (Perm (Fin n))) (hl : as.length ≤ (n + n) ^ 2)
    (hwh : (Val.list (as.map fun a => encPerm (nintSum (a, 1)))).wt ≤ 13 * (n + n + 1) ^ 6) :
    Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n, (encPerm (1 : Perm (Fin n))), Kv, .list (as.map fun a => encPerm (nintSum (a, 1)))]
      (.call 23 (mk2 (.var 1) (.var 4))) (.list (as.map encPerm)) (10 ^ 12 * (X + 1) ^ 8) := by
  have := hw.wG; have := hw.wA; have := hw.we1; have := hw.hn; have := hw.wn
  have hv1 : Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n, (encPerm (1 : Perm (Fin n))), Kv,
    .list (as.map fun a => encPerm (nintSum (a, 1)))] (.var 1) (.nat n) _ := Det.var' rfl
  have hv4 : Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n, (encPerm (1 : Perm (Fin n))), Kv,
    .list (as.map fun a => encPerm (nintSum (a, 1)))] (.var 4)
    (.list (as.map fun a => encPerm (nintSum (a, 1)))) _ := Det.var' rfl
  have hm := mapList_spec (nintInter_takeMap hp) as (fun a => encPerm (nintSum (a, 1))) encPerm
    (c := .nat n) (fun a _ a' _ h => by
      have := nintSum_injective (nint_encPerm_injective h)
      simp only [Prod.mk.injEq, and_true] at this
      rw [this]) (fun a _ => nintInter_restr_spec hp a)
  refine (Det.call (Det.mk2 hv1 hv4) hm).mono ?_
  have wo : (Val.list (as.map encPerm)).wt ≤ as.length * (2 * (4 * (n + 1) ^ 2) + 1) + 4 :=
    wt_list_map_le _ _ fun a _ => wt_encPerm_le a
  have hl' : as.length ≤ 4 * (n + 1) ^ 2 := by
    have : (n + n) ^ 2 ≤ (2 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    rw [mul_pow] at this; omega
  have p6 := nint_pow_le (W := n + n) (c := 2) (Y := n + 1) (by omega) 6
  have q1 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q2 : (n + 1) ^ 2 ≤ (n + 1) ^ 4 := nint_pow_mono (by omega) (by norm_num)
  have q3 : (n + 1) ^ 4 ≤ (n + 1) ^ 6 := nint_pow_mono (by omega) (by norm_num)
  have q4 : (n + 1) ^ 6 ≤ (n + 1) ^ 8 := nint_pow_mono (by omega) (by norm_num)
  have hX8 : (n + 1) ^ 8 ≤ (X + 1) ^ 8 := Nat.pow_le_pow_left (by omega) 8
  have b1 : as.length * (2 * (4 * (n + 1) ^ 2) + 1) ≤ 36 * (n + 1) ^ 4 := by
    have : as.length * (2 * (4 * (n + 1) ^ 2) + 1) ≤ (4 * (n + 1) ^ 2) * (9 * (n + 1) ^ 2) :=
      Nat.mul_le_mul hl' (by omega)
    have e : (4 * (n + 1) ^ 2) * (9 * (n + 1) ^ 2) = 36 * (n + 1) ^ 4 := by ring
    omega
  have b2 : as.length * (10 ^ 10 * (n + 1) ^ 6) ≤ 4 * 10 ^ 10 * (n + 1) ^ 8 := by
    have : as.length * (10 ^ 10 * (n + 1) ^ 6) ≤ (4 * (n + 1) ^ 2) * (10 ^ 10 * (n + 1) ^ 6) :=
      Nat.mul_le_mul hl' le_rfl
    have e : (4 * (n + 1) ^ 2) * (10 ^ 10 * (n + 1) ^ 6) = 4 * 10 ^ 10 * (n + 1) ^ 8 := by ring
    omega
  have w2 := wt_list2_le (.nat n) (.list (as.map fun a => encPerm (nintSum (a, 1))))
  have w3 := wt_nat_le n
  have b3 : mapK * (as.length + 1) * ((Val.list [.nat n, .list (as.map fun a =>
      encPerm (nintSum (a, 1)))]).wt + (Val.list (as.map encPerm)).wt + 1) ≤
      1000 * (5 * (n + 1) ^ 2) * (2000 * (n + 1) ^ 6) :=
    Nat.mul_le_mul (Nat.mul_le_mul (by unfold mapK; omega) (by omega)) (by omega)
  have e3 : 1000 * (5 * (n + 1) ^ 2) * (2000 * (n + 1) ^ 6) = 10 ^ 7 * (n + 1) ^ 8 := by ring
  omega

/-- Step 6: the argument of the second stabilizer call. -/
theorem nintInter_d6 {X : ℕ} (hX : (Val.list [encGroup gs, encGroup ns]).wt = X) (hw : NIntInterW gs ns X) (Kv hv : Val)
    (as : List (Perm (Fin n))) (hl : as.length ≤ (n + n) ^ 2) :
    Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n, (encPerm (1 : Perm (Fin n))), Kv, hv, .list (as.map encPerm)]
      (mk2 (mk2 (.var 1) (.call 2 (mk2 (mk1 (.var 2)) (.var 5)))) .nil)
      (.list [encGroup as, encPts ([] : List (Fin n))]) (10 ^ 14 * (X + 1) ^ 8) := by
  have := hw.wG; have := hw.wA; have := hw.we1; have := hw.hn; have := hw.wn
  have e : (Val.list [encGroup as, encPts ([] : List (Fin n))]) =
      .list [.list [.nat n, .list ([(encPerm (1 : Perm (Fin n)))] ++ as.map encPerm)], .list []] := rfl
  rw [e]
  have hv1 : Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n, (encPerm (1 : Perm (Fin n))), Kv, hv, .list (as.map encPerm)] (.var 1)
    (.nat n) _ := Det.var' rfl
  have hv2 : Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n, (encPerm (1 : Perm (Fin n))), Kv, hv, .list (as.map encPerm)] (.var 2)
    (encPerm (1 : Perm (Fin n))) _ := Det.var' rfl
  have hv5 : Det (nintInterProgram hp) [(Val.list [encGroup gs, encGroup ns]), .nat n, (encPerm (1 : Perm (Fin n))), Kv, hv, .list (as.map encPerm)] (.var 5)
    (.list (as.map encPerm)) _ := Det.var' rfl
  refine (Det.mk2 (Det.mk2 hv1 (Det.call (Det.mk2 (Det.mk1 hv2) hv5)
    (nint_append (nintInter_append hp) [(encPerm (1 : Perm (Fin n)))] (as.map encPerm)))) Det.nil).mono ?_
  have wo : (Val.list (as.map encPerm)).wt ≤ as.length * (2 * (4 * (n + 1) ^ 2) + 1) + 4 :=
    wt_list_map_le _ _ fun a _ => wt_encPerm_le a
  have hl' : as.length ≤ 4 * (n + 1) ^ 2 := by
    have : (n + n) ^ 2 ≤ (2 * (n + 1)) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    rw [mul_pow] at this; omega
  have q1 : n + 1 ≤ (n + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have b1 : as.length * (2 * (4 * (n + 1) ^ 2) + 1) ≤ 36 * (n + 1) ^ 4 := by
    have : as.length * (2 * (4 * (n + 1) ^ 2) + 1) ≤ (4 * (n + 1) ^ 2) * (9 * (n + 1) ^ 2) :=
      Nat.mul_le_mul hl' (by omega)
    have e : (4 * (n + 1) ^ 2) * (9 * (n + 1) ^ 2) = 36 * (n + 1) ^ 4 := by ring
    omega
  have hX4 : (n + 1) ^ 4 ≤ (X + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
  have r1 : X + 1 ≤ (X + 1) ^ 4 := Nat.le_self_pow (by norm_num) _
  have r2 : (X + 1) ^ 4 ≤ (X + 1) ^ 8 := nint_pow_mono (by omega) (by norm_num)
  have w1 := wt_list1_le (encPerm (1 : Perm (Fin n)))
  have w2 := wt_list2_le (.list [(encPerm (1 : Perm (Fin n)))]) (.list (as.map encPerm))
  have w3 := nint_wt_append [(encPerm (1 : Perm (Fin n)))] (as.map encPerm)
  have w4 := wt_list2_le (.nat n) (.list ([(encPerm (1 : Perm (Fin n)))] ++ as.map encPerm))
  have w5 := wt_list2_le (.list [.nat n, .list ([(encPerm (1 : Perm (Fin n)))] ++ as.map encPerm)]) (.list [])
  have w6 := wt_nat_le n
  have p := nint_pow_le (W := (Val.list [.list [(encPerm (1 : Perm (Fin n)))], .list (as.map encPerm)]).wt) (c := 200)
    (Y := (X + 1) ^ 4) (by omega) 2
  have e2 : ((X + 1) ^ 4) ^ 2 = (X + 1) ^ 8 := by rw [← pow_mul]
  rw [e2] at p
  simp only [wt_list_nil] at *
  omega

end Spec

theorem nint_pointwiseStab_nil {n : ℕ} (G : Subgroup (Perm (Fin n))) : pointwiseStab G [] = G := by
  ext g; simp [pointwiseStab]

/-- **The cost of the intersection program** on an input of weight `X`. -/
noncomputable def nintInterCost (hp : PointwiseStab) (X : ℕ) : ℕ :=
  10 ^ 16 * (X + 1) ^ 8 + (pointwiseStabPrim hp).boundSize (10 ^ 14 * (X + 1) ^ 6) +
    (pointwiseStabPrim hp).boundSize (10 ^ 14 * (X + 1) ^ 8)

theorem nintInterCost_poly (hp : PointwiseStab) : PBU (fun _ X _ => nintInterCost hp X) := by
  unfold nintInterCost Prim.boundSize
  norm_poly

/-- **The intersection program is correct, at cost `nintInterCost`.** -/
theorem nintInter_spec (hp : PointwiseStab) (I : NormalizedInst) :
    FunAll (nintInterProgram hp) 0 (.list [encGroup I.gs, encGroup I.ns])
      (fun v c => GensOf (gens I.gs ⊓ gens I.ns) v ∧
        c ≤ nintInterCost hp (Val.list [encGroup I.gs, encGroup I.ns]).wt) := by
  obtain ⟨n, gs, ns, hnorm⟩ := I
  dsimp only
  have hw := nintInterW_of gs ns
  obtain ⟨X, hX⟩ : ∃ X, (Val.list [encGroup gs, encGroup ns]).wt = X := ⟨_, rfl⟩
  rw [hX] at hw ⊢
  have hnormal : gens (1 :: gs) ≤ Subgroup.normalizer (gens (1 :: ns) : Set (Perm (Fin n))) := by
    rw [nint_gens_cons_one, nint_gens_cons_one]; exact nint_normalizer hnorm
  have d1 := nintInter_d1 hp gs ns hX hw
  have d2 := nintInter_d2 hp gs ns hX hw
  have d3 := nintInter_d3 hp gs ns hX hw
  have d4 := nintInter_d4 hp gs ns hX hw
  have wd4 := d4.wt_lt
  have c1 := pointwiseStab_call hp (nintInter_prim hp) d4 (G := gens (nintKGens gs ns)) ⟨_, rfl, rfl⟩
  apply FunAll.intro (nintInter_entry hp)
  refine EvalAll.letE d1 fun v1 k1 h1 => ?_
  obtain ⟨rfl, hk1⟩ := h1
  refine EvalAll.letE d2 fun v2 k2 h2 => ?_
  obtain ⟨rfl, hk2⟩ := h2
  refine EvalAll.letE d3 fun v3 k3 h3 => ?_
  obtain ⟨rfl, hk3⟩ := h3
  refine EvalAll.letE c1 fun w kw hw' => ?_
  have hwb := GensVal.wt_le hw'.1
  obtain ⟨⟨hs, rfl, hl, hgen⟩, hkw⟩ := hw'
  rw [← nint_gens_K] at hgen
  obtain ⟨as, rfl, has⟩ := nint_inter hnormal hgen
  have e : (as.map fun a => nintSum (a, 1)).map encPerm = as.map fun a => encPerm (nintSum (a, 1)) := by
    rw [List.map_map]; rfl
  rw [e] at hwb ⊢
  have hl' : as.length ≤ (n + n) ^ 2 := by simpa using hl
  have d5 := nintInter_d5 hp gs ns hX hw (.list (((1 :: gs).map (fun g => encPerm (nintSum (g, g)))) ++ ((1 :: ns).map (fun m => encPerm (nintSum (1, m)))))) as hl' hwb
  refine EvalAll.letE d5 fun v5 k5 h5 => ?_
  obtain ⟨rfl, hk5⟩ := h5
  have d6 := nintInter_d6 hp gs ns hX hw (.list (((1 :: gs).map (fun g => encPerm (nintSum (g, g)))) ++ ((1 :: ns).map (fun m => encPerm (nintSum (1, m))))))
    (.list (as.map fun a => encPerm (nintSum (a, 1)))) as hl'
  have wd6 := d6.wt_lt
  have c2 := pointwiseStab_call hp (nintInter_prim hp) d6 (G := gens as) ⟨_, rfl, rfl⟩
  refine c2.mono fun w c hc => ⟨?_, ?_⟩
  · have h : GensOf (pointwiseStab (gens as) []) w := hc.1
    rwa [nint_pointwiseStab_nil, has, nint_gens_cons_one, nint_gens_cons_one] at h
  · have hwo := GensVal.wt_le hc.1
    have hc2 := hc.2
    have b1 : (pointwiseStabPrim hp).bound (.list [encGroup (nintKGens gs ns), encPts (nintPts n)]) ≤
        (pointwiseStabPrim hp).boundSize (10 ^ 14 * (X + 1) ^ 6) :=
      Prim.bound_le _ (by have := Val.size_le_wt (.list [encGroup (nintKGens gs ns), encPts (nintPts n)]); omega)
    have b2 : (pointwiseStabPrim hp).bound (.list [encGroup as, encPts ([] : List (Fin n))]) ≤
        (pointwiseStabPrim hp).boundSize (10 ^ 14 * (X + 1) ^ 8) :=
      Prim.bound_le _ (by have := Val.size_le_wt (.list [encGroup as, encPts ([] : List (Fin n))]); omega)
    have := hw.wG; have := hw.wA; have := hw.we1; have := hw.hn
    have p6 := nint_pow_le (W := n + n) (c := 2) (Y := X + 1) (by omega) 6
    have p6' : (n + 1) ^ 6 ≤ (X + 1) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    have q1 : X + 1 ≤ (X + 1) ^ 6 := Nat.le_self_pow (by norm_num) _
    have q2 : (X + 1) ^ 6 ≤ (X + 1) ^ 8 := nint_pow_mono (by omega) (by norm_num)
    unfold nintInterCost
    omega

/-- The cells of the intersection input. -/
theorem nint_inter_cells (I : NormalizedInst) :
    ∀ a ∈ (Val.list [encGroup I.gs, encGroup I.ns]).cells,
      a ≤ 1 * ((Val.list [encGroup I.gs, encGroup I.ns]).size + 1) ^ 1 :=
  nint_cells_bound (nint_cells_list (by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact nint_cells_group _
    · exact nint_cells_group _))

/-- **Intersection with a normalized subgroup, from the pointwise stabilizer** ([LM, Theorem
3.1(viii)(b)]). -/
theorem nint_normalizedIntersection (hp : PointwiseStab) : NormalizedIntersection := by
  obtain ⟨K, D, hK⟩ := nint_poly_bound (nintInterCost_poly hp)
  exact polyTimeAt_ofVal_of_lang_cells (nintInterProgram hp) 0 K D 1 1 nint_inter_cells
    fun I => (nintInter_spec hp I).mono fun v c h => ⟨h.1, h.2.trans (hK _)⟩

end GI.Impl
