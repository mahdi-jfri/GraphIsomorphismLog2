module

public import Workspace.Impl.GMPConjTableCost
public import Workspace.Impl.NClPreMath

@[expose] public section

/-! # Encoding a graph permutation on two disjoint point sets -/

namespace GI.Impl

open GI.Lang GI.Cited Equiv

/-- The disjoint union encoding concatenates the first row with an offset second row. -/
theorem gmpSumPerm_enc {n m : ℕ} (g : Perm (Fin n)) (h : Perm (Fin m)) :
    encPerm (sumToFin (sumCongr g h)) =
      .list (((List.finRange n).map fun i => Val.nat (g i)) ++
        ((List.finRange m).map fun i => Val.nat (n + (h i : ℕ)))) := by
  unfold encPerm
  congr 1
  simp only [List.finRange, List.map_ofFn, List.ofFn_add, List.map_append]
  congr 1
  · apply congrArg List.ofFn
    funext i
    exact congrArg (fun x : Fin (n + m) => Val.nat x.val)
      (nclSumToFin_sumCongr_castAdd g h i)
  · apply congrArg List.ofFn
    funext i
    exact congrArg (fun x : Fin (n + m) => Val.nat x.val)
      (nclSumToFin_sumCongr_inDelta g h i)

def gmpShiftF : Expr := .arith .add (arg 0) (arg 1)

theorem gmpShift_spec {P : Program} {f : ℕ}
    (hf : P.funs[f]? = some gmpShiftF) (n x X : ℕ) (hn : n < X) (hx : x < X) :
    FunDet P f (.list [.nat n, .nat x]) (.nat (n + x)) (100 * X) := by
  have d := Det.arith' (P := P) (op := .add)
    (Det.arg' (vs := [.nat n, .nat x]) (rest := []) (j := 0) rfl)
    (Det.arg' (vs := [.nat n, .nat x]) (rest := []) (j := 1) rfl) (z := n + x) rfl
  refine FunDet.intro hf (d.mono ?_)
  have := wt_list2_le (.nat n) (.nat x)
  have := wt_nat_le n
  have := wt_nat_le x
  have := wt_nat_le (n + x)
  omega

def gmpSumPermEntryF (mp ap : ℕ) : Expr :=
  .letE (.call mp (mk2 (.length (arg 0)) (arg 1)))
    (.call ap (mk2 (arg 0) (.var 1)))

def gmpSumPermFuns (b : ℕ) : List Expr :=
  [gmpSumPermEntryF (b + 1) (b + 5)] ++ mapFuns (b + 1) (b + 4) ++
    [gmpShiftF] ++ appendFuns (b + 5)

/-- Construct `g ⊕ h` on `n + m` points from its two encoded rows. -/
theorem gmpSumPerm_spec {P : Program} {b n m : ℕ}
    (hp : P.HasAt b (gmpSumPermFuns b)) (g : Perm (Fin n)) (h : Perm (Fin m)) :
    FunDet P b (.list [encPerm g, encPerm h])
      (encPerm (sumToFin (sumCongr g h))) (10 ^ 7 * (n + m + 1) ^ 3) := by
  have hf := (hp.block 0 (gs := [gmpSumPermEntryF (b + 1) (b + 5)]) rfl).single
  have hmp : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4)) := hp.block 1 rfl
  have hs : P.funs[b + 4]? = some gmpShiftF := (hp.block 4 (gs := [gmpShiftF]) rfl).single
  have hap : P.HasAt (b + 5) (appendFuns (b + 5)) := hp.block 5 rfl
  let X := n + m + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hn : n < X := by dsimp [X]; omega
  have hm : m < X := by dsimp [X]; omega
  let ys := (List.finRange m).map fun i => Val.nat (n + (h i : ℕ))
  have hy : (Val.list ys).wt ≤ 5 * X ^ 2 := by
    have hb : ∀ x ∈ (List.finRange m).map (fun i => n + (h i : ℕ)), x ≤ n + m := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
      have := (h i).isLt
      omega
    have hl : ((List.finRange m).map fun i => n + (h i : ℕ)).length ≤ n + m := by simp
    simpa only [natList, List.map_map, Function.comp_def, ys, X] using wt_natList_le_sq hb hl
  have wg : (encPerm g).wt ≤ 4 * X ^ 2 :=
    (wt_encPerm_le g).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : n + 1 ≤ X) 2))
  have wh : (encPerm h).wt ≤ 4 * X ^ 2 :=
    (wt_encPerm_le h).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : m + 1 ≤ X) 2))
  have wn : (Val.nat n).wt ≤ X + 2 := (wt_nat_le n).trans (by omega)
  have wout : (encPerm (sumToFin (sumCongr g h))).wt ≤ 4 * X ^ 2 := wt_encPerm_le _
  have he : encPerm (sumToFin (sumCongr g h)) =
      .list (((List.finRange n).map fun i => Val.nat (g i)) ++ ys) := gmpSumPerm_enc g h
  have hmap := mapList_spec hmp (List.finRange m) (fun i => Val.nat (h i))
    (fun i => Val.nat (n + (h i : ℕ))) (c := .nat n)
    (fun i _ j _ he => by cases h.injective (Fin.ext (Val.nat.inj he)); rfl)
    (fun i _ => gmpShift_spec hs n (h i) X hn (lt_trans (h i).isLt hm))
  have hmap' : FunDet P (b + 1) (.list [.nat n, encPerm h]) (.list ys)
      (100000 * X ^ 3) := by
    apply hmap.mono
    have hw := wt_list2_le (.nat n) (encPerm h)
    simp only [List.length_finRange] 
    change m * (100 * X) + mapK * (m + 1) *
      ((Val.list [.nat n, encPerm h]).wt + (Val.list ys).wt + 1) ≤ _
    have hxx : X ≤ X ^ 2 := Nat.le_self_pow (by decide) X
    have ha : (Val.list [.nat n, encPerm h]).wt + (Val.list ys).wt + 1 ≤ 30 * X ^ 2 := by omega
    have ht := Nat.mul_le_mul (by omega : m + 1 ≤ X) ha
    have hu := Nat.mul_le_mul (by omega : m ≤ X) (show 100 * X ≤ 100 * X ^ 2 by omega)
    simp only [mapK]
    nlinarith [ht, hu]
  have happ : FunDet P (b + 5) (.list [encPerm g, .list ys])
      (encPerm (sumToFin (sumCongr g h))) (100000 * X ^ 3) := by
    refine FunAll.mono (append_spec hap ((List.finRange n).map fun i => Val.nat (g i)) ys)
      fun w c ⟨hw, hc⟩ => ?_
    have hew : w = encPerm (sumToFin (sumCongr g h)) := hw.trans he.symm
    rw [hew] at hc
    refine ⟨hew, hc.trans ?_⟩
    have warg := wt_list2_le (encPerm g) (.list ys)
    have hxx : X ≤ X ^ 2 := Nat.le_self_pow (by decide) X
    have hl : ys.length = m := by simp [ys]
    change loopModK * (ys.length + 1) *
      ((Val.list [encPerm g, .list ys]).wt + ys.length +
        (encPerm (sumToFin (sumCongr g h))).wt + 1) ≤ _
    rw [hl]
    have ha : (Val.list [encPerm g, .list ys]).wt + m +
        (encPerm (sumToFin (sumCongr g h))).wt + 1 ≤ 40 * X ^ 2 := by omega
    have ht := Nat.mul_le_mul (by omega : m + 1 ≤ X) ha
    simp only [loopModK]
    nlinarith [ht]
  let a := Val.list [encPerm g, encPerm h]
  have d0 (rest : List Val) := Det.arg' (P := P) (vs := [encPerm g, encPerm h]) (rest := rest) (j := 0) rfl
  have d1 := Det.arg' (P := P) (vs := [encPerm g, encPerm h]) (rest := []) (j := 1) rfl
  have dl := Det.length (d0 [])
  simp only [List.length_map, List.length_finRange] at dl
  have dm := Det.call (Det.mk2 dl d1) hmap'
  have da := Det.call (Det.mk2 (d0 [.list ys])
    (Det.var' (P := P) (env := [a, .list ys]) (i := 1) rfl)) happ
  refine FunDet.intro hf ((Det.letE dm da).mono ?_)
  have w1 := wt_list2_le (encPerm g) (encPerm h)
  have w2 := wt_list2_le (.nat n) (encPerm h)
  have w3 := wt_list2_le (encPerm g) (.list ys)
  have hxx : X ≤ X ^ 2 := Nat.le_self_pow (by decide) X
  have hxxx : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX (by decide)
  change _ ≤ 10 ^ 7 * X ^ 3
  have heqa : (Val.list [encPerm g, encPerm h]).wt = a.wt := rfl
  omega

end GI.Impl
