module

public import Workspace.Impl.FreshHier

@[expose] public section

/-!
# The colors of a fresh phase, in `GI.Lang`

`colorF` on `[xv, yv, P]` (the color values of `S` and the list `P` of the domain positions)
returns `[x', y']`, the compressed codes of the colors on the domain (`cmpCodes`):

1. the codes of `x` and `y` at the domain positions (two gathers, `domCodes`);
2. their concatenation `L` (`codeList`);
3. for each code `z`, the position of its first occurrence in `L` (`posOf L z`).

The input codes may be large numbers, so the costs are bounded by weights (the bit lengths of
the numbers), not by the numbers: `findEqW_spec` is `findEq_spec` with a cost polynomial in the
weight of its input.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPerms encGroup gens)

variable {Ω C : Type} {k : ℕ}

/-! ### Finding a number, at a cost polynomial in the weight -/

theorem eqTest_detW {P : Program} {f : ℕ} (hf : P.funs[f]? = some eqTestF) (j y : ℕ) :
    FunDet P f (.list [.nat j, .nat y]) (boolVal (natEq j (.nat y)))
      (5 * (Val.list [.nat j, .nat y]).wt + 20) := by
  refine FunDet.intro hf ((Det.arith' (Det.arg' (rest := []) (j := 1) rfl)
    (Det.arg' (j := 0) rfl) (z := (natEq j (.nat y)).toNat) ?_).mono ?_)
  · simp only [GI.Machine.BinOp.eval, natEq_nat]
    by_cases hij : y = j <;> simp [hij]
  · have : (natEq j (.nat y)).toNat ≤ 1 := Bool.toNat_le _
    omega

/-- The cost constant of `findEqW_spec`. -/
def findEqWK : ℕ := 10000

/-- **Find a number**, with the cost in the weight `W` of the input. -/
theorem findEqW_spec {P : Program} {b : ℕ} (h : P.HasAt b (findEqFuns b)) (xs : List ℕ) (j : ℕ) :
    FunDet P b (.list [.nat j, natList xs]) (.nat (xs.findIdx fun x => decide (x = j)))
      (findEqWK * ((Val.list [.nat j, natList xs]).wt + 1) ^ 2) := by
  have hfind : P.HasAt b (findFuns b (b + 3)) := h.left
  have htest : P.funs[b + 3]? = some eqTestF := by
    simpa [findEqFuns, findFuns, loopFuns] using h 3 (by simp [findEqFuns, findFuns, loopFuns])
  set W := (Val.list [.nat j, natList xs]).wt with hW
  have hjW : (Val.nat j).wt < W := wt_le_wt_list (by simp)
  have hxsW : (natList xs).wt < W := wt_le_wt_list (by simp)
  have hT : ∀ x ∈ xs.map Val.nat, FunDet P (b + 3) (.list [.nat j, x]) (boolVal (natEq j x))
      (25 * W + 50) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    refine (eqTest_detW htest j y).mono ?_
    have h1 := wt_list2_le (.nat j) (.nat y)
    have h2 : (Val.nat y).wt < (natList xs).wt := wt_le_wt_list (List.mem_map_of_mem hy)
    omega
  refine (find_spec hfind (c := .nat j) (xs := xs.map Val.nat) hT).mono fun w c hw => ⟨?_, ?_⟩
  · rw [hw.1, findIdx_natEq]
  · have hc := hw.2
    simp only [List.map_map, List.length_map] at hc
    have hs : ((xs.map ((fun _ => 25 * W + 50) ∘ Val.nat))).sum = xs.length * (25 * W + 50) := by
      rw [show ((fun _ => 25 * W + 50) ∘ Val.nat) = fun _ => 25 * W + 50 from rfl,
        List.map_const', List.sum_replicate, smul_eq_mul]
    have e1 : (Val.list [.nat j, .list (xs.map Val.nat)]).wt = W := rfl
    rw [hs, e1] at hc
    have hl : xs.length < W := by
      have := length_lt_wt_list (xs.map Val.nat)
      simp only [List.length_map] at this
      have : (Val.list (xs.map Val.nat)).wt = (natList xs).wt := rfl
      omega
    have h1 : xs.length * (25 * W + 50) ≤ (W + 1) * (25 * W + 50) :=
      Nat.mul_le_mul_right _ (by omega)
    have h2 : loopModK * (xs.length + 1) * (W + 2 * xs.length + 3) ≤
        loopModK * (W + 1) * (3 * (W + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have h3 : loopModK * (W + 1) * (3 * (W + 1)) = 3000 * (W + 1) ^ 2 := by
      simp only [loopModK]; ring
    have h4 : (W + 1) * (25 * W + 50) ≤ 50 * (W + 1) ^ 2 := by nlinarith
    simp only [findEqWK]
    omega

/-! ### The module -/

/-- The body of `colorF` on `[xv, yv, P]` (see the module docstring). -/
def colorBody (ga ap mp : ℕ) : Expr :=
  .letE (.call ga (mk2 (arg 0) (arg 2)))
  (.letE (.call ga (mk2 (arg 1) (arg 2)))
  (.letE (.call ap (mk2 (.var 1) (.var 2)))
  (mk2 (.call mp (mk2 (.var 3) (.var 1))) (.call mp (mk2 (.var 3) (.var 2))))))

section Colors

variable (e : Ω ≃ Fin k) (c : C → ℕ) (S : State Ω C)

/-- The color value of `x` (`ColorVal`). -/
def colVal (x : Ω → C) : Val := encFun fun i => c (x (e.symm i))

theorem sublist_domFin : (domFin e S.dom).Sublist (List.finRange k) := List.filter_sublist

theorem wt_domCodes_le (x : Ω → C) :
    (natList (domCodes e c S x)).wt ≤ 2 * (colVal e c x).wt + k + 4 := by
  have h1 := wt_list_le ((domCodes e c S x).map Val.nat)
  have hsub : (((domCodes e c S x).map Val.nat).map Val.wt).Sublist
      (((List.finRange k).map fun i => Val.nat (c (x (e.symm i)))).map Val.wt) := by
    simp only [domCodes, List.map_map]
    exact (sublist_domFin e S).map _
  have h2 := hsub.sum_le_sum (fun _ _ => Nat.zero_le _)
  have h3 := sum_wt_lt_wt_list ((List.finRange k).map fun i => Val.nat (c (x (e.symm i))))
  have h4 : (domCodes e c S x).length ≤ k := by
    simp only [domCodes, List.length_map]; exact length_domFin_le
  have e1 : (Val.list ((List.finRange k).map fun i => Val.nat (c (x (e.symm i))))).wt =
    (colVal e c x).wt := rfl
  simp only [List.length_map] at h1
  have e2 : (Val.list ((domCodes e c S x).map Val.nat)).wt = (natList (domCodes e c S x)).wt := rfl
  omega

/-- The codes of a coloring at the domain positions. -/
theorem gatherCodes_spec {P : Program} {d : ℕ} (hd : DomAt P d) (x : Ω → C) :
    FunDet P (d + 18) (.list [colVal e c x, natList (domNat e S.dom)])
      (natList (domCodes e c S x))
      (gatherK * ((Val.list [colVal e c x, natList (domNat e S.dom)]).wt + 1) ^ 3) := by
  have hg := gather_spec hd.gather (L := (List.finRange k).map fun i => Val.nat (c (x (e.symm i))))
    (is := domNat e S.dom) (fun i hi => by simpa using domNat_lt hi)
  have e1 : (Val.list ((domNat e S.dom).map fun i =>
      ((List.finRange k).map fun i => Val.nat (c (x (e.symm i)))).getD i (.nat 0))) =
      natList (domCodes e c S x) := by
    rw [natList_domNat_eq]
    simp only [natList, domCodes, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    simp only [Function.comp_apply]
    rw [getD_finRange_map _ _ p.isLt]
  rw [e1] at hg
  exact hg

end Colors

/-- The position of a number in a list (`posF`). -/
theorem pos_detW {P : Program} {d : ℕ} (hd : DomAt P d) (L : List ℕ) (z : ℕ) :
    FunDet P (d + 12) (.list [natList L, .nat z]) (.nat (posOf L z))
      (findEqWK * ((Val.list [.nat z, natList L]).wt + 1) ^ 2 +
        15 * (Val.list [natList L, .nat z]).wt + 50) := by
  have g0 := Det.arg' (P := P) (vs := [natList L, .nat z]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [natList L, .nat z]) (rest := []) (j := 1) rfl
  refine FunDet.intro hd.pos ((Det.call (Det.mk2 g1 g0) (findEqW_spec hd.findEq L z)).mono ?_)
  have h1 := wt_list2_le (.nat z) (natList L)
  have h2 := wt_list2_le (natList L) (.nat z)
  have h3 : (Val.nat z).wt < (Val.list [natList L, .nat z]).wt := wt_le_wt_list (by simp)
  have h4 : (natList L).wt < (Val.list [natList L, .nat z]).wt := wt_le_wt_list (by simp)
  have h5 : (Val.nat (posOf L z)).wt ≤ (Val.list [natList L, .nat z]).wt := by
    have := wt_nat_le (posOf L z)
    have := posOf_le L z
    have hl : L.length < (natList L).wt := by
      have := length_lt_wt_list (L.map Val.nat); simpa [natList] using this
    omega
  have e1 : (Val.nat (List.findIdx (fun x => decide (x = z)) L)).wt = (Val.nat (posOf L z)).wt :=
    rfl
  omega

/-- **The compressed codes**: `posOf L` on each entry. -/
theorem mapPos_spec {P : Program} {d : ℕ} (hd : DomAt P d) (L xs : List ℕ) {A : ℕ}
    (hA : (natList L).wt + (natList xs).wt ≤ A) :
    FunDet P (d + 9) (.list [natList L, natList xs]) (natList (xs.map (posOf L)))
      (10 ^ 7 * (A + 1) ^ 3) := by
  have hm := mapList_spec hd.map1 xs Val.nat (fun z => Val.nat (posOf L z)) (c := natList L)
    (B := findEqWK * (3 * A + 7) ^ 2 + 45 * A + 150)
    (fun a _ a' _ h => by simp only [Val.nat.injEq] at h ⊢; rw [h])
    (fun z hz => (pos_detW hd L z).mono (by
      have h1 := wt_list2_le (.nat z) (natList L)
      have h2 := wt_list2_le (natList L) (.nat z)
      have h3 : (Val.nat z).wt < (natList xs).wt := wt_le_wt_list (List.mem_map_of_mem hz)
      have h4 : ((Val.list [.nat z, natList L]).wt + 1) ^ 2 ≤ (3 * A + 7) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
      have h5 := Nat.mul_le_mul_left findEqWK h4
      omega))
  have e1 : (Val.list (xs.map fun z => Val.nat (posOf L z))) = natList (xs.map (posOf L)) := by
    simp [natList, List.map_map]
  have e2 : (Val.list (xs.map Val.nat)) = natList xs := rfl
  rw [e1, e2] at hm
  refine hm.mono ?_
  have hl : xs.length < (natList xs).wt := by
    have := length_lt_wt_list (xs.map Val.nat); simpa [natList] using this
  have w1 := wt_list2_le (natList L) (natList xs)
  have w2 : (natList (xs.map (posOf L))).wt ≤ xs.length * (2 * L.length + 5) + 4 := by
    have := wt_natList_le (xs := xs.map (posOf L)) (B := L.length) (fun y hy => by
      obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy; exact posOf_le L z)
    simpa [natList] using this
  have hL : L.length < (natList L).wt := by
    have := length_lt_wt_list (L.map Val.nat); simpa [natList] using this
  have w3 : xs.length * (2 * L.length + 5) ≤ A * (2 * A + 5) := Nat.mul_le_mul (by omega) (by omega)
  have b1 : xs.length * (findEqWK * (3 * A + 7) ^ 2 + 45 * A + 150) ≤
      (A + 1) * (findEqWK * (49 * (A + 1) ^ 2) + 150 * (A + 1)) := by
    refine Nat.mul_le_mul (by omega) ?_
    have : (3 * A + 7) ^ 2 ≤ 49 * (A + 1) ^ 2 := by nlinarith
    have := Nat.mul_le_mul_left findEqWK this
    omega
  have b2 : (A + 1) * (findEqWK * (49 * (A + 1) ^ 2) + 150 * (A + 1)) =
      490000 * (A + 1) ^ 3 + 150 * (A + 1) ^ 2 := by simp only [findEqWK]; ring
  have b3 : mapK * (xs.length + 1) * ((Val.list [natList L, natList xs]).wt +
      (natList (xs.map (posOf L))).wt + 1) ≤ mapK * (A + 1) * (6 * (A + 1) ^ 2) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by nlinarith)
  have b4 : mapK * (A + 1) * (6 * (A + 1) ^ 2) = 6000 * (A + 1) ^ 3 := by simp only [mapK]; ring
  have b5 : (A + 1) ^ 2 ≤ (A + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem pow_le_mul_pow {a b m : ℕ} (n : ℕ) (h : a ≤ m * b) : a ^ n ≤ m ^ n * b ^ n := by
  rw [← mul_pow]; exact Nat.pow_le_pow_left h n

/-- The cost constant of `colorF`. -/
def colorK : ℕ := 10 ^ 13

theorem wt_natList_append_le (a b : List ℕ) :
    (natList (a ++ b)).wt ≤ 2 * ((natList a).wt + (natList b).wt) + a.length + b.length + 4 := by
  have h1 := wt_list_le ((a ++ b).map Val.nat)
  have h2 := sum_wt_lt_wt_list (a.map Val.nat)
  have h3 := sum_wt_lt_wt_list (b.map Val.nat)
  simp only [List.map_append, List.sum_append, List.length_append, List.length_map] at h1
  have e1 : (Val.list ((a ++ b).map Val.nat)).wt = (natList (a ++ b)).wt := rfl
  have e2 : (Val.list (a.map Val.nat)).wt = (natList a).wt := rfl
  have e3 : (Val.list (b.map Val.nat)).wt = (natList b).wt := rfl
  simp only [List.map_append] at e1
  omega

/-- **The colors of a fresh phase.** -/
theorem color_spec {P : Program} {f d ap : ℕ} (hf : P.funs[f]? = some (colorBody (d + 18) ap (d + 9)))
    (hd : DomAt P d) (hap : P.HasAt ap (appendFuns ap)) (e : Ω ≃ Fin k) (c : C → ℕ)
    (S : State Ω C) :
    FunDet P f (.list [colVal e c S.x, colVal e c S.y, natList (domNat e S.dom)])
      (.list [natList (cmpCodes e c S S.x), natList (cmpCodes e c S S.y)])
      (colorK * ((Val.list [colVal e c S.x, colVal e c S.y, natList (domNat e S.dom)]).wt + 1) ^ 3) := by
  set xv := colVal e c S.x
  set yv := colVal e c S.y
  set Pv := natList (domNat e S.dom)
  set inp := Val.list [xv, yv, Pv] with hinp
  set xd := natList (domCodes e c S S.x)
  set yd := natList (domCodes e c S S.y)
  set A0 := inp.wt with hA0
  have hx : xv.wt < A0 := wt_le_wt_list (by simp)
  have hy : yv.wt < A0 := wt_le_wt_list (by simp)
  have hP : Pv.wt < A0 := wt_le_wt_list (by simp)
  have hk : k < xv.wt := by
    have := length_lt_wt_list ((List.finRange k).map fun i => Val.nat (c (S.x (e.symm i))))
    simpa [xv, colVal, encFun] using this
  have wxd := wt_domCodes_le e c S S.x
  have wyd := wt_domCodes_le e c S S.y
  have lx : (domCodes e c S S.x).length ≤ k := by
    simp only [domCodes, List.length_map]; exact length_domFin_le
  have ly : (domCodes e c S S.y).length ≤ k := by
    simp only [domCodes, List.length_map]; exact length_domFin_le
  have wL := wt_natList_append_le (domCodes e c S S.x) (domCodes e c S S.y)
  have g0 := Det.arg' (P := P) (vs := [xv, yv, Pv]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [xv, yv, Pv]) (rest := []) (j := 1) rfl
  have g2 := Det.arg' (P := P) (vs := [xv, yv, Pv]) (rest := []) (j := 2) rfl
  have g1' := Det.arg' (P := P) (vs := [xv, yv, Pv]) (rest := [xd]) (j := 1) rfl
  have g2' := Det.arg' (P := P) (vs := [xv, yv, Pv]) (rest := [xd]) (j := 2) rfl
  have d1 := Det.call (Det.mk2 g0 g2) (gatherCodes_spec e c S hd S.x)
  have d2 := Det.call (Det.mk2 g1' g2') (gatherCodes_spec e c S hd S.y)
  have happ := append_spec hap ((domCodes e c S S.x).map Val.nat) ((domCodes e c S S.y).map Val.nat)
  have happ' : FunDet P ap (.list [xd, yd]) (natList (codeList e c S))
      (loopModK * ((domCodes e c S S.y).length + 1) *
        ((Val.list [xd, yd]).wt + (domCodes e c S S.y).length + (natList (codeList e c S)).wt + 1)) :=
    happ.mono fun w c' ⟨hw, hc⟩ => ⟨by rw [hw]; simp [natList, codeList], by
      have : w = natList (codeList e c S) := by rw [hw]; simp [natList, codeList]
      subst this
      simpa [xd, yd, natList] using hc⟩
  have d3 := Det.call (Det.mk2 (Det.var' (P := P) (env := [inp, xd, yd]) (i := 1) rfl)
    (Det.var' (P := P) (env := [inp, xd, yd]) (i := 2) rfl)) happ'
  set Lv := natList (codeList e c S)
  have q1 : (colVal e c S.x).wt = xv.wt := rfl
  have q2 : (colVal e c S.y).wt = yv.wt := rfl
  have q3 : (natList (domCodes e c S S.x)).wt = xd.wt := rfl
  have q4 : (natList (domCodes e c S S.y)).wt = yd.wt := rfl
  have q5 : (natList (domCodes e c S S.x ++ domCodes e c S S.y)).wt = Lv.wt := rfl
  have hAx : Lv.wt + xd.wt ≤ 20 * A0 + 50 := by omega
  have hAy : Lv.wt + yd.wt ≤ 20 * A0 + 50 := by omega
  set env := [inp, xd, yd, Lv]
  have d4 := Det.mk2
    (Det.call (Det.mk2 (Det.var' (P := P) (env := env) (i := 3) rfl)
      (Det.var' (P := P) (env := env) (i := 1) rfl))
      (mapPos_spec hd (codeList e c S) (domCodes e c S S.x) hAx))
    (Det.call (Det.mk2 (Det.var' (P := P) (env := env) (i := 3) rfl)
      (Det.var' (P := P) (env := env) (i := 2) rfl))
      (mapPos_spec hd (codeList e c S) (domCodes e c S S.y) hAy))
  refine FunDet.intro hf ((Det.letE d1 (Det.letE d2 (Det.letE d3 d4))).mono ?_)
  -- the cost
  set Y := A0 + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  have p12 : Y ≤ Y ^ 2 := Nat.le_self_pow (by norm_num) _
  have p23 : Y ^ 2 ≤ Y ^ 3 := Nat.pow_le_pow_right hY1 (by omega)
  have a1 := wt_list2_le xv Pv
  have a2 := wt_list2_le yv Pv
  have a3 := wt_list2_le xd yd
  have a4 := wt_list2_le Lv xd
  have a5 := wt_list2_le Lv yd
  have hcl : (codeList e c S).length ≤ 2 * k := by
    simp only [codeList, List.length_append]; omega
  have wcx : (natList (cmpCodes e c S S.x)).wt ≤ k * (2 * (2 * k) + 5) + 4 := by
    refine (wt_natList_le (B := 2 * k) fun y hy => ?_).trans ?_
    · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy; exact (posOf_le _ z).trans hcl
    · simp only [cmpCodes, List.length_map]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ lx) _
  have wcy : (natList (cmpCodes e c S S.y)).wt ≤ k * (2 * (2 * k) + 5) + 4 := by
    refine (wt_natList_le (B := 2 * k) fun y hy => ?_).trans ?_
    · obtain ⟨z, -, rfl⟩ := List.mem_map.1 hy; exact (posOf_le _ z).trans hcl
    · simp only [cmpCodes, List.length_map]
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ ly) _
  have hkk : k * (2 * (2 * k) + 5) ≤ 9 * Y ^ 2 := by
    have : k * (2 * (2 * k) + 5) ≤ Y * (9 * Y) := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have a6 := wt_list2_le (natList (cmpCodes e c S S.x)) (natList (cmpCodes e c S S.y))
  have a7 := wt_list2_le Lv (natList (domCodes e c S S.x))
  have hsum := sum_wt_lt_wt_list [xv, yv, Pv]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  have g3 : (Val.list [xv, Pv]).wt + 1 ≤ 7 * Y := by omega
  have g4 : (Val.list [yv, Pv]).wt + 1 ≤ 7 * Y := by omega
  have g5 := pow_le_mul_pow 3 g3
  have g6 := pow_le_mul_pow 3 g4
  have g7 : 20 * A0 + 50 + 1 ≤ 51 * Y := by omega
  have g8 := pow_le_mul_pow 3 g7
  have g9 : loopModK * ((domCodes e c S S.y).length + 1) *
      ((Val.list [xd, yd]).wt + (domCodes e c S S.y).length + Lv.wt + 1) ≤
      loopModK * Y * (100 * Y) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have g10 : loopModK * Y * (100 * Y) = 100000 * Y ^ 2 := by simp only [loopModK]; ring
  have hinpw : (Val.list [colVal e c S.x, colVal e c S.y, natList (domNat e S.dom)]).wt = A0 := rfl
  rw [hinpw]
  have r1 : ((Val.list [colVal e c S.x, natList (domNat e S.dom)]).wt + 1) ^ 3 =
    ((Val.list [xv, Pv]).wt + 1) ^ 3 := rfl
  have r2 : ((Val.list [colVal e c S.y, natList (domNat e S.dom)]).wt + 1) ^ 3 =
    ((Val.list [yv, Pv]).wt + 1) ^ 3 := rfl
  have r3 : (natList ((domCodes e c S S.x).map (posOf (codeList e c S)))).wt =
    (natList (cmpCodes e c S S.x)).wt := rfl
  have r4 : (natList ((domCodes e c S S.y).map (posOf (codeList e c S)))).wt =
    (natList (cmpCodes e c S S.y)).wt := rfl
  have r5 : (Val.list [natList ((domCodes e c S S.x).map (posOf (codeList e c S))),
      natList ((domCodes e c S S.y).map (posOf (codeList e c S)))]).wt =
    (Val.list [natList (cmpCodes e c S S.x), natList (cmpCodes e c S S.y)]).wt := rfl
  have r6 : (Val.list [xv, yv, Pv]).wt = A0 := rfl
  simp only [colorK, gatherK] at *
  omega

end GI.Impl
