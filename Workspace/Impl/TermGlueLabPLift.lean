import Workspace.Impl.TermGlueLabPLiftM
import Workspace.Impl.RowA18Prog
import Workspace.Impl.LabelLift
import Workspace.Impl.AggItemHvLift
import Workspace.Impl.GenProdSq

/-!
# The lifts `k(s)` of the label step, as a program

Proof of Theorem A.23, using the proof of Theorem A.18:
"Standard constructive quotient operations then give all displayed maps and lifts".

The module `tmGLPLiftFuns b jp jf` (110 functions) has two entry points.

* `tmGLPLcF` at `b`, on `[[n, q], ps, zs₀]` (`ps` graph-form generators of `G`, `zs₀` the
  positions of row `0`): the label kernel `K` in graph form (**PointwiseStab** at `jp`,
  `rowKer_spec`), the pairs `(a, a|_{row 0})` of its generators (`tmGLP_pairs`), and the context
  of the label lift on them (`it_hvLc_spec`). `tmGLPLc_spec`.
* `tmGLPL1F` at `b + 1`, on `[[ctx, rows], s]` (`rows` the positions of all rows, as in
  `coordsVal`): a lift `(a, s)` of `s` (**NormalizedFactor** at `jf`, `liftLab_spec`), then the
  parts of `a` on all rows. The result encodes a tuple `y` with `cleanRowPerm E y ∈ G|_dom` and
  `y 0 = s` (`tmGLPL1_spec`).
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang GI.Paper Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup gens PointwiseStab NormalizedFactor)

/-! ### The program -/

/-- On `[zs, [a, b]]`: `[a, part of a on zs]` (the part module at `pt`). -/
def tmGLPPairStepF (pt : ℕ) : Expr := mk2 (.get (arg 1) (.nat 0)) (.call pt (.var 0))

/-- On `[[a, a], zs]`: the part of `a` on `zs` (the part module at `pt`). -/
def tmGLPRowStepF (pt : ℕ) : Expr := .call pt (mk2 (arg 1) (arg 0))

/-- **The context of the lifts**, on `[[n, q], ps, zs₀]`. -/
def tmGLPLcF (b : ℕ) : Expr :=
  .letE (.call (b + 69) (mk2 (arg 0) (arg 1)))
    (.letE (.call (b + 3) (mk2 (arg 2) (.var 1)))
      (.call (b + 22) (mk2 (mk2 (.get (arg 0) (.nat 0)) (.length (arg 2))) (.var 2))))

/-- **One lift**, on `[[ctx, rows], s]`. -/
def tmGLPL1F (b : ℕ) : Expr :=
  .letE (.call (b + 51) (mk2 (.get (arg 0) (.nat 0)) (arg 1)))
    (.call (b + 7) (mk2 (mk2 (.var 1) (.var 1)) (.get (arg 0) (.nat 1))))

/-- **The lift module** at `b` (110 functions), with **PointwiseStab** at `jp` and
**NormalizedFactor** at `jf`. -/
def tmGLPLiftFuns (b jp jf : ℕ) : List Expr :=
  [tmGLPLcF b, tmGLPL1F b, tmGLPPairStepF (b + 10)] ++ (mapFuns (b + 3) (b + 2) ++
    ([tmGLPRowStepF (b + 10)] ++ (mapFuns (b + 7) (b + 6) ++ (partFuns (b + 10) ++
    ([itHvLcF (b + 23) (b + 26) (b + 47)] ++ (rangeFuns (b + 23) ++ ([grpF (b + 27) (b + 40)] ++
    (pEncMapFuns (b + 27) ++ (mkGroupFuns (b + 40) ++ (fstMapFuns (b + 47) ++
    ([liftLabF (b + 51) (b + 60) jf, shiftAppF (b + 53) (b + 56)] ++ (appendFuns (b + 53) ++
    (mapFuns (b + 56) (b + 59) ++ ([addKF] ++ (pSplitFuns (b + 60) ++
    rowKerFuns (b + 69) jp)))))))))))))))

/-- The blocks of the lift module. -/
structure TmGLPLiftAt (P : Program) (b jp jf : ℕ) : Prop where
  lc : P.funs[b]? = some (tmGLPLcF b)
  l1 : P.funs[b + 1]? = some (tmGLPL1F b)
  pairStep : P.funs[b + 2]? = some (tmGLPPairStepF (b + 10))
  pairMap : P.HasAt (b + 3) (mapFuns (b + 3) (b + 2))
  rowStep : P.funs[b + 6]? = some (tmGLPRowStepF (b + 10))
  rowMap : P.HasAt (b + 7) (mapFuns (b + 7) (b + 6))
  part : P.HasAt (b + 10) (partFuns (b + 10))
  hvLc : P.funs[b + 22]? = some (itHvLcF (b + 23) (b + 26) (b + 47))
  range : P.HasAt (b + 23) (rangeFuns (b + 23))
  grp : P.funs[b + 26]? = some (grpF (b + 27) (b + 40))
  enc : P.HasAt (b + 27) (pEncMapFuns (b + 27))
  mkG : P.HasAt (b + 40) (mkGroupFuns (b + 40))
  fstM : P.HasAt (b + 47) (fstMapFuns (b + 47))
  liftLab : P.funs[b + 51]? = some (liftLabF (b + 51) (b + 60) jf)
  shift : ShiftAt P (b + 51)
  split : P.HasAt (b + 60) (pSplitFuns (b + 60))
  ker : P.HasAt (b + 69) (rowKerFuns (b + 69) jp)

theorem tmGLPLiftAt_of {P : Program} {b jp jf : ℕ} (h : P.HasAt b (tmGLPLiftFuns b jp jf)) :
    TmGLPLiftAt P b jp jf := by
  unfold tmGLPLiftFuns at h
  have lm : ∀ x y, (mapFuns x y).length = 3 := fun _ _ => rfl
  have lp : ∀ x, (partFuns x).length = 12 := fun _ => rfl
  have lr : ∀ x, (rangeFuns x).length = 3 := fun _ => rfl
  have le : ∀ x, (pEncMapFuns x).length = 13 := fun _ => rfl
  have lg : ∀ x, (mkGroupFuns x).length = 7 := fun _ => rfl
  have lf : ∀ x, (fstMapFuns x).length = 4 := fun _ => rfl
  have la : ∀ x, (appendFuns x).length = 3 := fun _ => rfl
  have h0 := h.left
  have r1 := h.right
  have r2 := r1.right
  have r3 := r2.right
  have r4 := r3.right
  have r5 := r4.right
  have r6 := r5.right
  have r7 := r6.right
  have r8 := r7.right
  have r9 := r8.right
  have r10 := r9.right
  have r11 := r10.right
  have r12 := r11.right
  have r13 := r12.right
  have r14 := r13.right
  have r15 := r14.right
  simp only [List.length_cons, List.length_nil, lm, lp, lr, le, lg, lf, la, Nat.add_assoc]
    at r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  norm_num at r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
  exact
    { lc := by simpa using (h0.block (gs := [tmGLPLcF b]) 0 rfl).single
      l1 := by simpa using (h0.block (gs := [tmGLPL1F b]) 1 rfl).single
      pairStep := by simpa using (h0.block (gs := [tmGLPPairStepF (b + 10)]) 2 rfl).single
      pairMap := r1.left
      rowStep := r2.left.single
      rowMap := r3.left
      part := r4.left
      hvLc := r5.left.single
      range := r6.left
      grp := r7.left.single
      enc := r8.left
      mkG := r9.left
      fstM := r10.left
      liftLab := by simpa using r11 0 (by simp)
      shift :=
        { shiftApp := by simpa [Nat.add_assoc] using r11 1 (by simp)
          append := r12.left
          addMap := r13.left
          addK := by simpa using r14 0 (by simp) }
      split := r15.left
      ker := r15.right }

/-! ### The steps -/

variable {n q : ℕ}

/-- The cost bound of one step of the two maps. -/
def tmGLPStepC (n q : ℕ) : ℕ := 1000 * (partK * (n + q + 1) ^ 6)

theorem tmGLPPairStep_spec {P : Program} {f pt : ℕ} (hf : P.funs[f]? = some (tmGLPPairStepF pt))
    (hpt : P.HasAt pt (partFuns pt)) {zs : List ℕ} (hz : ZsOK n zs)
    (p : Perm (Fin n) × Perm (Fin q)) :
    FunDet P f (.list [natList zs, pairV p]) (.list [encPerm p.1, natList (partNat zs p.1)])
      (tmGLPStepC n q) := by
  set inp := Val.list [natList zs, pairV p] with hinp
  have g1 := Det.arg' (P := P) (vs := [natList zs, pairV p]) (rest := []) (j := 1) rfl
  have d1 := Det.get' g1 (Det.nat 0) (vs := [encPerm p.1, encPerm p.2]) (v := encPerm p.1) rfl
  have d2 := Det.call (Det.var' (P := P) (env := [inp]) (i := 0) (v := inp) rfl)
    (part_spec hpt hz p)
  refine FunDet.intro hf ((Det.mk2 d1 d2).mono ?_)
  have w1 := wt_encPerm_le p.1
  have w2 := wt_partNat_le zs hz.len p.1
  have w3 := wt_list2_le (encPerm p.1) (natList (partNat zs p.1))
  have w4 := wt_list2_le (natList zs) (pairV p)
  have w5 := wt_zs_le hz
  have w6 := wt_pairV_le p
  have e1 : (Val.list [natList zs, pairV p]).wt = inp.wt := rfl
  have b1 : (n + 1) ^ 2 ≤ (n + q + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have b2 : (n + q + 1) ^ 2 ≤ (n + q + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hK : 1 ≤ partK := by unfold partK; omega
  have b3 : (n + q + 1) ^ 6 ≤ partK * (n + q + 1) ^ 6 := Nat.le_mul_of_pos_left _ hK
  have b4 : 1 ≤ (n + q + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold tmGLPStepC
  clear_value inp
  omega

theorem tmGLPRowStep_spec {P : Program} {f pt : ℕ} (hf : P.funs[f]? = some (tmGLPRowStepF pt))
    (hpt : P.HasAt pt (partFuns pt)) {zs : List ℕ} (hz : ZsOK n zs) (a : Perm (Fin n)) :
    FunDet P f (.list [pairV (a, a), natList zs]) (natList (partNat zs a)) (tmGLPStepC n n) := by
  set inp := Val.list [pairV (a, a), natList zs] with hinp
  have g0 := Det.arg' (P := P) (vs := [pairV (a, a), natList zs]) (rest := []) (j := 0) rfl
  have g1 := Det.arg' (P := P) (vs := [pairV (a, a), natList zs]) (rest := []) (j := 1) rfl
  have d := Det.call (Det.mk2 g1 g0) (part_spec hpt hz (a, a))
  refine FunDet.intro hf (d.mono ?_)
  have w2 := wt_partNat_le zs hz.len a
  have w4 := wt_list2_le (natList zs) (pairV (a, a))
  have w4' := wt_list2_le (pairV (a, a)) (natList zs)
  have w5 := wt_zs_le hz
  have w6 := wt_pairV_le (a, a)
  have e1 : (Val.list [pairV (a, a), natList zs]).wt = inp.wt := rfl
  have b1 : (n + 1) ^ 2 ≤ (n + n + 1) ^ 6 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have b2 : (n + n + 1) ^ 2 ≤ (n + n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have hK : 1 ≤ partK := by unfold partK; omega
  have b3 : (n + n + 1) ^ 6 ≤ partK * (n + n + 1) ^ 6 := Nat.le_mul_of_pos_left _ hK
  have b4 : 1 ≤ (n + n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  unfold tmGLPStepC
  clear_value inp
  dsimp only at *
  omega

end GI.Impl
