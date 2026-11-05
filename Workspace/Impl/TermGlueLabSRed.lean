module

public import Workspace.Impl.TermGlueLabST4
public import Workspace.Impl.Combine

@[expose] public section

/-!
# Adjoining `N` to the label stabilizer (step 6, the generator cut)

Proof of Theorem A.23: "Adjoining `N` lifts the resulting label stabilizer and
transporter back to `D`." The affine call returns generators `L` of the label stabilizer in
the supplement `S`. The label coset needs generators of `L ⊔ N`. The program appends the two
generator lists and cuts the result to at most `n²` generators, so that the answer stays a
canonical answer (`AnsC` asks for at most `n²` generators).

The cut is one call of the cited **PointwiseStab** primitive on the empty set of points: the
pointwise stabilizer of no points is the whole group, and the primitive returns at most `n²`
generators of it (`GensOf`). Then `mkGroup` puts the list back into group form.

`tmGLSRedF app mg jp` on `[encGroup σN, encGroup L]` returns `encGroup hs` with
`gens hs = gens L ⊔ gens σN` and `hs.length ≤ n²` (`tmGLSRed_spec`, cost `tmGLSRedC`).
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encPerm encGroup gens PointwiseStab pointwiseStab encPts)

variable {n : ℕ}

/-- On `[encGroup σN, encGroup L]`: append the two lists (append at `app`), make a group value
(`mkGroup` at `mg`), cut with the pointwise stabilizer of no points (primitive `jp`), and make
a group value again. -/
def tmGLSRedF (app mg jp : ℕ) : Expr :=
  .letE (.call app (mk2 (.get (arg 1) (.nat 1)) (.get (arg 0) (.nat 1))))
    (.letE (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 1)))
      (.letE (.prim jp (mk2 (.var 2) .nil))
        (.call mg (mk2 (.get (arg 0) (.nat 0)) (.var 3)))))

/-- The cost bound, for an input of weight `W`, with the constants `c`, `k` of the primitive. -/
def tmGLSRedC (c k W : ℕ) : ℕ := c * (100 * (W + 1) ^ 2) ^ k + 10 ^ 8 * (W + 1) ^ 9

/-- The pointwise stabilizer of no points is the whole group. -/
theorem tmGLS_pstab_nil (H : Subgroup (Perm (Fin n))) : pointwiseStab H [] = H := by
  ext g
  simp [pointwiseStab]

/-- The generated group of an append is the join. -/
theorem tmGLS_gens_append (ms ns : List (Perm (Fin n))) : gens (ms ++ ns) = gens ms ⊔ gens ns := by
  unfold gens
  rw [← Subgroup.closure_union]
  congr 1; ext g; simp

/-- Adding the identity does not change the generated group. -/
theorem tmGLS_gens_cons_one (ms : List (Perm (Fin n))) : gens (1 :: ms) = gens ms := by
  unfold gens
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure hg
  · exact Subgroup.closure_mono fun g hg => List.mem_cons_of_mem _ hg


set_option maxHeartbeats 1000000 in
/-- **The cut of `L ++ σN` to at most `n²` generators.** -/
theorem tmGLSRed_spec (h : PointwiseStab) {P : Program} {f app mg jp : ℕ}
    (hf : P.funs[f]? = some (tmGLSRedF app mg jp)) (happ : P.HasAt app (appendFuns app))
    (hmg : P.HasAt mg (mkGroupFuns mg)) (hj : P.prims[jp]? = some (pointwiseStabPrim h))
    (σN L : List (Perm (Fin n))) :
    FunAll P f (.list [encGroup σN, encGroup L]) (fun w c =>
      ∃ hs : List (Perm (Fin n)), w = encGroup hs ∧ hs.length ≤ n ^ 2 ∧
        gens hs = gens L ⊔ gens σN ∧
        c ≤ tmGLSRedC (pointwiseStabPrim h).c (pointwiseStabPrim h).k
          (Val.list [encGroup σN, encGroup L]).wt) := by
  set a : Val := .list [encGroup σN, encGroup L] with ha
  have hwa : (Val.list [encGroup σN, encGroup L]).wt = a.wt := rfl
  -- weights
  have hsum : (encGroup σN).wt + (encGroup L).wt < a.wt := by
    have := sum_wt_lt_wt_list [encGroup σN, encGroup L]
    simpa using this
  have hSN := S_le_wt_encGroup σN
  have hSL := S_le_wt_encGroup L
  have wxN : (Val.list ((1 :: σN).map encPerm)).wt ≤ (encGroup σN).wt :=
    (wt_le_wt_list (vs := [.nat n, .list ((1 :: σN).map encPerm)]) (by simp)).le
  have wxL : (Val.list ((1 :: L).map encPerm)).wt ≤ (encGroup L).wt :=
    (wt_le_wt_list (vs := [.nat n, .list ((1 :: L).map encPerm)]) (by simp)).le
  have hnW : n + 1 ≤ a.wt := by
    have : n + 1 ≤ (σN.length + 2) * (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  apply FunAll.intro hf
  -- 1. append
  have e0 := Det.arg' (P := P) (vs := [encGroup σN, encGroup L]) (rest := []) (j := 0) rfl
  have e1 := Det.arg' (P := P) (vs := [encGroup σN, encGroup L]) (rest := []) (j := 1) rfl
  have dL := Det.get' e1 (Det.nat 1) (vs := [.nat n, .list ((1 :: L).map encPerm)]) rfl
  have dN := Det.get' e0 (Det.nat 1) (vs := [.nat n, .list ((1 :: σN).map encPerm)]) rfl
  have dm := Det.mk2 dL dN
  have happ' := FunAll.mono (append_spec happ ((1 :: L).map encPerm) ((1 :: σN).map encPerm))
    fun w c hw => (⟨hw.1, hw.1 ▸ hw.2⟩ : w = _ ∧ _)
  have wapp := wt_list_append_le ((1 :: L).map encPerm) ((1 :: σN).map encPerm)
  have win := wt_list2_le (.list ((1 :: L).map encPerm)) (.list ((1 :: σN).map encPerm))
  have hlen : ((1 :: σN).map encPerm).length + 1 ≤ a.wt := by
    simp only [List.length_map, List.length_cons]
    have : σN.length + 2 ≤ (σN.length + 2) * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have d1 := (Det.call dm happ').mono (c' := 10 ^ 5 * (a.wt + 1) ^ 2 +
      loopModK * (a.wt + 1) * (8 * (a.wt + 1))) (by
    have h1 : loopModK * (((1 :: σN).map encPerm).length + 1) *
        ((Val.list [.list ((1 :: L).map encPerm), .list ((1 :: σN).map encPerm)]).wt +
          ((1 :: σN).map encPerm).length +
          (Val.list ((1 :: L).map encPerm ++ (1 :: σN).map encPerm)).wt + 1) ≤
        loopModK * (a.wt + 1) * (8 * (a.wt + 1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have h2 : (2 * (Val.list [encGroup σN, encGroup L]).wt + 0 + 5 + (1 + 3) +
        (Val.list ((1 :: L).map encPerm)).wt + 1 + (2 * (Val.list [encGroup σN, encGroup L]).wt +
          1 + 5 + (1 + 3) + (Val.list ((1 :: σN).map encPerm)).wt + 1) +
        2 * (Val.list [.list ((1 :: L).map encPerm), .list ((1 :: σN).map encPerm)]).wt + 7) +
        (Val.list ((1 :: L).map encPerm ++ (1 :: σN).map encPerm)).wt + 1 ≤
        10 ^ 5 * (a.wt + 1) ^ 2 := by
      have : a.wt + 1 ≤ (a.wt + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
      rw [← ha]; omega
    omega)
  refine EvalAll.letE d1 fun v1 c1 hv1 => ?_
  obtain ⟨rfl, hc1⟩ := hv1
  -- 2. the group of `(1 :: L) ++ (1 :: σN)`
  set hs0 : List (Perm (Fin n)) := (1 :: L) ++ (1 :: σN) with hhs0
  have ev1 : Val.list ((1 :: L).map encPerm ++ (1 :: σN).map encPerm) = .list (hs0.map encPerm) := by
    rw [hhs0, List.map_append]
  rw [ev1]
  have f0 := Det.arg' (P := P) (vs := [encGroup σN, encGroup L])
    (rest := [.list (hs0.map encPerm)]) (j := 0) rfl
  have fn := Det.get' f0 (Det.nat 0) (vs := [.nat n, .list ((1 :: σN).map encPerm)]) rfl
  have fv := Det.var' (P := P) (env := [a, .list (hs0.map encPerm)]) (i := 1) rfl
  have d2 := Det.call (Det.mk2 fn fv) (mkGroup_spec hmg hs0)
  have hS0 : (hs0.length + 2) * (n + 1) ≤ a.wt := by
    have e : (hs0.length + 2) * (n + 1) = (L.length + 2) * (n + 1) + (σN.length + 2) * (n + 1) := by
      simp only [hhs0, List.length_append, List.length_cons]; ring
    omega
  have wG0 := wt_encGroup_le hs0
  have wG0' : (encGroup hs0).wt ≤ 40 * (a.wt + 1) ^ 2 := wG0.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2))
  have hmk1 : mkGroupK * ((hs0.length + 2) * (n + 1)) ^ 3 ≤ mkGroupK * (a.wt + 1) ^ 3 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have whs0 : (Val.list (hs0.map encPerm)).wt ≤ (encGroup hs0).wt := wt_gens_le_encGroup hs0
  have d2' := d2.mono (c' := 10 ^ 6 * (a.wt + 1) ^ 3) (by
    have wn := wt_nat_le n
    have w2 := wt_list2_le (.nat n) (.list (hs0.map encPerm))
    have : (a.wt + 1) ^ 2 ≤ (a.wt + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have : a.wt + 1 ≤ (a.wt + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hlog : (Val.nat n).wt ≤ n + 2 := by
      have := wt_nat_le n
      omega
    unfold mkGroupK at hmk1 ⊢
    have hY : (a.wt + 1) ^ 2 ≤ (a.wt + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have hA : a.wt + 1 ≤ (a.wt + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have hS : (Val.nat n).wt + (Val.list (List.map encPerm hs0)).wt +
        2 * (Val.list [Val.nat n, Val.list (List.map encPerm hs0)]).wt + (encGroup hs0).wt
        ≤ 400 * (a.wt + 1) ^ 2 := by omega
    clear d2 fv fn f0 d1 dm dN dL e0 e1 happ'
    generalize (a.wt + 1) ^ 2 = Y2 at *
    generalize (a.wt + 1) ^ 3 = Y3 at *
    generalize ((hs0.length + 2) * (n + 1)) ^ 3 = Z at *
    omega)
  refine EvalAll.letE d2' fun v2 c2 hv2 => ?_
  obtain ⟨rfl, hc2⟩ := hv2
  -- 3. the pointwise stabilizer of no points
  have gv := Det.var' (P := P) (env := [a, .list (hs0.map encPerm), encGroup hs0]) (i := 2) rfl
  have gnil := Det.nil (P := P) (env := [a, .list (hs0.map encPerm), encGroup hs0])
  have hpre := pointwiseStabPrim_spec h (⟨hs0, rfl, rfl⟩ : GroupVal n (encGroup hs0) (gens hs0)) []
  have dp := EvalAll.prim_spec hj (Det.mk2 gv gnil) hpre
  refine EvalAll.letE dp fun v3 c3 hv3 => ?_
  obtain ⟨⟨hs, rfl, hl, hgen⟩, hc3⟩ := hv3
  -- 4. the group value of the cut list
  have g0 := Det.arg' (P := P) (vs := [encGroup σN, encGroup L])
    (rest := [.list (hs0.map encPerm), encGroup hs0, .list (hs.map encPerm)]) (j := 0) rfl
  have gn := Det.get' g0 (Det.nat 0) (vs := [.nat n, .list ((1 :: σN).map encPerm)]) rfl
  have gl := Det.var' (P := P) (env := [a, .list (hs0.map encPerm), encGroup hs0,
    .list (hs.map encPerm)]) (i := 3) rfl
  have d4 := Det.call (Det.mk2 gn gl) (mkGroup_spec hmg hs)
  refine d4.post fun c hc => ⟨hs, rfl, hl, ?_, ?_⟩
  · rw [tmGLS_pstab_nil] at hgen
    rw [hgen, hhs0, tmGLS_gens_append, tmGLS_gens_cons_one, tmGLS_gens_cons_one]
  -- the cost
  have hW6 := wt_encGroup_le_sq hl
  have wgs : (Val.list (hs.map encPerm)).wt ≤ (encGroup hs).wt := wt_gens_le_encGroup hs
  have hS3 := measure_le_of_sq hl
  have wn := wt_nat_le n
  have hlog : (Val.nat n).wt ≤ n + 2 := wn
  have w3 := wt_list2_le (.nat n) (.list (hs.map encPerm))
  have wp := wt_list2_le (encGroup hs0) (.list [])
  have wnil : (Val.list []).wt ≤ 5 := by decide
  have hb : (pointwiseStabPrim h).bound (.list [encGroup hs0, .list []]) ≤
      (pointwiseStabPrim h).c * (100 * (a.wt + 1) ^ 2) ^ (pointwiseStabPrim h).k := by
    unfold Prim.bound
    refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
    have := (Val.list [encGroup hs0, .list []]).size_le_wt
    have : 1 ≤ (a.wt + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hn6 : (n + 1) ^ 6 ≤ (a.wt + 1) ^ 9 :=
    (Nat.pow_le_pow_left (show n + 1 ≤ a.wt + 1 by omega) 6).trans
      (Nat.pow_le_pow_right (by omega) (by norm_num))
  have hn9 : (n + 1) ^ 9 ≤ (a.wt + 1) ^ 9 := Nat.pow_le_pow_left (by omega) 9
  have h29 : (a.wt + 1) ^ 2 ≤ (a.wt + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h39 : (a.wt + 1) ^ 3 ≤ (a.wt + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h19 : a.wt + 1 ≤ (a.wt + 1) ^ 9 := Nat.le_self_pow (by norm_num) _
  have hmk : mkGroupK * ((hs.length + 2) * (n + 1)) ^ 3 ≤ mkGroupK * (8 * (n + 1) ^ 9) := by
    refine Nat.mul_le_mul_left _ ?_
    calc ((hs.length + 2) * (n + 1)) ^ 3 ≤ (2 * (n + 1) ^ 3) ^ 3 := Nat.pow_le_pow_left hS3 3
      _ = 8 * (n + 1) ^ 9 := by ring
  have hl8 : loopModK * (a.wt + 1) * (8 * (a.wt + 1)) = 8000 * (a.wt + 1) ^ 2 := by
    unfold loopModK; ring
  unfold tmGLSRedC
  unfold mkGroupK at *
  clear d4 gl gn g0 dp gv gnil d2' d2 fv fn f0 d1 dm dN dL e0 e1 happ' hpre
  generalize (pointwiseStabPrim h).c * (100 * (a.wt + 1) ^ 2) ^ (pointwiseStabPrim h).k = B at *
  generalize (a.wt + 1) ^ 9 = Y at *
  generalize (a.wt + 1) ^ 2 = Y2 at *
  generalize (a.wt + 1) ^ 3 = Y3 at *
  omega

end GI.Impl
