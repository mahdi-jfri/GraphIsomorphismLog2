module

public import Workspace.Impl.AggItemC1Dat

@[expose] public section

/-!
# Case 1 as a program: transpositions and block swaps

* `itSwB`, `it_swTab_spec`: the transposition `(u v)`, tabulated over the points.
* `itBsB`, `it_bsTab_spec`: the block swap `itpBs lab u u'` of two least points of blocks of the
  same size, tabulated over the points. A point `z` of the block of `u` goes to the point at
  position `pos z - pos u + pos u'`, read off the inverse positions; this position is below `q`
  (`itp_shift_pos`), so the program never reads outside the list.
-/

namespace GI.Impl

open GI.Algorithm GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm)

variable {q : ℕ}

/-- `if` on a test with a known truth value. -/
theorem it_ite {P : Program} {env : List Val} {W : ℕ} {c t e : Expr} {p : Prop} [Decidable p]
    {v : Val} {nc nt ne Ec Et Ee : ℕ}
    (hc : StDC P env c (.nat (if p then 1 else 0)) nc Ec W) (ht : p → StDC P env t v nt Et W)
    (he : ¬ p → StDC P env e v ne Ee W) (hw : v.wt ≤ W) :
    StDC P env (.ite c t e) v (nc + nt + ne + 1) (Ec + Et + Ee) W :=
  StDC.ite hc (fun h => ht (by by_contra hp; simp [hp] at h))
    (fun h => he (by intro hp; simp [hp] at h)) hw

/-! ### Transpositions -/

/-- On `[[u, v], z]`: the image of `z` under the transposition `(u v)`. -/
def itSwB : Expr :=
  let U := Expr.get (arg 0) (.nat 0)
  let V := Expr.get (arg 0) (.nat 1)
  .ite (.arith .eq (arg 1) U) V (.ite (.arith .eq (arg 1) V) U (arg 1))

set_option maxHeartbeats 1000000 in
theorem it_swB_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some itSwB) (u v z : Fin q) :
    FunDet P f (.list [.list [.nat u, .nat v], .nat z]) (.nat (Equiv.swap u v z))
      (1000 * (q + 1)) := by
  set W := 20 * (q + 1)
  have hu := wt_nat_le (u : ℕ)
  have hv := wt_nat_le (v : ℕ)
  have hz := wt_nat_le (z : ℕ)
  have huq := u.isLt
  have hvq := v.isLt
  have hzq := z.isLt
  have hc := wt_list2_le (.nat u) (.nat v)
  have hin := wt_list2_le (.list [.nat u, .nat v]) (.nat z)
  set vs : List Val := [.list [.nat u, .nat v], .nat z]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gZ := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gU := StDC.get g0 (StDC.nat 0 (by omega)) (v := .nat u) rfl (by omega)
  have gV := StDC.get g0 (StDC.nat 1 (by omega)) (v := .nat v) rfl (by omega)
  have hsw := wt_nat_le (Equiv.swap u v z : ℕ)
  have hswq := (Equiv.swap u v z).isLt
  have e1 := StDC.arith' (op := .eq) gZ gU rfl
    (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have e2 := StDC.arith' (op := .eq) gZ gV rfl
    (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have outer := it_ite (p := (z : ℕ) = u) (v := .nat (Equiv.swap u v z)) e1
    (fun h => by
      have : ((Equiv.swap u v z : Fin q) : ℕ) = v := by rw [Fin.ext h, Equiv.swap_apply_left]
      rw [this]; exact gV)
    (fun h => it_ite (p := (z : ℕ) = v) e2
      (fun h' => by
        have : ((Equiv.swap u v z : Fin q) : ℕ) = u := by
          rw [Fin.ext h', Equiv.swap_apply_right]
        rw [this]; exact gU)
      (fun h' => by
        rw [Equiv.swap_apply_of_ne_of_ne (fun e => h (congrArg Fin.val e))
          (fun e => h' (congrArg Fin.val e))]
        exact gZ) (by omega)) (by omega)
  exact StDC.funDet hf outer (by omega)

/-- **The transposition `(u v)` as a list of images.** -/
theorem it_swTab_spec {P : Program} {mp f : ℕ} (hmp : P.HasAt mp (mapFuns mp f))
    (hf : P.funs[f]? = some itSwB) (u v : Fin q) :
    FunDet P mp (.list [.list [.nat u, .nat v], natList (List.range q)]) (encPerm (Equiv.swap u v))
      (10 ^ 5 * (q + 1) ^ 3) := by
  have h := it_tab hmp (c := .list [.nat u, .nat v]) (fun z => (Equiv.swap u v z : ℕ))
    (fun z => (Equiv.swap u v z).isLt.le) (fun z => it_swB_spec hf u v z)
  refine h.mono ?_
  have hc := wt_list2_le (.nat u) (.nat v)
  have := wt_nat_le (u : ℕ); have := wt_nat_le (v : ℕ); have := u.isLt; have := v.isLt
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h1 : q * (1000 * (q + 1)) ≤ 1000 * (q + 1) ^ 3 := by
    calc q * (1000 * (q + 1)) ≤ (q + 1) * (1000 * (q + 1) ^ 2) :=
          Nat.mul_le_mul (by omega) (by omega)
      _ = 1000 * (q + 1) ^ 3 := by ring
  have h2 : mapK * (q + 1) * (2 * (Val.list [.nat u, .nat v]).wt + 22 * (q + 1) ^ 2) ≤
      50000 * (q + 1) ^ 3 := by
    calc mapK * (q + 1) * (2 * (Val.list [.nat u, .nat v]).wt + 22 * (q + 1) ^ 2)
        ≤ 1000 * (q + 1) * (50 * (q + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
      _ = 50000 * (q + 1) ^ 3 := by ring
  calc _ ≤ 1000 * (q + 1) ^ 3 + 50000 * (q + 1) ^ 3 := Nat.add_le_add h1 h2
    _ ≤ 10 ^ 5 * (q + 1) ^ 3 := by omega

/-! ### Block swaps -/

/-- The position read by a block swap is below `q`. -/
theorem itp_shift_pos {lab : Fin q → ℕ} {u u' z : Fin q} (h : ItpBsOK lab u u')
    (hz : lab z = lab u) : itpPos lab z - itpPos lab u + itpPos lab u' < q := by
  have hr : itpRk lab z < itpSz lab u' := by
    rw [← h.2.2, ← itpSz_congr hz]; exact itpRk_lt z
  obtain ⟨w, hw, hwr⟩ := itpRk_surj u' hr
  have e : itpPos lab z - itpPos lab u + itpPos lab u' = itpPos lab w := by
    rw [itpPos_center h.1 hz, itpPos_center h.2.1 hw, hwr]; omega
  rw [e]; exact itpPos_lt w

/-- The point at a position below `q` is the entry of the inverse positions. -/
theorem itpAt_eq {lab : Fin q → ℕ} {p : ℕ} (hp : p < q) (d : Fin q) :
    itpAt lab p d = (itpPosE lab)⁻¹ ⟨p, hp⟩ := by
  rw [itpAt, dif_pos hp]; rfl

/-- On `[[L, Pos, Inv, u, u'], z]`: the image of `z` under the block swap of `u` and `u'`. -/
def itBsB : Expr :=
  let L := Expr.get (arg 0) (.nat 0)
  let Ps := Expr.get (arg 0) (.nat 1)
  let Iv := Expr.get (arg 0) (.nat 2)
  let U := Expr.get (arg 0) (.nat 3)
  let U' := Expr.get (arg 0) (.nat 4)
  let Z := arg 1
  .ite (.arith .eq (.get L Z) (.get L U))
    (.get Iv (.arith .add (.arith .sub (.get Ps Z) (.get Ps U)) (.get Ps U')))
    (.ite (.arith .eq (.get L Z) (.get L U'))
      (.get Iv (.arith .add (.arith .sub (.get Ps Z) (.get Ps U')) (.get Ps U))) Z)

/-- The context of a block swap. -/
noncomputable def itBsCtx (lab : Fin q → ℕ) (u u' : Fin q) : Val :=
  .list [encFun lab, encPerm (itpPosE lab), encPerm (itpPosE lab)⁻¹, .nat u, .nat u']

theorem it_bsCtx_wt {lab : Fin q → ℕ} (hlt : ∀ x, lab x < q) (u u' : Fin q) :
    (itBsCtx lab u u').wt ≤ 60 * (q + 1) ^ 2 := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h := wt_list_le_of [encFun lab, encPerm (itpPosE lab), encPerm (itpPosE lab)⁻¹, .nat u,
    .nat u'] (c := 5 * (q + 1) ^ 2) (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl
      · exact it_encFun_wt lab fun x => (hlt x).le
      · have := wt_encPerm_le (itpPosE lab); omega
      · have := wt_encPerm_le (itpPosE lab)⁻¹; omega
      · have := wt_nat_le (u : ℕ); have := u.isLt; omega
      · have := wt_nat_le (u' : ℕ); have := u'.isLt; omega)
  simp only [List.length_cons, List.length_nil] at h
  rw [itBsCtx]; omega

set_option maxHeartbeats 4000000 in
theorem it_bsB_spec {P : Program} {f : ℕ} (hf : P.funs[f]? = some itBsB) {lab : Fin q → ℕ}
    (hlt : ∀ x, lab x < q) {u u' : Fin q} (hok : ItpBsOK lab u u') (z : Fin q) :
    FunDet P f (.list [itBsCtx lab u u', .nat z]) (.nat (itpBsF lab u u' z))
      (10 ^ 5 * (q + 1) ^ 2) := by
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  set W := 300 * (q + 1) ^ 2
  have hC := it_bsCtx_wt hlt u u'
  have hz := wt_nat_le (z : ℕ)
  have hzq := z.isLt
  have hin := wt_list2_le (itBsCtx lab u u') (.nat z)
  have hL := it_encFun_wt lab fun x => (hlt x).le
  have hP := wt_encPerm_le (itpPosE lab)
  have hI := wt_encPerm_le (itpPosE lab)⁻¹
  have hpt : ∀ k : ℕ, k < q → (Val.nat k).wt ≤ W := fun k hk => by
    have := wt_nat_le k; omega
  set vs : List Val := [itBsCtx lab u u', .nat z]
  have g0 := StDC.arg (P := P) (rest := []) (vs := vs) (j := 0) rfl (W := W) (by omega) (by omega)
    (by omega)
  have gZ := StDC.arg (P := P) (rest := []) (vs := vs) (j := 1) rfl (W := W) (by omega) (by omega)
    (by omega)
  have g0' : StDC P [Val.list vs] (arg 0) (.list [encFun lab, encPerm (itpPosE lab),
      encPerm (itpPosE lab)⁻¹, .nat u, .nat u']) 3 0 W := g0
  have gL := StDC.get g0' (StDC.nat 0 (by omega)) (v := encFun lab) rfl (by omega)
  have gP := StDC.get g0' (StDC.nat 1 (by omega)) (v := encPerm (itpPosE lab)) rfl (by omega)
  have gI := StDC.get g0' (StDC.nat 2 (by omega)) (v := encPerm (itpPosE lab)⁻¹) rfl (by omega)
  have gU := StDC.get g0' (StDC.nat 3 (by omega)) (v := .nat u) rfl (hpt _ u.isLt)
  have gU' := StDC.get g0' (StDC.nat 4 (by omega)) (v := .nat u') rfl (hpt _ u'.isLt)
  have lZ := StDC.get (vs := (List.finRange q).map fun i => Val.nat (lab i)) gL gZ
    (encFun_getElem? lab z) (hpt _ (hlt z))
  have lU := StDC.get (vs := (List.finRange q).map fun i => Val.nat (lab i)) gL gU
    (encFun_getElem? lab u) (hpt _ (hlt u))
  have lU' := StDC.get (vs := (List.finRange q).map fun i => Val.nat (lab i)) gL gU'
    (encFun_getElem? lab u') (hpt _ (hlt u'))
  have pZ := StDC.get (vs := (List.finRange q).map fun i => Val.nat (itpPosE lab i : ℕ)) gP gZ
    (encFun_getElem? (fun i => (itpPosE lab i : ℕ)) z) (hpt _ (itpPosE lab z).isLt)
  have pU := StDC.get (vs := (List.finRange q).map fun i => Val.nat (itpPosE lab i : ℕ)) gP gU
    (encFun_getElem? (fun i => (itpPosE lab i : ℕ)) u) (hpt _ (itpPosE lab u).isLt)
  have pU' := StDC.get (vs := (List.finRange q).map fun i => Val.nat (itpPosE lab i : ℕ)) gP gU'
    (encFun_getElem? (fun i => (itpPosE lab i : ℕ)) u') (hpt _ (itpPosE lab u').isLt)
  simp only [itpPosE_val] at pZ pU pU'
  have e1 := StDC.arith' (op := .eq) lZ lU rfl
    (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have e2 := StDC.arith' (op := .eq) lZ lU' rfl
    (by simp only [GI.Machine.BinOp.eval]; split_ifs <;> omega)
  have hpos := itpPos_lt (lab := lab)
  have s1 := StDC.arith' (op := .sub) pZ pU rfl (by
    simp only [GI.Machine.BinOp.eval]; have := hpos z; omega)
  have s2 := StDC.arith' (op := .sub) pZ pU' rfl (by
    simp only [GI.Machine.BinOp.eval]; have := hpos z; omega)
  have hpz := hpos z
  have hpu := hpos u
  have hpu' := hpos u'
  have outer := it_ite (p := lab z = lab u) (v := .nat (itpBsF lab u u' z)) e1
    (fun h => by
      have hp := itp_shift_pos hok h
      have a1 := StDC.arith' (op := .add) s1 pU' rfl (by
        simp only [GI.Machine.BinOp.eval]; omega)
      have hv : (itpBsF lab u u' z : ℕ) =
          ((itpPosE lab)⁻¹ ⟨itpPos lab z - itpPos lab u + itpPos lab u', hp⟩ : Fin q) := by
        rw [itpBsF, if_pos h, itpAt_eq hp]
      rw [hv]
      exact StDC.get (vs := (List.finRange q).map fun i => Val.nat ((itpPosE lab)⁻¹ i : ℕ)) gI a1
        (encFun_getElem? (fun i => ((itpPosE lab)⁻¹ i : ℕ))
          ⟨itpPos lab z - itpPos lab u + itpPos lab u', hp⟩) (hpt _ (Fin.isLt _)))
    (fun h => it_ite (p := lab z = lab u') e2
      (fun h' => by
        have hp := itp_shift_pos (itpBsOK_symm hok) h'
        have a1 := StDC.arith' (op := .add) s2 pU rfl (by
          simp only [GI.Machine.BinOp.eval]; omega)
        have hv : (itpBsF lab u u' z : ℕ) =
            ((itpPosE lab)⁻¹ ⟨itpPos lab z - itpPos lab u' + itpPos lab u, hp⟩ : Fin q) := by
          rw [itpBsF, if_neg h, if_pos h', itpAt_eq hp]
        rw [hv]
        exact StDC.get (vs := (List.finRange q).map fun i => Val.nat ((itpPosE lab)⁻¹ i : ℕ)) gI a1
          (encFun_getElem? (fun i => ((itpPosE lab)⁻¹ i : ℕ))
            ⟨itpPos lab z - itpPos lab u' + itpPos lab u, hp⟩) (hpt _ (Fin.isLt _)))
      (fun h' => by
        rw [itpBsF, if_neg h, if_neg h']
        exact gZ) (hpt _ (Fin.isLt _))) (hpt _ (Fin.isLt _))
  exact StDC.funDet hf outer (by omega)

/-- **A block swap as a list of images.** -/
theorem it_bsTab_spec {P : Program} {mp f : ℕ} (hmp : P.HasAt mp (mapFuns mp f))
    (hf : P.funs[f]? = some itBsB) {lab : Fin q → ℕ} (hlt : ∀ x, lab x < q) {u u' : Fin q}
    (hok : ItpBsOK lab u u') :
    FunDet P mp (.list [itBsCtx lab u u', natList (List.range q)]) (encPerm (itpBs lab u u'))
      (10 ^ 6 * (q + 1) ^ 3) := by
  have h := it_tab hmp (c := itBsCtx lab u u') (fun z => (itpBs lab u u' z : ℕ))
    (fun z => (itpBs lab u u' z).isLt.le) (fun z => by
      show FunDet P f _ (.nat (itpBs lab u u' z : ℕ)) _
      rw [itpBs_apply hok]; exact it_bsB_spec hf hlt hok z)
  refine h.mono ?_
  have hc := it_bsCtx_wt hlt u u'
  have hq1 : 1 ≤ (q + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hqa : q + 1 ≤ (q + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h1 : q * (10 ^ 5 * (q + 1) ^ 2) ≤ 10 ^ 5 * (q + 1) ^ 3 := by
    calc q * (10 ^ 5 * (q + 1) ^ 2) ≤ (q + 1) * (10 ^ 5 * (q + 1) ^ 2) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 10 ^ 5 * (q + 1) ^ 3 := by ring
  have h2 : mapK * (q + 1) * (2 * (itBsCtx lab u u').wt + 22 * (q + 1) ^ 2) ≤
      2 * 10 ^ 5 * (q + 1) ^ 3 := by
    calc mapK * (q + 1) * (2 * (itBsCtx lab u u').wt + 22 * (q + 1) ^ 2)
        ≤ 1000 * (q + 1) * (200 * (q + 1) ^ 2) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * 10 ^ 5 * (q + 1) ^ 3 := by ring
  calc _ ≤ 10 ^ 5 * (q + 1) ^ 3 + 2 * 10 ^ 5 * (q + 1) ^ 3 := Nat.add_le_add h1 h2
    _ ≤ 10 ^ 6 * (q + 1) ^ 3 := by omega

end GI.Impl
