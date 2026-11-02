import Workspace.Impl.LinAffineLayer

/-! Compute the homogeneous representation data before making a vector call. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linAffineInputF (range map : ℕ) : Expr :=
  .letE (.call range (.length (arg 2)))
    (.letE (.call map (mk2 (.var 0) (.var 1)))
      (mk4 (arg 0) (arg 1) (.var 2) (.snoc (arg 4) (.nat 1))))

def linAffineInputFuns (b : ℕ) : List Expr :=
  [linAffineInputF (b + 2) (b + 5), linAffineLayerItemF (b + 8)] ++
    rangeFuns (b + 2) ++ mapFuns (b + 5) (b + 1) ++ linAffineMatrixFuns (b + 8)

theorem linAffineInputFuns_length (b : ℕ) : (linAffineInputFuns b).length = 15 := rfl

structure linAffineInputAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linAffineInputF (b + 2) (b + 5))
  item : P.funs[b + 1]? = some (linAffineLayerItemF (b + 8))
  range : P.HasAt (b + 2) (rangeFuns (b + 2))
  map : P.HasAt (b + 5) (mapFuns (b + 5) (b + 1))
  matrix : linAffineMatrixAt P (b + 8)

theorem linAffineInputAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linAffineInputFuns b)) : linAffineInputAt P b where
  entry := (h.block (gs := [linAffineInputF (b + 2) (b + 5)]) 0 rfl).single
  item := (h.block (gs := [linAffineLayerItemF (b + 8)]) 1 rfl).single
  range := h.block 2 rfl
  map := h.block 5 rfl
  matrix := linAffineMatrixAt_of (h.block 8 rfl)

private theorem linAffineInput_attach_get {α : Type*} (xs : List α) {k : ℕ} (hk : k < xs.length) :
    xs.attach[k]'(by simpa using hk) = ⟨xs[k], List.getElem_mem hk⟩ := by
  apply Subtype.ext
  simp

def linAffineInputCost (W : ℕ) : ℕ :=
  100000 * (W + 8000 * (W + 1) ^ 3 + linAffineLayerMapBudget W + linAffineLayerMapInputBudget W + linAffineLayerMatricesBudget W + 4 * (W + 1) ^ 2 + 1)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 6000 in
theorem linAffineInput_spec {P : Program} {b : ℕ} (h : linAffineInputAt P b)
    (I : VecStabInst) (c : gens I.gs → Fin I.d → ZMod I.p)
    (hc : ∀ g k, c (g * k) = (I.φ g).val.mulVec (c k) + c g) :
    FunDet P b (linAffineLayerInput I c) (vecStabEnc (linAffineLayerInst I c hc))
      (linAffineInputCost (linAffineLayerInput I c).wt) := by
  let a := linAffineLayerInput I c
  let W := a.wt
  let L := I.gs.length
  let g (i : Fin L) : gens I.gs := ⟨I.gs[i.val], Subgroup.subset_closure (List.getElem_mem i.isLt)⟩
  let ms := (List.finRange L).map fun i => encModMatrix (linAffineMatrix (I.φ (g i)).val (c (g i)))
  let xs := (List.finRange L).map fun i => Val.nat i.val
  let B := linAffineLayerItemBudget W
  let M := linAffineLayerMatricesBudget W
  have wg : (encGroup I.gs).wt < W := wt_le_wt_list (by simp [a, linAffineLayerInput])
  have wp : (Val.nat I.p).wt < W := wt_le_wt_list (by simp [a, linAffineLayerInput])
  have wv : (encVec I.v).wt < W := wt_le_wt_list (by simp [a, linAffineLayerInput])
  have hsrc := S_le_wt_encGroup I.gs
  have hL : L ≤ W := by dsimp only [L]; nlinarith
  have hn : I.n ≤ W := by nlinarith
  have hd : I.d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange I.d).map fun i => Val.nat (I.v i).val)
    simp only [List.length_map, List.length_finRange] at hh
    exact (hh.trans wv).le
  have item (i : Fin L) : FunDet P (b + 1) (.list [a, .nat i.val])
      (encModMatrix (linAffineMatrix (I.φ (g i)).val (c (g i)))) B := by
    have hi : i.val ≤ W := i.isLt.le.trans hL
    have wi := wt_nat_le i.val
    have wa := wt_list2_le a (.nat i.val)
    have warg : (Val.list [a, .nat i.val]).wt ≤ 10 * (W + W + 1) := by dsimp only [W]; omega
    have hm := linAffineMatrixCost_mono (le_refl (10 * (W + 1))) hd
    refine (linAffineLayerItem_spec h.item h.matrix I c i).mono ?_
    change 1000 * ((Val.list [a, .nat i.val]).wt + linAffineMatrixCost (10 * (W + 1)) I.d + 1) ≤ B
    unfold B linAffineLayerItemBudget
    omega
  have wms : (Val.list ms).wt ≤ M := by
    have hh := linWtList (vs := ms) (B := B) (by
      intro v hv; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv; exact (item i).wt_lt.le)
    simp only [ms, List.length_map, List.length_finRange] at hh
    exact hh.trans (by unfold M linAffineLayerMatricesBudget linVectorAccWt; nlinarith [Nat.mul_le_mul_right B hL])
  have wxs : (Val.list xs).wt ≤ 4 * (W + 1) ^ 2 := by
    have hx : Val.list xs = encPerm (1 : Equiv.Perm (Fin L)) := rfl
    rw [hx]
    exact (wt_encPerm_le _).trans (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.add_le_add_right hL 1) 2))
  have wmap : (Val.list [a, .list xs]).wt ≤ linAffineLayerMapInputBudget W := by
    have hh := wt_list2_le a (.list xs)
    unfold linAffineLayerMapInputBudget
    dsimp only [W] at *
    omega
  have mapped : FunDet P (b + 5) (.list [a, .list xs]) (.list ms) (linAffineLayerMapBudget W) := by
    have hm := map_spec h.map (c := a) (xs := xs)
      (R := fun x w => ∀ i : Fin L, x = .nat i.val →
        w = encModMatrix (linAffineMatrix (I.φ (g i)).val (c (g i)))) (B := fun _ => B) (by
        intro x hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        refine FunAll.mono (item i) fun out cost ho => ⟨?_, ho.2⟩
        intro k hk
        have he : i = k := Fin.ext (Val.nat.inj hk)
        simpa only [he] using ho.1)
    refine hm.mono fun out cost ho => ?_
    obtain ⟨ws, rfl, hws, hcost⟩ := ho
    have he : ws = ms := forall₂_map_eq (h := hws) (fun i _ w hw => hw i rfl)
    subst ws
    refine ⟨rfl, ?_⟩
    simp only [xs, List.length_map, List.length_finRange, List.map_const', List.sum_replicate,
      smul_eq_mul] at hcost
    have h₁ := Nat.mul_le_mul_right B hL
    have h₂ := Nat.mul_le_mul (Nat.mul_le_mul_left mapK (Nat.add_le_add_right hL 1))
      (show (Val.list [a, .list xs]).wt + (Val.list ms).wt + 1 ≤ linAffineLayerMapInputBudget W + M + 1 by omega)
    dsimp only [xs] at h₂
    unfold linAffineLayerMapBudget
    change cost ≤ W * B + mapK * (W + 1) * (linAffineLayerMapInputBudget W + M + 1)
    omega
  have rr := GI.Lang.range_det h.range L
  have rr' : FunDet P (b + 2) (.nat L) (.list xs) (8000 * (W + 1) ^ 3) := by
    exact rr.mono (Nat.mul_le_mul_left 8000 (Nat.pow_le_pow_left (Nat.add_le_add_right hL 1) 3))
  have dl := Det.length (Det.arg' (P := P) (vs := [encGroup I.gs, .nat I.p,
    .list (I.gs.attach.map fun g => encModMatrix (I.φ ⟨g.1, Subgroup.subset_closure g.2⟩).val),
    .list (I.gs.attach.map fun g => encVec (c ⟨g.1, Subgroup.subset_closure g.2⟩)), encVec I.v])
    (rest := []) (j := 2) rfl)
  simp only [List.length_map, List.length_attach] at dl
  have dr := Det.call dl rr'
  have dm := Det.call (Det.mk2 (Det.var' (P := P) (env := [a, .list xs]) (i := 0) rfl)
    (Det.var' (P := P) (env := [a, .list xs]) (i := 1) rfl)) mapped
  let I' := linAffineLayerInst I c hc
  have hmat : I.gs.attach.map (fun g => encModMatrix (I'.φ ⟨g.1, Subgroup.subset_closure g.2⟩).val) = ms := by
    apply List.ext_getElem (by simp [ms, L])
    intro k hk hk'
    simp only [ms, List.getElem_map, linAffineInput_attach_get I.gs (by simpa using hk), List.getElem_finRange]
    rfl
  have hext : encVec (linExtend I.v 1) = .list (((List.finRange I.d).map fun i => .nat (I.v i).val) ++ [.nat 1]) := by
    have hh := congrArg Val.list (linExtend_value (fun x : ZMod I.p => Val.nat x.val) I.v 1)
    simpa [encVec, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt I.prime.one_lt] using hh
  have hpv : vecStabEnc I' = .list [encGroup I.gs, .nat I.p, .list ms,
      .list (((List.finRange I.d).map fun i => .nat (I.v i).val) ++ [.nat 1])] := by
    change Val.list [encGroup I.gs, .nat I.p,
      .list (I.gs.attach.map (fun g => encModMatrix (I'.φ ⟨g.1, Subgroup.subset_closure g.2⟩).val)),
      encVec (linExtend I.v 1)] = _
    rw [hmat, hext]
  have da (j : ℕ) {v : Val} (hv : [encGroup I.gs, .nat I.p,
    .list (I.gs.attach.map fun g => encModMatrix (I.φ ⟨g.1, Subgroup.subset_closure g.2⟩).val),
    .list (I.gs.attach.map fun g => encVec (c ⟨g.1, Subgroup.subset_closure g.2⟩)), encVec I.v][j]? = some v) :=
    Det.arg' (P := P) (vs := [encGroup I.gs, .nat I.p,
      .list (I.gs.attach.map fun g => encModMatrix (I.φ ⟨g.1, Subgroup.subset_closure g.2⟩).val),
      .list (I.gs.attach.map fun g => encVec (c ⟨g.1, Subgroup.subset_closure g.2⟩)), encVec I.v])
      (rest := [.list xs, .list ms]) (j := j) hv
  have dp := Det.mk4 (da 0 rfl) (da 1 rfl)
    (Det.var' (P := P) (env := [a, .list xs, .list ms]) (i := 2) rfl)
    (Det.snoc (da 4 rfl) (Det.nat 1))
  rw [← hpv] at dp
  have wext := wt_list_snoc_le ((List.finRange I.d).map fun i => Val.nat (I.v i).val) (.nat 1)
  have w1 : (Val.nat 1).wt = 3 := rfl
  have wpi := wt_list4_le (encGroup I.gs) (.nat I.p) (.list ms)
    (.list (((List.finRange I.d).map fun i => .nat (I.v i).val) ++ [.nat 1]))
  have wpv : (vecStabEnc I').wt ≤ 100 * (W + M + 1) := by
    rw [hpv]
    dsimp only [encVec] at wv
    omega
  have wlis : (Val.list (I.gs.attach.map fun g =>
      encModMatrix (I.φ ⟨g.val, Subgroup.subset_closure g.property⟩).val)).wt < W :=
    wt_le_wt_list (by simp [a, linAffineLayerInput])
  apply FunDet.intro h.entry
  refine (Det.letE dr (Det.letE dm dp)).mono ?_
  change _ ≤ linAffineInputCost W
  dsimp only [linAffineInputCost]
  dsimp only [a, W, L, I', M, linAffineLayerInput, encVec] at *
  omega

theorem linAffineInputCost_poly : PBU (fun _ W _ => linAffineInputCost W) := by
  simp only [linAffineInputCost, linAffineLayerMapBudget, linAffineLayerMapInputBudget,
    linAffineLayerMatricesBudget, linAffineLayerItemBudget, linAffineMatrixCost,
    linAffineRowsCost, linAffineRowsAcc, linVectorAccWt]
  norm_poly

end GI.Impl
