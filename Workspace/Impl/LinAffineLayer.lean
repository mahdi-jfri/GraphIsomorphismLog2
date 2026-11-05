module

public import Workspace.Impl.LinAffineMatrixGroup
public import Workspace.Lang.Lib.List

@[expose] public section

/-! One executable affine layer: build every homogeneous generator matrix,
then call the vector stabilizer on the same solvable permutation cover. -/
namespace GI.Impl
open GI.Cited GI.Lang
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

def linAffineLayerInst (I : VecStabInst) (c : gens I.gs → Fin I.d → ZMod I.p)
    (hc : ∀ g h, c (g * h) = (I.φ g).val.mulVec (c h) + c g) : VecStabInst :=
  { I with
    d := I.d + 1
    φ := linAffineGLRep I.φ c hc
    solvable := linAffineGLRep_range_solvable I.φ c hc I.solvable
    v := linExtend I.v 1 }

def linAffineLayerInput (I : VecStabInst) (c : gens I.gs → Fin I.d → ZMod I.p) : Val :=
  .list [encGroup I.gs, .nat I.p,
    .list (I.gs.attach.map fun g => encModMatrix (I.φ ⟨g.1, Subgroup.subset_closure g.2⟩).val),
    .list (I.gs.attach.map fun g => encVec (c ⟨g.1, Subgroup.subset_closure g.2⟩)), encVec I.v]

def linAffineLayerF (range map j : ℕ) : Expr :=
  .letE (.call range (.length (arg 2)))
    (.letE (.call map (mk2 (.var 0) (.var 1)))
      (.prim j (.mkList [arg 0, arg 1, .var 2, .snoc (arg 4) (.nat 1)])))

def linAffineLayerItemF (matrix : ℕ) : Expr :=
  .call matrix (mk2 (.get (.get (arg 0) (.nat 2)) (arg 1))
    (.get (.get (arg 0) (.nat 3)) (arg 1)))

def linAffineLayerFuns (b j : ℕ) : List Expr :=
  [linAffineLayerF (b + 2) (b + 5) j, linAffineLayerItemF (b + 8)] ++
    rangeFuns (b + 2) ++ mapFuns (b + 5) (b + 1) ++ linAffineMatrixFuns (b + 8)

theorem linAffineLayerFuns_length (b j : ℕ) : (linAffineLayerFuns b j).length = 15 := rfl

structure linAffineLayerAt (P : Program) (b j : ℕ) : Prop where
  entry : P.funs[b]? = some (linAffineLayerF (b + 2) (b + 5) j)
  item : P.funs[b + 1]? = some (linAffineLayerItemF (b + 8))
  range : P.HasAt (b + 2) (rangeFuns (b + 2))
  map : P.HasAt (b + 5) (mapFuns (b + 5) (b + 1))
  matrix : linAffineMatrixAt P (b + 8)

theorem linAffineLayerAt_of {P : Program} {b j : ℕ}
    (h : P.HasAt b (linAffineLayerFuns b j)) : linAffineLayerAt P b j where
  entry := (h.block (gs := [linAffineLayerF (b + 2) (b + 5) j]) 0 rfl).single
  item := (h.block (gs := [linAffineLayerItemF (b + 8)]) 1 rfl).single
  range := h.block 2 rfl
  map := h.block 5 rfl
  matrix := linAffineMatrixAt_of (h.block 8 rfl)

/-- The homogeneous vector stabilizer is exactly the affine stabilizer. -/
theorem linAffineLayerInst_stabilizer (I : VecStabInst) (c : gens I.gs → Fin I.d → ZMod I.p)
    (hc : ∀ g h, c (g * h) = (I.φ g).val.mulVec (c h) + c g) (g : gens I.gs) :
    g ∈ vecStab (linAffineLayerInst I c hc) ↔ (I.φ g).val.mulVec I.v + c g = I.v :=
  linAffineGLRep_fixed I.φ c hc g I.v

private theorem linAttach_get {α : Type*} (xs : List α) {k : ℕ} (hk : k < xs.length) :
    xs.attach[k]'(by simpa using hk) = ⟨xs[k], List.getElem_mem hk⟩ := by
  apply Subtype.ext
  simp

/-- A single matrix-item call, used by the indexed map. -/
theorem linAffineLayerItem_spec {P : Program} {b matrix : ℕ}
    (hf : P.funs[b]? = some (linAffineLayerItemF matrix)) (hm : linAffineMatrixAt P matrix)
    (I : VecStabInst) (c : gens I.gs → Fin I.d → ZMod I.p)
    (i : Fin I.gs.length) :
    let g : gens I.gs := ⟨I.gs[i.val], Subgroup.subset_closure (List.getElem_mem i.isLt)⟩
    FunDet P b (.list [linAffineLayerInput I c, .nat i.val])
      (encModMatrix (linAffineMatrix (I.φ g).val (c g)))
      (1000 * ((Val.list [linAffineLayerInput I c, .nat i.val]).wt +
        linAffineMatrixCost (10 * ((linAffineLayerInput I c).wt + 1)) I.d + 1)) := by
  let g : gens I.gs := ⟨I.gs[i.val], Subgroup.subset_closure (List.getElem_mem i.isLt)⟩
  let a := linAffineLayerInput I c
  let W := a.wt
  have dl := Det.arg' (P := P) (vs := [a, .nat i.val]) (rest := []) (j := 0) rfl
  have di := Det.arg' (P := P) (vs := [a, .nat i.val]) (rest := []) (j := 1) rfl
  have dm := Det.get' dl (Det.nat 2) rfl
  have dc := Det.get' dl (Det.nat 3) rfl
  have dr := Det.get' dm di (show (I.gs.attach.map fun h =>
      encModMatrix (I.φ ⟨h.1, Subgroup.subset_closure h.2⟩).val)[i.val]? =
      some (encModMatrix (I.φ g).val) by
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using i.isLt), linAttach_get I.gs i.isLt]
    rfl)
  have du := Det.get' dc di (show (I.gs.attach.map fun h =>
      encVec (c ⟨h.1, Subgroup.subset_closure h.2⟩))[i.val]? = some (encVec (c g)) by
    rw [List.getElem?_map, List.getElem?_eq_getElem (by simpa using i.isLt), linAttach_get I.gs i.isLt]
    rfl)
  have wm : (encModMatrix (I.φ g).val).wt < W := by
    have hh : encModMatrix (I.φ g).val ∈ I.gs.attach.map (fun h =>
        encModMatrix (I.φ ⟨h.1, Subgroup.subset_closure h.2⟩).val) := by
      apply List.mem_map.mpr
      exact ⟨⟨I.gs[i.val], List.getElem_mem i.isLt⟩, by simp, rfl⟩
    exact (wt_le_wt_list hh).trans (wt_le_wt_list (by simp [a, linAffineLayerInput]))
  have wu : (encVec (c g)).wt < W := by
    have hh : encVec (c g) ∈ I.gs.attach.map (fun h => encVec (c ⟨h.1, Subgroup.subset_closure h.2⟩)) := by
      apply List.mem_map.mpr
      exact ⟨⟨I.gs[i.val], List.getElem_mem i.isLt⟩, by simp, rfl⟩
    exact (wt_le_wt_list hh).trans (wt_le_wt_list (by simp [a, linAffineLayerInput]))
  have wi := wt_list2_le (encModMatrix (I.φ g).val) (encVec (c g))
  have wb : (Val.list [encModMatrix (I.φ g).val, encVec (c g)]).wt ≤ 10 * (W + 1) := by omega
  have hcost := linAffineMatrixCost_mono wb (le_refl I.d)
  have spec := (linAffineMatrix_spec hm I.prime (I.φ g).val (c g)).mono hcost
  have outw := spec.wt_lt.le
  apply FunDet.intro hf
  refine (Det.call (Det.mk2 dr du) spec).mono ?_
  have wml : (Val.list (I.gs.attach.map fun h =>
      encModMatrix (I.φ ⟨h.1, Subgroup.subset_closure h.2⟩).val)).wt < W :=
    wt_le_wt_list (by simp [a, linAffineLayerInput])
  have wcl : (Val.list (I.gs.attach.map fun h => encVec (c ⟨h.1, Subgroup.subset_closure h.2⟩))).wt < W :=
    wt_le_wt_list (by simp [a, linAffineLayerInput])
  have wsrc : W < (Val.list [a, .nat i.val]).wt := wt_le_wt_list (by simp)
  have win := wt_list2_le a (.nat i.val)
  have wn := wt_nat_le i.val
  dsimp only [a, W, g] at *
  omega

def linAffineLayerItemBudget (W : ℕ) : ℕ :=
  1000 * (10 * (W + W + 1) + linAffineMatrixCost (10 * (W + 1)) W + 1)
def linAffineLayerMatricesBudget (W : ℕ) : ℕ := linVectorAccWt W (linAffineLayerItemBudget W)
def linAffineLayerMapInputBudget (W : ℕ) : ℕ := 10 * (W + 4 * (W + 1) ^ 2 + 1)
def linAffineLayerMapBudget (W : ℕ) : ℕ :=
  W * linAffineLayerItemBudget W + mapK * (W + 1) *
    (linAffineLayerMapInputBudget W + linAffineLayerMatricesBudget W + 1)
def linAffineLayerPrimInputBudget (W : ℕ) : ℕ := 100 * (W + linAffineLayerMatricesBudget W + 1)
noncomputable def linAffineLayerBudget (h : VectorStabilizer) (W : ℕ) : ℕ :=
  10000 * (W + 8000 * (W + 1) ^ 3 + linAffineLayerMapBudget W +
    linAffineLayerMatricesBudget W + linAffineLayerPrimInputBudget W +
    (vectorStabilizerPrim h).boundSize (linAffineLayerPrimInputBudget W) + 13 * (W + 1) ^ 6 + 1)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 8000 in
theorem linAffineLayer_spec (hv : VectorStabilizer) {P : Program} {b j : ℕ}
    (h : linAffineLayerAt P b j) (hj : P.prims[j]? = some (vectorStabilizerPrim hv))
    (I : VecStabInst) (c : gens I.gs → Fin I.d → ZMod I.p)
    (hc : ∀ g k, c (g * k) = (I.φ g).val.mulVec (c k) + c g) :
    FunAll P b (linAffineLayerInput I c) (fun out cost =>
      GensVal I.n out (vecStabSub (linAffineLayerInst I c hc)) ∧
      cost ≤ linAffineLayerBudget hv (linAffineLayerInput I c).wt) := by
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
    simp only [ms, List.getElem_map, linAttach_get I.gs (by simpa using hk), List.getElem_finRange]
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
  have dprim := vectorStabilizer_call hv I' hj dp
  apply FunAll.intro h.entry
  refine (EvalAll.letE dr fun rows cr hr => ?_)
  obtain ⟨rfl, hcr⟩ := hr
  apply EvalAll.letE dm
  intro matrices cm hm
  obtain ⟨rfl, hcm⟩ := hm
  refine dprim.mono fun out cost ho => ⟨ho.1, ?_⟩
  have wz := wt_list_snoc_le ((List.finRange I.d).map fun i => Val.nat (I.v i).val) (.nat 1)
  have w1 : (Val.nat 1).wt = 3 := by decide
  have wpi := wt_list4_le (encGroup I.gs) (.nat I.p) (.list ms)
    (.list (((List.finRange I.d).map fun i => Val.nat (I.v i).val) ++ [.nat 1]))
  have wPV : (vecStabEnc I').wt ≤ linAffineLayerPrimInputBudget W := by
    rw [hpv]
    unfold linAffineLayerPrimInputBudget
    dsimp only [encVec] at wv
    omega
  have wPVenc := wPV
  rw [hpv] at wPV
  have wout := GensVal.wt_le ho.1
  change out.wt ≤ 13 * (I.n + 1) ^ 6 at wout
  have hpc := (vectorStabilizerPrim hv).bound_le ((vecStabEnc I').size_le_wt.trans wPVenc)
  have hgen := Nat.mul_le_mul_left 13 (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 6)
  have wl := wt_nat_le L
  have wlis : (Val.list (I.gs.attach.map fun g => encModMatrix (I.φ ⟨g.1, Subgroup.subset_closure g.2⟩).val)).wt < W :=
    wt_le_wt_list (by simp [a, linAffineLayerInput])
  have wma := wt_list2_le a (.list xs)
  have hpCost := ho.2
  rw [show I'.n = I.n from rfl] at hpCost
  have hpow : (W + 1) ^ 2 ≤ (W + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  clear * - hpow hL hcr hcm hpCost hpc hgen wPVenc wPV wout wl wlis wma wxs wms wg wp wv w1 wz wpi
  change _ ≤ linAffineLayerBudget hv W
  unfold linAffineLayerBudget
  dsimp only [W, a, L, I', M, linAffineLayerInput, encVec] at *
  omega

/-- With the cited vector algorithm fixed, one affine layer has uniform polynomial bit cost. -/
theorem linAffineLayerBudget_poly (h : VectorStabilizer) : PBU (fun _ W _ => linAffineLayerBudget h W) := by
  simp only [linAffineLayerBudget, linAffineLayerItemBudget, linAffineLayerMatricesBudget,
    linAffineLayerMapBudget, linAffineLayerMapInputBudget, linAffineLayerPrimInputBudget,
    linAffineMatrixCost, linAffineRowsCost, linAffineRowsAcc, linVectorAccWt, Prim.boundSize]
  norm_poly

/-- Installable one-layer specification with a uniform input-weight polynomial.
The only cited algorithm is VectorStabilizer, at the parameter index j. -/
theorem linAffineLayer_spec_poly (hv : VectorStabilizer) :
    ∃ K D : ℕ, ∀ {P : Program} {b j : ℕ},
      P.HasAt b (linAffineLayerFuns b j) → P.prims[j]? = some (vectorStabilizerPrim hv) →
      ∀ (I : VecStabInst) (c : gens I.gs → Fin I.d → ZMod I.p)
        (hc : ∀ g k, c (g * k) = (I.φ g).val.mulVec (c k) + c g),
      FunAll P b (linAffineLayerInput I c) (fun out cost =>
        GensVal I.n out (vecStabSub (linAffineLayerInst I c hc)) ∧
        cost ≤ K * ((linAffineLayerInput I c).wt + 1) ^ D) := by
  obtain ⟨K, D, hp⟩ := linAffineLayerBudget_poly hv
  refine ⟨K * 2 ^ D, D, fun h hj I c hc => ?_⟩
  refine (linAffineLayer_spec hv (linAffineLayerAt_of h) hj I c hc).mono fun out cost ho =>
    ⟨ho.1, ho.2.trans ?_⟩
  let W := (linAffineLayerInput I c).wt
  have hb := hp 0 W 0
  change linAffineLayerBudget hv W ≤ K * (W + 0 + 0 + 2) ^ D at hb
  calc
    _ ≤ K * (W + 2) ^ D := by simpa using hb
    _ ≤ K * (2 * (W + 1)) ^ D := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) D)
    _ = (K * 2 ^ D) * (W + 1) ^ D := by rw [mul_pow]; ring

end GI.Impl
