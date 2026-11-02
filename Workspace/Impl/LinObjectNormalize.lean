import Workspace.Impl.LinObjectFind
import Workspace.Impl.LinObjectRelabel
import Workspace.Lang.Prims.Ops
import Workspace.Lang.Prims.LinNormal

/-! Normalize colors and compress all object subgroups before the affine glue. -/
namespace GI.Impl
open GI.Cited GI.Lang

def linObjectNormalizeItemF (find red : ℕ) : Expr :=
  .letE (.call find (.var 0))
    (.letE (.call red (.get (arg 1) (.nat 1)))
      (mk3 (.var 1) (.var 2) (.get (arg 1) (.nat 2))))

def linObjectNormalizeItemFuns (b j : ℕ) : List Expr :=
  [linObjectNormalizeItemF (b + 1) (b + 12)] ++ linObjectFindFuns (b + 1) j ++
    reduceFuns (b + 12) j

theorem linObjectNormalizeItemFuns_length (b j : ℕ) :
    (linObjectNormalizeItemFuns b j).length = 17 := rfl

noncomputable def linObjectNormalizeItemCost (h : Membership) (W : ℕ) : ℕ :=
  100000 * (W + linObjectFindCost h W + reduceCost h W W + (W + 1) ^ 6 + 1)

theorem linReduceCost_mono (h : Membership) {n m N M : ℕ} (hn : n ≤ N) (hm : m ≤ M) :
    reduceCost h n m ≤ reduceCost h N M := by
  unfold reduceCost memCost
  gcongr

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linObjectNormalizeItem_spec (hm : Membership) {P : Program} {b j n : ℕ}
    (hp : P.HasAt b (linObjectNormalizeItemFuns b j))
    (hj : P.prims[j]? = some (membershipPrim hm)) (Z : List (TmRiO n)) (o : TmRiO n) :
    FunDet P b (.list [tmGlObjsVal Z, tmGlObjVal o])
      (tmGlObjVal (linObjectNorm (linObjectColor Z) o))
      (linObjectNormalizeItemCost hm (Val.list [tmGlObjsVal Z, tmGlObjVal o]).wt) := by
  let a := Val.list [tmGlObjsVal Z, tmGlObjVal o]
  let W := a.wt
  have wo : (tmGlObjVal o).wt < W := wt_le_wt_list (by simp [W, a])
  have wg : (encGroup o.2.1).wt < W :=
    (wt_le_wt_list (by simp [tmGlObjVal] : encGroup o.2.1 ∈
      [.nat o.1, encGroup o.2.1, encPerm o.2.2])).trans wo
  have ws := S_le_wt_encGroup o.2.1
  have hn : n ≤ W := by nlinarith
  have hm' : o.2.1.length ≤ W := by nlinarith
  have hf := linObjectFind_spec hm (hp.block 1 rfl) hj Z o
  have hr := (reduce_spec hm (hp.block 12 rfl) hj o.2.1).mono (linReduceCost_mono hm hn hm')
  have df := Det.call (Det.var' (P := P) (env := [a]) (i := 0) rfl) hf
  have dg := Det.call (Det.get'
    (Det.arg' (P := P) (vs := [tmGlObjsVal Z, tmGlObjVal o])
      (rest := [.nat (linObjectColor Z o)]) (j := 1) rfl) (Det.nat 1) rfl) hr
  have ds := Det.mk3
    (Det.var' (P := P) (env := [a, .nat (linObjectColor Z o), encGroup (keepList o.2.1)]) (i := 1) rfl)
    (Det.var' (P := P) (env := [a, .nat (linObjectColor Z o), encGroup (keepList o.2.1)]) (i := 2) rfl)
    (Det.get' (Det.arg' (P := P) (vs := [tmGlObjsVal Z, tmGlObjVal o])
      (rest := [.nat (linObjectColor Z o), encGroup (keepList o.2.1)]) (j := 1) rfl) (Det.nat 2) rfl)
  have dz : linObjectColor Z o ≤ Z.length := List.findIdx_le_length
  have wz : (tmGlObjsVal Z).wt < W := wt_le_wt_list (by simp [W, a])
  have wl : Z.length < W := by
    have hh := length_lt_wt_list (Z.map tmGlObjVal)
    simpa only [List.length_map] using hh.trans wz
  have wi := wt_nat_le (linObjectColor Z o)
  have wk := wt_encGroup_sq (length_keepList_le o.2.1)
  have wp : (encPerm o.2.2).wt < W :=
    (wt_le_wt_list (by simp [tmGlObjVal] : encPerm o.2.2 ∈
      [.nat o.1, encGroup o.2.1, encPerm o.2.2])).trans wo
  have wn : (n + 1) ^ 6 ≤ (W + 1) ^ 6 := by gcongr
  have ww := wt_list3_le (.nat (linObjectColor Z o)) (encGroup (keepList o.2.1)) (encPerm o.2.2)
  apply FunAll.intro (hp.block (gs := [linObjectNormalizeItemF (b + 1) (b + 12)]) 0 rfl).single
  refine (Det.letE df (Det.letE dg ds)).post fun cost hcost => ⟨rfl, ?_⟩
  change cost ≤ linObjectNormalizeItemCost hm W
  unfold linObjectNormalizeItemCost
  dsimp only [W, a] at *
  omega

theorem linObjectNormalizeItemCost_mono (h : Membership) {W V : ℕ} (hW : W ≤ V) :
    linObjectNormalizeItemCost h W ≤ linObjectNormalizeItemCost h V := by
  unfold linObjectNormalizeItemCost
  gcongr
  · exact linObjectFindCost_mono h hW
  · exact linReduceCost_mono h hW hW

theorem linObjectNormalizeItemCost_poly (h : Membership) :
    PBU (fun _ W _ => linObjectNormalizeItemCost h W) := by
  simp only [linObjectNormalizeItemCost, linObjectFindCost, linObjectClassCost, linGroupEqCost,
    linGroupLeCost, linGroupMemberCost, Prim.boundSize, reduceCost, memCost]
  norm_poly

def linObjectNormalizeF (map : ℕ) : Expr := .call map (mk2 (.var 0) (.var 0))

def linObjectNormalizeFuns (b j : ℕ) : List Expr :=
  [linObjectNormalizeF (b + 1)] ++ mapFuns (b + 1) (b + 4) ++
    linObjectNormalizeItemFuns (b + 4) j

theorem linObjectNormalizeFuns_length (b j : ℕ) :
    (linObjectNormalizeFuns b j).length = 21 := rfl

structure linObjectNormalizeAt (P : Program) (b j : ℕ) : Prop where
  entry : P.funs[b]? = some (linObjectNormalizeF (b + 1))
  map : P.HasAt (b + 1) (mapFuns (b + 1) (b + 4))
  item : P.HasAt (b + 4) (linObjectNormalizeItemFuns (b + 4) j)

theorem linObjectNormalizeAt_of {P : Program} {b j : ℕ}
    (h : P.HasAt b (linObjectNormalizeFuns b j)) : linObjectNormalizeAt P b j where
  entry := (h.block (gs := [linObjectNormalizeF (b + 1)]) 0 rfl).single
  map := h.block 1 rfl
  item := h.block 4 rfl

noncomputable def linObjectNormalizeCost (h : Membership) (W : ℕ) : ℕ :=
  let B := linObjectNormalizeItemCost h (10 * (W + 1))
  100000 * (W + 1) ^ 2 * (B + W + 1)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4000 in
theorem linObjectNormalize_spec (hm : Membership) {P : Program} {b j n : ℕ}
    (hp : linObjectNormalizeAt P b j) (hj : P.prims[j]? = some (membershipPrim hm))
    (Z : List (TmRiO n)) :
    FunDet P b (tmGlObjsVal Z)
      (tmGlObjsVal (Z.map (linObjectNorm (linObjectColor Z))))
      (linObjectNormalizeCost hm (tmGlObjsVal Z).wt) := by
  classical
  let a := tmGlObjsVal Z
  let W := a.wt
  let xs := Z.map tmGlObjVal
  let B := linObjectNormalizeItemCost hm (10 * (W + 1))
  let out := (Z.map (linObjectNorm (linObjectColor Z))).map tmGlObjVal
  have wl : xs.length ≤ W := (length_lt_wt_list xs).le
  have hi : ∀ x ∈ xs, FunAll P (b + 4) (.list [a, x])
      (fun w cost => w = tmGlObjVal (linObjectNorm (linObjectColor Z) (tmRiDec (n := n) x)) ∧ cost ≤ B) := by
    intro x hx
    obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hx
    have wo : (tmGlObjVal o).wt < W := wt_le_wt_list (List.mem_map.mpr ⟨o, ho, rfl⟩)
    have ww := wt_list2_le a (tmGlObjVal o)
    have hh : (Val.list [a, tmGlObjVal o]).wt ≤ 10 * (W + 1) := by omega
    have hs := (linObjectNormalizeItem_spec hm hp.item hj Z o).mono
      (linObjectNormalizeItemCost_mono hm hh)
    simpa only [tmRiDec_val] using hs
  have hs := map_spec hp.map hi
  have heq : ∀ ws, List.Forall₂
      (fun x w => w = tmGlObjVal (linObjectNorm (linObjectColor Z) (tmRiDec (n := n) x))) xs ws →
      ws = out := by
    intro ws hws
    have hh : ws = xs.map (fun x => tmGlObjVal (linObjectNorm (linObjectColor Z) (tmRiDec (n := n) x))) := by
      apply List.ext_getElem (by simp [hws.length_eq])
      intro i hi hi'
      simpa only [List.getElem_map] using hws.get (by simpa only [List.length_map] using hi') hi
    simpa only [xs, out, List.map_map, Function.comp_def, tmRiDec_val] using hh
  have ws : (Val.list out).wt ≤ 2 * (W * B) + W + 4 := by
    have hh := linWtList (vs := out) (B := B) (by
      intro w hw
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hw
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ho
      have hh := hi (tmGlObjVal x) (List.mem_map.mpr ⟨x, hx, rfl⟩)
      have hw := (linObjectNormalizeItem_spec hm hp.item hj Z x).wt_lt
      have wx : (tmGlObjVal x).wt < W := wt_le_wt_list (List.mem_map.mpr ⟨x, hx, rfl⟩)
      have wi := wt_list2_le a (tmGlObjVal x)
      have ww : (Val.list [a, tmGlObjVal x]).wt ≤ 10 * (W + 1) := by omega
      exact hw.le.trans (linObjectNormalizeItemCost_mono hm ww))
    have wl' : out.length ≤ W := by simpa only [out, List.length_map, xs] using wl
    nlinarith [Nat.mul_le_mul_right B wl']
  have hd : FunDet P (b + 1) (.list [a, .list xs]) (.list out)
      (xs.length * B + mapK * (xs.length + 1) * ((Val.list [a, .list xs]).wt + (Val.list out).wt + 1)) := hs.mono (fun w cost hw => by
    obtain ⟨zs, rfl, hz, hc⟩ := hw
    have he := heq zs hz
    subst zs
    exact ⟨rfl, by simpa only [List.map_const', List.sum_replicate, smul_eq_mul] using hc⟩)
  have dd := Det.call (Det.mk2 (Det.var' (P := P) (env := [a]) (i := 0) rfl)
    (Det.var' (P := P) (env := [a]) (i := 0) rfl)) hd
  have wi := wt_list2_le a a
  apply FunAll.intro hp.entry
  refine dd.post fun cost hc => ⟨rfl, ?_⟩
  change cost ≤ linObjectNormalizeCost hm W
  unfold linObjectNormalizeCost
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hc
  have hb := Nat.mul_le_mul_right B wl
  dsimp only [B, W, a, xs, out, tmGlObjsVal] at *
  simp only [mapK] at *
  nlinarith

theorem linObjectNormalizeCost_poly (h : Membership) :
    PBU (fun _ W _ => linObjectNormalizeCost h W) := by
  simp only [linObjectNormalizeCost, linObjectNormalizeItemCost, linObjectFindCost,
    linObjectClassCost, linGroupEqCost, linGroupLeCost, linGroupMemberCost,
    Prim.boundSize, reduceCost, memCost]
  norm_poly

end GI.Impl
