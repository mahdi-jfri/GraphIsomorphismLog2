module

public import Workspace.Impl.LinWreathSwapTest
public import Workspace.Impl.LinWreathScanMath
public import Workspace.Impl.LinWreathExtract
public import Workspace.Lang.Prims.Repr

@[expose] public section

/-! Select a swapping stabilizer generator and extract its transporter. -/
namespace GI.Impl
open GI.Cited GI.Lang Equiv

def linWreathChoiceF (find extract : ℕ) : Expr :=
  .letE (.call find (mk2 (arg 0) (.get (arg 1) (.nat 1))))
    (.ite (.length (.var 1))
      (mk1 (.call extract (mk2 (arg 0) (.get (.var 1) (.nat 0))))) .nil)

def linWreathChoiceFuns (b : ℕ) : List Expr :=
  [linWreathChoiceF (b + 2) (b + 6), linWreathSwapTestF] ++
    transpFirstFuns (b + 2) (b + 1) ++ linWreathExtractFuns (b + 6)

theorem linWreathChoiceFuns_length (b : ℕ) : (linWreathChoiceFuns b).length = 15 := rfl

structure linWreathChoiceAt (P : Program) (b : ℕ) : Prop where
  entry : P.funs[b]? = some (linWreathChoiceF (b + 2) (b + 6))
  test : P.funs[b + 1]? = some linWreathSwapTestF
  find : P.HasAt (b + 2) (transpFirstFuns (b + 2) (b + 1))
  extract : linWreathExtractAt P (b + 6)

theorem linWreathChoiceAt_of {P : Program} {b : ℕ}
    (h : P.HasAt b (linWreathChoiceFuns b)) : linWreathChoiceAt P b where
  entry := (h.block (gs := [linWreathChoiceF (b + 2) (b + 6)]) 0 rfl).single
  test := (h.block (gs := [linWreathSwapTestF]) 1 rfl).single
  find := h.block 2 rfl
  extract := linWreathExtractAt_of (h.block 6 rfl)

def linWreathChoiceOut (I : VecStabInst) (w : Fin I.d → ZMod I.p) (out : Val) : Prop :=
  (out = .list [] ∧ ¬∃ g : gens I.gs, (I.φ g).val.mulVec I.v = w) ∨
    ∃ g : gens I.gs, out = .list [encPerm g.val] ∧ (I.φ g).val.mulVec I.v = w

def linWreathChoiceFindCost (W : ℕ) : ℕ := 10000 * (W + 1) * (100 * (W + 1) + 1)
def linWreathChoiceExtractCost (W : ℕ) : ℕ := linWreathExtractCost (100 * (W + 1)) W

def linWreathChoiceCost (W : ℕ) : ℕ :=
  100000 * (W + linWreathChoiceFindCost W + linWreathChoiceExtractCost W + 1)

theorem linWreathExtractCost_mono {W V n m : ℕ} (hW : W ≤ V) (hn : n ≤ m) :
    linWreathExtractCost W n ≤ linWreathExtractCost V m := by
  unfold linWreathExtractCost linTabulateCost linTabulateRangeCost linMapBudget
  gcongr

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 6000 in
theorem linWreathChoice_spec {P : Program} {b : ℕ} (h : linWreathChoiceAt P b)
    (I : VecStabInst) [NeZero I.n] (w : Fin I.d → ZMod I.p)
    (hs : List (Perm (Fin (I.n + I.n))))
    (hhs : gens hs = vecStabSub (linWreathVecInst I w)) :
    FunAll P b (.list [.nat I.n, encGroup hs]) (fun out cost => linWreathChoiceOut I w out ∧
      cost ≤ linWreathChoiceCost (Val.list [.nat I.n, encGroup hs]).wt) := by
  let a := Val.list [.nat I.n, encGroup hs]
  let W := a.wt
  let els := (1 : Perm (Fin (I.n + I.n))) :: hs
  let q : Perm (Fin (I.n + I.n)) → Bool := fun σ => decide (I.n ≤ (σ 0 : ℕ))
  let raw := Val.list (els.map encPerm)
  have wgroup : (encGroup hs).wt < W := wt_le_wt_list (by simp [W, a])
  have wn : (Val.nat I.n).wt < W := wt_le_wt_list (by simp [W, a])
  have wraw : raw.wt < (encGroup hs).wt := wt_le_wt_list (by simp [raw, els, encGroup, encPerms])
  have hlen : els.length ≤ W := by
    have hh := length_lt_wt_list (els.map encPerm)
    simp only [List.length_map] at hh
    change els.length < raw.wt at hh
    omega
  have hn : I.n ≤ W := by have hh := S_le_wt_encGroup hs; nlinarith
  have hn0 : 0 < I.n := Nat.pos_of_ne_zero (NeZero.ne I.n)
  have warg : (Val.list [.nat I.n, raw]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (.nat I.n) raw
    omega
  have wpoint (σ : Perm (Fin (I.n + I.n))) (hσ : σ ∈ els) :
      (Val.list [.nat I.n, encPerm σ]).wt ≤ 100 * (W + 1) := by
    have hh := wt_list2_le (.nat I.n) (encPerm σ)
    have hw : (encPerm σ).wt < raw.wt := wt_le_wt_list (List.mem_map.mpr ⟨σ, hσ, rfl⟩)
    omega
  have hfind := transpFirst_spec h.find els q (T := 1000 * (100 * (W + 1) + 1)) (fun σ hσ =>
    (linWreathSwapTest_spec h.test hn0 σ).mono (Nat.mul_le_mul_left _ (by have := wpoint σ hσ; omega)))
  have hfind' : FunDet P (b + 2) (.list [.nat I.n, raw])
      (.list ((els.find? q).toList.map encPerm)) (linWreathChoiceFindCost W) := by
    refine hfind.mono ?_
    unfold linWreathChoiceFindCost
    simp only [loopModK]
    have hh₁ := Nat.mul_le_mul_right (1000 * (100 * (W + 1) + 1)) (Nat.le_succ_of_le hlen)
    have hh₂ := Nat.mul_le_mul (by omega : 3000 * (els.length + 1) ≤ 3000 * (W + 1))
      (Nat.add_le_add_right warg 1)
    nlinarith
  have he : gens els = (vecStab (linWreathVecInst I w)).map
      (gens (linWreathCoverGenerators I.gs)).subtype := by
    rw [show gens els = gens hs by simp [els, gens_one_cons], hhs]; rfl
  have dn := Det.arg' (P := P) (vs := [.nat I.n, encGroup hs]) (rest := []) (j := 0) rfl
  have dg := Det.arg' (P := P) (vs := [.nat I.n, encGroup hs]) (rest := []) (j := 1) rfl
  have dr := Det.get' dg (Det.nat 1) rfl
  cases hres : els.find? q with
  | none =>
    have hf := hfind'
    rw [hres] at hf
    simp only [Option.toList_none, List.map_nil] at hf
    have dfind := Det.call (Det.mk2 dn dr) hf
    have dlen := Det.length (Det.var' (P := P) (env := [a, .list []]) (i := 1) rfl)
    have db := Det.letE dfind (Det.ite_zero (t := mk1 (.call (b + 6) (mk2 (arg 0) (.get (.var 1) (.nat 0))))) dlen Det.nil)
    have hno : ¬∃ g : gens I.gs, (I.φ g).val.mulVec I.v = w := by
      intro hg
      obtain ⟨σ, hσ, ht⟩ := (linWreathReturned_perms I w els he).mpr hg
      have hh := List.find?_eq_none.mp hres σ hσ
      have hq : q σ = true := by simp [q, ht]
      exact hh hq
    apply FunAll.intro h.entry
    refine db.post fun cost hc => ⟨Or.inl ⟨rfl, hno⟩, ?_⟩
    have w₀ : (Val.list []).wt = 4 := rfl
    have wi := wt_list2_le (.nat I.n) raw
    change cost ≤ linWreathChoiceCost W
    dsimp only [linWreathChoiceCost]
    dsimp only [a, W, raw, els, encGroup, encPerms] at *
    simp only [List.length_nil, List.length_cons, List.nil_append, wt_list_nil] at *
    omega
  | some σ =>
    have hσ := List.mem_of_find?_eq_some hres
    have hq := List.find?_some hres
    have htest : I.n ≤ (σ 0 : ℕ) := by simpa only [q, decide_eq_true_eq] using hq
    obtain ⟨x, hx, hcover, hswap, htrans⟩ := linWreathReturned_selected I w els he hσ htest
    have harg := wpoint σ hσ
    have hextract := linWreathExtract_spec h.extract I.gs x hswap
    rw [hcover] at hextract
    have hextract' := hextract.mono (linWreathExtractCost_mono harg hn)
    have hf := hfind'
    rw [hres] at hf
    simp only [Option.toList_some, List.map_cons, List.map_nil] at hf
    have dfind := Det.call (Det.mk2 dn dr) hf
    have dlen := Det.length (Det.var' (P := P) (env := [a, .list [encPerm σ]]) (i := 1) rfl)
    have dn' := Det.arg' (P := P) (vs := [.nat I.n, encGroup hs]) (rest := [.list [encPerm σ]]) (j := 0) rfl
    have ds := Det.get' (Det.var' (P := P) (env := [a, .list [encPerm σ]]) (i := 1) rfl) (Det.nat 0) rfl
    have dx := Det.call (Det.mk2 dn' ds) hextract'
    have db := Det.letE dfind (Det.ite_pos (e := .nil) dlen (by decide : 1 ≠ 0) (Det.mk1 dx))
    have wfound := hf.wt_lt.le
    have wσ : (encPerm σ).wt ≤ (Val.list [encPerm σ]).wt := (wt_le_wt_list (by simp)).le
    have wx := hextract'.wt_lt.le
    have wo := wt_list_snoc_le [] (encPerm (x.left linTwoSwap).val)
    have wi := wt_list2_le (.nat I.n) raw
    apply FunAll.intro h.entry
    refine db.post fun cost hc => ⟨Or.inr ⟨x.left linTwoSwap, rfl, htrans⟩, ?_⟩
    change cost ≤ linWreathChoiceCost W
    dsimp only [linWreathChoiceCost, linWreathChoiceExtractCost] at *
    dsimp only [a, W, raw, els, encGroup, encPerms] at *
    simp only [List.length_nil, List.length_cons, List.nil_append, wt_list_nil] at *
    omega

theorem linWreathChoiceCost_poly : PBU (fun _ W _ => linWreathChoiceCost W) := by
  simp only [linWreathChoiceCost, linWreathChoiceFindCost, linWreathChoiceExtractCost,
    linWreathExtractCost, linTabulateCost, linTabulateRangeCost, linMapBudget]
  norm_poly

end GI.Impl
