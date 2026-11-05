module

public import Workspace.Impl.LinPrimaryStepSuccess

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang
set_option maxRecDepth 18000

theorem linDet_wt_le {P : Program} {env : List Val} {e : Expr} {out : Val} {c : ℕ}
    (h : Det P env e out c) : out.wt ≤ c := by
  obtain ⟨v, k, he, hv, hk⟩ := h.exists_eval
  subst v
  exact he.wt_lt.le.trans hk

theorem linPrimaryZero_spec {P : Program} {b p d : ℕ} (h : P.HasAt b (replicateFuns b)) :
    FunDet P b (.list [.nat d, .nat 0]) (encVec (0 : Fin d → ZMod p)) (100000 * (d + 1) ^ 3) := by
  have hh := replicate_spec h d (.nat 0)
  refine FunAll.mono hh fun out cost ho => ⟨?_, ?_⟩
  · rw [ho.1]
    simp [encVec]
  · have hw := linWtList (vs := List.replicate d (.nat 0)) (B := 2) (by
      intro v hv
      simp only [List.mem_replicate] at hv
      rcases hv with ⟨_, rfl⟩
      decide)
    simp only [List.length_replicate] at hw
    change (Val.list (List.replicate d (.nat 0))).wt ≤ _ at hw
    have hi := wt_list2_le (.nat d) (.nat 0)
    have hn := wt_nat_le d
    have hc := ho.2
    rw [ho.1] at hc
    simp only [loopModK] at hc
    have h0 : (Val.nat 0).wt = 2 := rfl
    have hb : (Val.list [.nat d, .nat 0]).wt + d +
        (Val.list (List.replicate d (.nat 0))).wt + 1 ≤ 100 * (d + 1) := by omega
    calc cost ≤ 1000 * (d + 1) * ((Val.list [.nat d, .nat 0]).wt + d +
        (Val.list (List.replicate d (.nat 0))).wt + 1) := hc
      _ ≤ 1000 * (d + 1) * (100 * (d + 1)) := Nat.mul_le_mul_left _ hb
      _ = 100000 * (d + 1) ^ 2 := by ring
      _ ≤ 100000 * (d + 1) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by decide))

set_option maxHeartbeats 1500000 in
theorem linPrimaryStepLayerArg_spec {P : Program} {n p d : ℕ} (gs : List (Equiv.Perm (Fin n)))
    (ν : Fin d → ℕ) (level : ℕ)
    (ρ : gens gs →* (linFiniteVec (linPrimaryOrders p ν) ≃+ linFiniteVec (linPrimaryOrders p ν)))
    (c : gens gs → linFiniteVec (linPrimaryOrders p ν)) (x : linFiniteVec (linPrimaryOrders p ν))
    (acc : Equiv.Perm (Fin n)) (zero : Val) :
    let a := linPrimaryIterationVal gs (linPrimaryOrders p ν) ρ c x acc p ν level
    Det P [a, zero] linPrimaryStepLayerArgE (.list [linPrimaryInputVal gs ν level ρ c x, zero])
      (100000 * (a.wt + zero.wt + 1)) := by
  let m := linPrimaryOrders p ν
  let ctx := linActionContext gs m ρ c
  let point := linFinitePointVal m x
  let a := linPrimaryIterationVal gs m ρ c x acc p ν level
  let dict := linGroupSlpTable (linFiniteAffineVal m ρ c) (linActionGens gs)
  have dctx := Det.arg' (P := P)
    (vs := [ctx, point, encPerm acc, .nat p, encFun ν, .nat level]) (rest := [zero]) (j := 0) rfl
  have dgroup := Det.get' dctx (Det.nat 0) rfl
  have ddict := Det.get' dctx (Det.nat 1) rfl
  have darg (k : ℕ) {v : Val}
      (hk : ([ctx, point, encPerm acc, .nat p, encFun ν, .nat level] : List Val)[k]? = some v) :=
    Det.arg' (P := P) (vs := [ctx, point, encPerm acc, .nat p, encFun ν, .nat level]) (rest := [zero]) (j := k) hk
  have dout := Det.mk2 (Det.snoc (Det.snoc (Det.mk4 dgroup (darg 3 rfl) (darg 4 rfl) (darg 5 rfl)) ddict)
    (darg 1 rfl)) (Det.var' (P := P) (env := [a, zero]) (i := 1) rfl)
  rw [linPrimaryInput_context]
  refine dout.mono ?_
  have wc : ctx.wt < a.wt := wt_le_wt_list (by simp [a, ctx, linPrimaryIterationVal])
  have wg : (encGroup gs).wt < ctx.wt := wt_le_wt_list (by simp [ctx, linActionContext])
  have wd : dict.wt < ctx.wt := wt_le_wt_list (by simp [ctx, dict, linActionContext])
  have wp : (Val.nat p).wt < a.wt := wt_le_wt_list (by simp [a, linPrimaryIterationVal])
  have wν : (encFun ν).wt < a.wt := wt_le_wt_list (by simp [a, linPrimaryIterationVal])
  have wl : (Val.nat level).wt < a.wt := wt_le_wt_list (by simp [a, linPrimaryIterationVal])
  have wx : point.wt < a.wt := wt_le_wt_list (by simp [a, point, linPrimaryIterationVal])
  have w4 := wt_list4_le (encGroup gs) (.nat p) (encFun ν) (.nat level)
  have w5 := wt_list_snoc_le [encGroup gs, .nat p, encFun ν, .nat level] dict
  have w6 := wt_list_snoc_le [encGroup gs, .nat p, encFun ν, .nat level, dict] point
  have wout := wt_list2_le (.list [encGroup gs, .nat p, encFun ν, .nat level, dict, point]) zero
  dsimp only [a, ctx, point, dict, m, darg, linPrimaryIterationVal] at *
  simp only [List.cons_append, List.nil_append] at *
  omega

set_option maxHeartbeats 1000000 in
theorem linPrimaryStep_zero_det {P : Program} {br n p d : ℕ}
    (h : P.HasAt br (replicateFuns br)) (gs : List (Equiv.Perm (Fin n)))
    (m : Fin d → ℕ) (ρ : gens gs →* (linFiniteVec m ≃+ linFiniteVec m))
    (c : gens gs → linFiniteVec m) (x : linFiniteVec m) (acc : Equiv.Perm (Fin n))
    (ν : Fin d → ℕ) (level : ℕ) :
    let a := linPrimaryIterationVal gs m ρ c x acc p ν level
    Det P [a] (.call br (mk2 (.length (arg 4)) (.nat 0))) (encVec (0 : Fin d → ZMod p))
      (100 * (a.wt + 100000 * (a.wt + 1) ^ 3 + 1)) := by
  let ctx := linActionContext gs m ρ c
  let point := linFinitePointVal m x
  let a := linPrimaryIterationVal gs m ρ c x acc p ν level
  let W := a.wt
  have wν : (encFun ν).wt < W := wt_le_wt_list (by simp [W, a, linPrimaryIterationVal])
  have hd : d ≤ W := by
    have hh := length_lt_wt_list ((List.finRange d).map fun i => Val.nat (ν i))
    simp only [List.length_map, List.length_finRange] at hh
    change d < (encFun ν).wt at hh
    omega
  have hz := (linPrimaryZero_spec (p := p) (d := d) h).mono
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hd 1) 3))
  have wz := hz.wt_lt.le
  have dν := Det.arg' (P := P)
    (vs := [ctx, point, encPerm acc, .nat p, encFun ν, .nat level]) (rest := []) (j := 4) rfl
  have dn := Det.length dν
  simp only [List.length_map, List.length_finRange] at dn
  have dd := Det.call (Det.mk2 dn (Det.nat 0)) hz
  refine dd.mono ?_
  have wsmall := wt_list2_le (.nat d) (.nat 0)
  have wd := wt_nat_le d
  have w0 : (Val.nat 0).wt = 2 := rfl
  dsimp only [ctx, point, a, W, linPrimaryIterationVal] at *
  omega

end GI.Impl
