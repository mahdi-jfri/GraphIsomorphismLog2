import Workspace.Impl.AggItemHvInitD

/-!
# Case 2a init program, part 2: the kept value

Once the lifts `a₀ = τ₀` and `a₀₁ = τ₀ t` (on positions) and a group value `kgv` of the kernel
`K` are known, the kept value of Case 2a (`ItHvKept`) is

`[1, winVal' k kgv dv xv xv hv N, winVal' k kgv dv xv y₀ hv N, winVal' k kgv dv xv y₁ hv N,
  a₀, a₀₁, gA]`,

where `[k, gv, dv, xv, yv, hv, rv, fv, hh, N]` is the canonical value of the state and
`y₀`, `y₁` are the colors `y ∘ τ₀` and `y ∘ τ₀ t` (`it_hvCol_spec`). These are the canonical values
of the three kernel calls on `x`, `y ∘ τ₀` and `y ∘ τ₀ t` (`it_hv_canon`).

`itHvOutF` builds this value from `[sv, [a₀, a₀₁], kgv, gA]` (`it_hvOut_spec`).
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPts)

variable {Ω C : Type} {k : ℕ}

/-- Reading entry `j` of entry `i` of the argument. -/
theorem itHv_rd {P : Program} {vs rest us : List Val} {i j W : ℕ} {v : Val}
    (hi : vs[i]? = some (.list us)) (hj : us[j]? = some v) (hW : (Val.list vs).wt ≤ W)
    (hi2 : i + 2 ≤ W) (hj2 : j + 2 ≤ W) :
    StDC P (.list vs :: rest) (.get (arg i) (.nat j)) v 5 0 W := by
  obtain ⟨hi', hvs⟩ := List.getElem?_eq_some_iff.mp hi
  have w1 := wt_getElem_lt vs i hi'
  rw [hvs] at w1
  obtain ⟨hj', hv⟩ := List.getElem?_eq_some_iff.mp hj
  have w2 := wt_getElem_lt us j hj'
  rw [hv] at w2
  exact StDC.get (StDC.arg hi hW hi2 (by omega)) (StDC.nat j hj2) hj (by omega)

/-- The window value of a kernel call, as an expression over `[sv, lt, kgv, gA]`. -/
def itHvWinE (z : Expr) : Expr :=
  Expr.mkList [.get (arg 0) (.nat 0), arg 2, .get (arg 0) (.nat 2), .get (arg 0) (.nat 3), z,
    .get (arg 0) (.nat 5), .nil, .nat 0, .nat 2, .get (arg 0) (.nat 9)]

/-- On `[sv, [a₀, a₀₁], kgv, gA]`: the kept value of Case 2a. -/
def itHvOutF (col : ℕ) : Expr :=
  .letE (.call col (mk2 (.get (arg 0) (.nat 4)) (.get (arg 1) (.nat 0))))
  (.letE (.call col (mk2 (.get (arg 0) (.nat 4)) (.get (arg 1) (.nat 1))))
    (Expr.mkList [.nat 1, itHvWinE (.get (arg 0) (.nat 3)), itHvWinE (.var 1),
      itHvWinE (.var 2), .get (arg 1) (.nat 0), .get (arg 1) (.nat 1), arg 3]))

/-- The cost bound of `itHvOutF`, for a size `M` at least the input weight. -/
def itHvOutC (M : ℕ) : ℕ := 10 ^ 5 * gatherK * (4 * M + 8) ^ 3

theorem itHvOutC_mono {a b : ℕ} (h : a ≤ b) : itHvOutC a ≤ itHvOutC b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)

/-- The colors of `y ∘ e⁻¹ a`, as `it_hvCol_spec` returns them. -/
noncomputable def itHvYv (e : Ω ≃ Fin k) (c : C → ℕ) (y : Ω → C) (a : Perm (Fin k)) : Val :=
  encFun fun i => c ((y ∘ (toFin e).symm a) (e.symm i))

theorem itHvYv_colorVal (e : Ω ≃ Fin k) (c : C → ℕ) (y : Ω → C) (a : Perm (Fin k)) :
    ColorVal e c (itHvYv e c y a) (y ∘ (toFin e).symm a) := rfl

set_option maxHeartbeats 2000000 in
/-- **The kept value as a program.** -/
theorem it_hvOut_spec {P : Program} {f col : ℕ} (hf : P.funs[f]? = some (itHvOutF col))
    (hga : P.HasAt col (gatherFuns col)) {e : Ω ≃ Fin k} {c : C → ℕ} {y : Ω → C}
    (gv dv xv yv hv rv fv hh : Val) (N : ℕ) (hyv : ColorVal e c yv y) (a₀ a₁ : Perm (Fin k))
    (kgv gAV : Val) {M : ℕ}
    (hM : (Val.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N],
      .list [encPerm a₀, encPerm a₁], kgv, gAV]).wt ≤ M) :
    FunDet P f (.list [.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N],
      .list [encPerm a₀, encPerm a₁], kgv, gAV])
      (.list [.nat 1, winVal' k kgv dv xv xv hv N, winVal' k kgv dv xv (itHvYv e c y a₀) hv N,
        winVal' k kgv dv xv (itHvYv e c y a₁) hv N, encPerm a₀, encPerm a₁, gAV])
      (itHvOutC M) := by
  set sv := Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N] with hsv
  set lt := Val.list [encPerm a₀, encPerm a₁] with hlt
  set inp := Val.list [sv, lt, kgv, gAV] with hinp
  set y₀ := itHvYv e c y a₀ with hy₀
  set y₁ := itHvYv e c y a₁ with hy₁
  have ei : (Val.list [sv, lt, kgv, gAV]).wt = inp.wt := rfl
  have es : (Val.list [.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N]).wt = sv.wt := rfl
  have el : (Val.list [encPerm a₀, encPerm a₁]).wt = lt.wt := rfl
  have wsv : sv.wt < inp.wt := wt_le_wt_list (by simp [hinp])
  have wlt : lt.wt < inp.wt := wt_le_wt_list (by simp [hinp])
  have wkg : kgv.wt < inp.wt := wt_le_wt_list (by simp [hinp])
  have wgA : gAV.wt < inp.wt := wt_le_wt_list (by simp [hinp])
  have wyv : yv.wt < sv.wt := wt_le_wt_list (by simp [hsv])
  have wxv : xv.wt < sv.wt := wt_le_wt_list (by simp [hsv])
  have wdv : dv.wt < sv.wt := wt_le_wt_list (by simp [hsv])
  have whv : hv.wt < sv.wt := wt_le_wt_list (by simp [hsv])
  have wk : (Val.nat k).wt < sv.wt := wt_le_wt_list (by simp [hsv])
  have wN : (Val.nat N).wt < sv.wt := wt_le_wt_list (by simp [hsv])
  have wa₀ : (encPerm a₀).wt < lt.wt := wt_le_wt_list (by simp [hlt])
  have wa₁ : (encPerm a₁).wt < lt.wt := wt_le_wt_list (by simp [hlt])
  -- the gathers
  have hc₀ := it_hvCol_spec hga hyv a₀
  have hc₁ := it_hvCol_spec hga hyv a₁
  have g₀ : (Val.list [yv, encPerm a₀]).wt ≤ 4 * M + 6 := by
    have := wt_list2_le yv (encPerm a₀); omega
  have g₁ : (Val.list [yv, encPerm a₁]).wt ≤ 4 * M + 6 := by
    have := wt_list2_le yv (encPerm a₁); omega
  set G := gatherK * (4 * M + 7) ^ 3 with hG
  have hG₀ : gatherK * ((Val.list [yv, encPerm a₀]).wt + 1) ^ 3 ≤ G :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have hG₁ : gatherK * ((Val.list [yv, encPerm a₁]).wt + 1) ^ 3 ≤ G :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
  have v₀ := FunDet.wt_lt hc₀
  have v₁ := FunDet.wt_lt hc₁
  have hMG : M + 10 ≤ G := by
    have h1 : 4 * M + 7 ≤ (4 * M + 7) ^ 3 := Nat.le_self_pow (by norm_num) _
    have h2 : (4 * M + 7) ^ 3 ≤ gatherK * (4 * M + 7) ^ 3 :=
      Nat.le_mul_of_pos_left _ (by unfold gatherK; norm_num)
    omega
  -- the windows
  have ww : ∀ z : Val, (winVal' k kgv dv xv z hv N).wt ≤ 2 * (6 * M + z.wt + 20) + 14 := by
    intro z
    have h := wt_list_le [Val.nat k, kgv, dv, xv, z, hv, .list [], boolVal false, .nat 2, .nat N]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at h
    have := wt_boolVal_le false
    have := wt_nat_le 2
    unfold winVal'
    rw [wt_list_nil] at h
    omega
  set W := 100 * G + 100 with hW
  have hy0w : y₀.wt ≤ G := by rw [hy₀]; unfold itHvYv; omega
  have hy1w : y₁.wt ≤ G := by rw [hy₁]; unfold itHvYv; omega
  have hxw := ww xv
  have hw0 := ww y₀
  have hw1 := ww y₁
  have hout : (Val.list [.nat 1, winVal' k kgv dv xv xv hv N, winVal' k kgv dv xv y₀ hv N,
      winVal' k kgv dv xv y₁ hv N, encPerm a₀, encPerm a₁, gAV]).wt ≤ W := by
    have h := wt_list_le [.nat 1, winVal' k kgv dv xv xv hv N, winVal' k kgv dv xv y₀ hv N,
      winVal' k kgv dv xv y₁ hv N, encPerm a₀, encPerm a₁, gAV]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at h
    have := wt_nat_le 1
    omega
  -- the reads
  have rS : ∀ (rest : List Val) (j : ℕ) (v : Val),
      [Val.nat k, gv, dv, xv, yv, hv, rv, fv, hh, .nat N][j]? = some v → j ≤ 9 →
      StDC P (inp :: rest) (.get (arg 0) (.nat j)) v 5 0 W := fun rest j v hj hj9 =>
    itHv_rd (vs := [sv, lt, kgv, gAV]) (i := 0) rfl hj (by omega) (by omega) (by omega)
  have rL : ∀ (rest : List Val) (j : ℕ) (v : Val), [encPerm a₀, encPerm a₁][j]? = some v →
      j ≤ 1 → StDC P (inp :: rest) (.get (arg 1) (.nat j)) v 5 0 W := fun rest j v hj hj9 =>
    itHv_rd (vs := [sv, lt, kgv, gAV]) (i := 1) rfl hj (by omega) (by omega) (by omega)
  have rA : ∀ (rest : List Val) (j : ℕ) (v : Val), [sv, lt, kgv, gAV][j]? = some v → j ≤ 3 →
      StDC P (inp :: rest) (arg j) v 3 0 W := fun rest j v hj hj3 => by
    obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hj
    have := wt_getElem_lt [sv, lt, kgv, gAV] j hj'
    exact StDC.arg (List.getElem?_eq_getElem hj') (by omega) (by omega) (by omega)
  have d1 : StDC P [inp] (.call col (mk2 (.get (arg 0) (.nat 4)) (.get (arg 1) (.nat 0)))) y₀ 14
      G W :=
    (StDC.call (StDC.mk2 (rS [] 4 yv rfl (by omega)) (rL [] 0 _ rfl (by omega))
      (by omega) (by omega)) (hc₀.mono hG₀) (by omega)).mono le_rfl (by omega)
  have d2 : StDC P [inp, y₀] (.call col (mk2 (.get (arg 0) (.nat 4)) (.get (arg 1) (.nat 1)))) y₁
      14 G W :=
    (StDC.call (StDC.mk2 (rS [y₀] 4 yv rfl (by omega)) (rL [y₀] 1 _ rfl (by omega))
      (by omega) (by omega)) (hc₁.mono hG₁) (by omega)).mono le_rfl (by omega)
  set env := [inp, y₀, y₁] with henv
  -- a window, from the read of its fifth entry
  have dW : ∀ (ez : Expr) (z : Val), StDC P env ez z 5 0 W → z.wt ≤ G →
      Det P env (itHvWinE ez) (winVal' k kgv dv xv z hv N) (10 * (6 * (W + 1) + W + 1) + 5) := by
    intro ez z hz hzw
    have h := Det.mkList (P := P) (env := env) (c := 6 * (W + 1))
      [(.get (arg 0) (.nat 0), .nat k), (arg 2, kgv), (.get (arg 0) (.nat 2), dv),
        (.get (arg 0) (.nat 3), xv), (ez, z), (.get (arg 0) (.nat 5), hv), (.nil, .list []),
        (.nat 0, .nat 0), (.nat 2, .nat 2), (.get (arg 0) (.nat 9), .nat N)] (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (rS _ 0 _ rfl (by omega)).det.mono (by omega)
      · exact (rA _ 2 _ rfl (by omega)).det.mono (by omega)
      · exact (rS _ 2 _ rfl (by omega)).det.mono (by omega)
      · exact (rS _ 3 _ rfl (by omega)).det.mono (by omega)
      · exact hz.det.mono (by omega)
      · exact (rS _ 5 _ rfl (by omega)).det.mono (by omega)
      · exact Det.nil.mono (by omega)
      · exact (Det.nat 0).mono (by omega)
      · exact (Det.nat 2).mono (by omega)
      · exact (rS _ 9 _ rfl (by omega)).det.mono (by omega))
    have hwz := ww z
    refine h.mono ?_
    show 10 * (6 * (W + 1) + (winVal' k kgv dv xv z hv N).wt + 1) + 5 ≤ _
    omega
  have dx : StDC P env (.get (arg 0) (.nat 3)) xv 5 0 W := rS _ 3 _ rfl (by omega)
  have dy0 : StDC P env (.var 1) y₀ 5 0 W := (StDC.var' rfl (by omega)).mono (by omega) le_rfl
  have dy1 : StDC P env (.var 2) y₁ 5 0 W := (StDC.var' rfl (by omega)).mono (by omega) le_rfl
  have hxG : xv.wt ≤ G := by omega
  have d3 : Det P env (Expr.mkList [.nat 1, itHvWinE (.get (arg 0) (.nat 3)), itHvWinE (.var 1),
      itHvWinE (.var 2), .get (arg 1) (.nat 0), .get (arg 1) (.nat 1), arg 3])
      (.list [.nat 1, winVal' k kgv dv xv xv hv N, winVal' k kgv dv xv y₀ hv N,
        winVal' k kgv dv xv y₁ hv N, encPerm a₀, encPerm a₁, gAV])
      (7 * (10 * (6 * (W + 1) + W + 1) + 5 + W + 1) + 5) := by
    have h := Det.mkList (P := P) (env := env) (c := 10 * (6 * (W + 1) + W + 1) + 5)
      [(.nat 1, .nat 1), (itHvWinE (.get (arg 0) (.nat 3)), winVal' k kgv dv xv xv hv N),
        (itHvWinE (.var 1), winVal' k kgv dv xv y₀ hv N),
        (itHvWinE (.var 2), winVal' k kgv dv xv y₁ hv N), (.get (arg 1) (.nat 0), encPerm a₀),
        (.get (arg 1) (.nat 1), encPerm a₁), (arg 3, gAV)] (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (Det.nat 1).mono (by omega)
      · exact dW _ _ dx hxG
      · exact dW _ _ dy0 hy0w
      · exact dW _ _ dy1 hy1w
      · exact (rL _ 0 _ rfl (by omega)).det.mono (by omega)
      · exact (rL _ 1 _ rfl (by omega)).det.mono (by omega)
      · exact (rA _ 3 _ rfl (by omega)).det.mono (by omega))
    refine h.mono ?_
    show 7 * (10 * (6 * (W + 1) + W + 1) + 5 + (Val.list [.nat 1, winVal' k kgv dv xv xv hv N,
      winVal' k kgv dv xv y₀ hv N, winVal' k kgv dv xv y₁ hv N, encPerm a₀, encPerm a₁,
      gAV]).wt + 1) + 5 ≤ _
    omega
  have d3' : StDC P env (Expr.mkList [.nat 1, itHvWinE (.get (arg 0) (.nat 3)), itHvWinE (.var 1),
      itHvWinE (.var 2), .get (arg 1) (.nat 0), .get (arg 1) (.nat 1), arg 3])
      (.list [.nat 1, winVal' k kgv dv xv xv hv N, winVal' k kgv dv xv y₀ hv N,
        winVal' k kgv dv xv y₁ hv N, encPerm a₀, encPerm a₁, gAV]) 600 0 W :=
    d3.mono (by omega)
  have dall := StDC.letE d1 (StDC.letE d2 d3' hout) hout
  refine StDC.funDet hf dall ?_
  -- the cost
  have e3 : (4 * M + 8) ^ 3 ≥ (4 * M + 7) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have e4 : 10 ^ 5 * gatherK * (4 * M + 8) ^ 3 ≥ 10 ^ 5 * G := by
    rw [hG, ← Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ e3
  unfold itHvOutC
  omega

end GI.Impl
