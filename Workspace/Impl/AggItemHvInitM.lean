import Workspace.Impl.AggItemHvInitO

/-!
# Case 2a init program, part 3: the two cited calls in between

After the choice-free data (`itHvDaF`) the init program of Case 2a makes its two calls whose
result is not unique: the two label lifts (`it_hvLt_spec`, through **NormalizedFactor**) and the
group value of the kernel `K` (`it_hvKg_spec`, through **PointwiseStab**). Then it builds the kept
value (`itHvOutF`).

`itHvMF da lt kg out` on `[st, Px, Py]`:
1. `D = [[σ, (a b)(c d)], ctx, flag, gA]` by `da`;
2. the lifts `[a₀, a₀₁]` by `lt` on `[ctx, σ, (a b)(c d), flag]`;
3. the group value `kgv` by `kg` on `[[k, q], ps, Px]`;
4. the kept value by `out` on `[sv, [a₀, a₀₁], kgv, gA]`.

`it_hvM_spec` states this for callees given by their specifications, with any facts `Rl` of the
lifts and `Rk` of the group value.
-/

set_option linter.unusedSectionVars false

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encPts)

variable {k : ℕ}

/-- On `[st, Px, Py]`: the data, the lifts, the kernel and the kept value. -/
def itHvMF (da lt kg out : ℕ) : Expr :=
  .letE (.call da (.var 0))
  (.letE (.call lt (mk4 (.get (.var 1) (.nat 1)) (.get (.get (.var 1) (.nat 0)) (.nat 0))
      (.get (.get (.var 1) (.nat 0)) (.nat 1)) (.get (.var 1) (.nat 2))))
  (.letE (.call kg (mk3 (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)) (arg 1)))
    (.call out (mk4 (.get (arg 0) (.nat 0)) (.var 2) (.var 3) (.get (.var 1) (.nat 3))))))

/-- The overhead of `itHvMF`, for a bound `X` on the weights it reads. -/
def itHvMK (X : ℕ) : ℕ := 1000 * (X + 1)

set_option maxHeartbeats 2000000 in
/-- **The middle part of the init program.** -/
theorem it_hvM_spec {P : Program} {f da lt kg out : ℕ} (hf : P.funs[f]? = some (itHvMF da lt kg out))
    (sv kq psV fxV fyV cv Px Py s₁ s₂ ctx gAV : Val) (fl : ℕ)
    {Rl : Perm (Fin k) → Perm (Fin k) → Prop} {Rk : Val → Prop}
    {Ov : Perm (Fin k) → Perm (Fin k) → Val → Val} {cD cL cK BK cO : ℕ}
    (hda : FunDet P da (.list [.list [sv, kq, psV, fxV, fyV, cv], Px, Py])
      (.list [.list [s₁, s₂], ctx, .nat fl, gAV]) cD)
    (hlt : FunAll P lt (.list [ctx, s₁, s₂, .nat fl]) (fun w c => ∃ a₀ a₁,
      w = .list [encPerm a₀, encPerm a₁] ∧ Rl a₀ a₁ ∧ c ≤ cL))
    (hkg : FunAll P kg (.list [kq, psV, Px]) (fun w c => Rk w ∧ w.wt ≤ BK ∧ c ≤ cK))
    (hout : ∀ a₀ a₁ kgv, Rl a₀ a₁ → Rk kgv →
      FunDet P out (.list [sv, .list [encPerm a₀, encPerm a₁], kgv, gAV]) (Ov a₀ a₁ kgv) cO) :
    FunAll P f (.list [.list [sv, kq, psV, fxV, fyV, cv], Px, Py]) (fun w c => ∃ a₀ a₁ kgv,
      Rl a₀ a₁ ∧ Rk kgv ∧ w = Ov a₀ a₁ kgv ∧
      c ≤ cD + 2 * cL + cK + 5 * cO +
        itHvMK ((Val.list [.list [sv, kq, psV, fxV, fyV, cv], Px, Py]).wt + cD + cL + BK)) := by
  set st := Val.list [sv, kq, psV, fxV, fyV, cv] with hst
  set x := Val.list [st, Px, Py] with hx
  set D := Val.list [.list [s₁, s₂], ctx, .nat fl, gAV] with hD
  set X := x.wt + cD + cL + BK with hX
  set W := 10 * X + 10 with hW
  have ex : (Val.list [st, Px, Py]).wt = x.wt := rfl
  have est : (Val.list [sv, kq, psV, fxV, fyV, cv]).wt = st.wt := rfl
  have eD : (Val.list [.list [s₁, s₂], ctx, .nat fl, gAV]).wt = D.wt := rfl
  have wD : D.wt < cD := FunDet.wt_lt hda
  have wst : st.wt < x.wt := wt_le_wt_list (by simp)
  have wPx : Px.wt < x.wt := wt_le_wt_list (by simp)
  have wsv : sv.wt < st.wt := wt_le_wt_list (by simp)
  have wkq : kq.wt < st.wt := wt_le_wt_list (by simp)
  have wps : psV.wt < st.wt := wt_le_wt_list (by simp)
  have ws : (Val.list [s₁, s₂]).wt < D.wt := wt_le_wt_list (by simp)
  have ws₁ : s₁.wt < (Val.list [s₁, s₂]).wt := wt_le_wt_list (by simp)
  have ws₂ : s₂.wt < (Val.list [s₁, s₂]).wt := wt_le_wt_list (by simp)
  have wctx : ctx.wt < D.wt := wt_le_wt_list (by simp)
  have wfl : (Val.nat fl).wt < D.wt := wt_le_wt_list (by simp)
  have wgA : gAV.wt < D.wt := wt_le_wt_list (by simp)
  -- step 1: the data
  have d1 : Det P [x] (.call da (.var 0)) D (x.wt + 1 + cD + D.wt + 1) :=
    Det.call (Det.var' rfl) hda
  refine FunAll.intro hf (EvalAll.letE d1 fun v ca h1 => ?_)
  obtain ⟨rfl, hca⟩ := h1
  -- step 2: the lifts
  have a2 : StDC P [x, D] (mk4 (.get (.var 1) (.nat 1)) (.get (.get (.var 1) (.nat 0)) (.nat 0))
      (.get (.get (.var 1) (.nat 0)) (.nat 1)) (.get (.var 1) (.nat 2)))
      (.list [ctx, s₁, s₂, .nat fl]) 21 0 W := by
    have rD : ∀ (j : ℕ) (u : Val), [Val.list [s₁, s₂], ctx, .nat fl, gAV][j]? = some u → j ≤ 3 →
        StDC P [x, D] (.get (.var 1) (.nat j)) u 3 0 W := fun j u hj hj3 => by
      obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hj
      have := wt_getElem_lt [Val.list [s₁, s₂], ctx, .nat fl, gAV] j hj'
      exact StDC.get (StDC.var' rfl (by omega)) (StDC.nat j (by omega))
        (List.getElem?_eq_getElem hj') (by omega)
    have r0 := rD 0 _ rfl (by omega)
    have h4 := wt_list4_le ctx s₁ s₂ (.nat fl)
    exact (StDC.mk4 (rD 1 ctx rfl (by omega))
      (StDC.get r0 (StDC.nat 0 (by omega)) rfl (by omega))
      (StDC.get r0 (StDC.nat 1 (by omega)) rfl (by omega)) (rD 2 _ rfl (by omega))
      (by rw [hW, hX]; omega) (by omega)).mono (by omega) le_rfl
  refine EvalAll.letE (Ra := fun v c => ∃ a₀ a₁, v = .list [encPerm a₀, encPerm a₁] ∧
      Rl a₀ a₁ ∧ c ≤ 21 * (W + 1) + cL + cL + 1 ∧ v.wt < cL)
    (EvalAll.call_funAll a2.det fun v ca' h2 => ?_) fun v₂ c₂ h₂ => ?_
  · obtain ⟨rfl, hca'⟩ := h2
    refine hlt.wt_lt.mono fun w cb ⟨⟨a₀, a₁, hw, hR, hc⟩, hwt⟩ => ⟨a₀, a₁, hw, hR, by omega, by
      omega⟩
  obtain ⟨a₀, a₁, rfl, hR, hc₂, hw₂⟩ := h₂
  set lV := Val.list [encPerm a₀, encPerm a₁] with hlV
  -- step 3: the kernel
  have a3 : StDC P [x, D, lV] (mk3 (.get (arg 0) (.nat 1)) (.get (arg 0) (.nat 2)) (arg 1))
      (.list [kq, psV, Px]) 20 0 W := by
    have r0 := StDC.arg (P := P) (W := W) (vs := [st, Px, Py]) (rest := [D, lV]) (j := 0) rfl
      (by omega) (by omega) (by omega)
    have h3 := wt_list3_le kq psV Px
    exact (StDC.mk3 (StDC.get r0 (StDC.nat 1 (by omega)) rfl (by omega))
      (StDC.get r0 (StDC.nat 2 (by omega)) rfl (by omega))
      (StDC.arg (vs := [st, Px, Py]) (j := 1) rfl (by omega) (by omega) (by omega))
      (by omega) (by omega)).mono (by omega) le_rfl
  refine EvalAll.letE (Ra := fun v c => Rk v ∧ v.wt ≤ BK ∧ c ≤ 20 * (W + 1) + cK + BK + 1)
    (EvalAll.call_funAll a3.det fun v ca' h3 => ?_) fun v₃ c₃ h₃ => ?_
  · obtain ⟨rfl, hca'⟩ := h3
    exact hkg.mono fun w cb ⟨hR', hwt, hc⟩ => ⟨hR', hwt, by omega⟩
  obtain ⟨hRk, hw₃, hc₃⟩ := h₃
  -- step 4: the kept value
  have a4 : StDC P [x, D, lV, v₃] (mk4 (.get (arg 0) (.nat 0)) (.var 2) (.var 3)
      (.get (.var 1) (.nat 3))) (.list [sv, lV, v₃, gAV]) 20 0 W := by
    have r0 := StDC.arg (P := P) (W := W) (vs := [st, Px, Py]) (rest := [D, lV, v₃]) (j := 0) rfl
      (by omega) (by omega) (by omega)
    have h4 := wt_list4_le sv lV v₃ gAV
    exact (StDC.mk4 (StDC.get r0 (StDC.nat 0 (by omega)) rfl (by omega))
      (StDC.var' rfl (by omega)) (StDC.var' rfl (by omega))
      (StDC.get (StDC.var' rfl (by omega)) (StDC.nat 3 (by omega)) rfl (by omega))
      (by omega) (by omega)).mono (by omega) le_rfl
  have d4 := Det.call a4.det (hout a₀ a₁ v₃ hR hRk)
  have wO : (Ov a₀ a₁ v₃).wt < cO := FunDet.wt_lt (hout a₀ a₁ v₃ hR hRk)
  refine d4.post fun c' hc' => ⟨a₀, a₁, v₃, hR, hRk, rfl, ?_⟩
  unfold itHvMK
  omega

end GI.Impl
