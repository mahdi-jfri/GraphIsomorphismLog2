import Workspace.Impl.AggItemHvScr

/-!
# Case 2a: the branch step

The branch step runs the script of Lemma A.11 (`Halving.script`), one call at a time. The kept
value `w` of the case is `[0]` when the test of `halvingItem` fails, and otherwise
`w = [1, arg₀, arg₁, arg₂, a₀, a₀₁, gA]`: the values of the three kernel calls (on `x`, on
`y ∘ τ₀` and on `y ∘ τ₀ t`), the positions of `τ₀` and of `τ₀ t`, and generators of `A`.

The branch state is `[v, tb, w]` at the start of a branch and `[kst, u]` after an answer `u`,
with `kst = [s, w, …]` listing the stage `s` and the answers so far. The program `itHvBF`:

* stage `0`, `w = [0]`: return `[0, [⟨⟩, ⟨⟩, w]]` (the empty item);
* stage `0`, `w = [1, …]`: ask the call on `arg₀` and keep `[1, w]`;
* stage `1`: ask the call on `arg₁` and keep `[2, w, u₀]`;
* stage `2`: ask the call on `arg₂` and keep `[3, w, u₀, u₁]`;
* stage `3`: return the two pieces `itHvPcF` of `(a₀, u₀, u₁)` and `(a₀₁, u₀, u₂)`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Lang Equiv Equiv.Perm
open GI.Cited (Val encPerm encGroup)

variable {k : ℕ}

/-- **The branch step of Case 2a**, with the piece program at `pc`. -/
def itHvBF (pc : ℕ) : Expr :=
  .ite (.arith .eq (.length (.var 0)) (.nat 3))
    (.ite (.get (arg 2) (.nat 0))
      (mk4 (.nat 1) (.nat 1) (.get (arg 2) (.nat 1)) (mk2 (.nat 1) (arg 2)))
      (mk2 (.nat 0) (mk3 .nil .nil (arg 2))))
    (.letE (.get (arg 0) (.nat 0))
    (.letE (.get (arg 0) (.nat 1))
      (.ite (.arith .eq (.var 1) (.nat 1))
        (mk4 (.nat 1) (.nat 1) (.get (.var 2) (.nat 2)) (mk3 (.nat 2) (.var 2) (arg 1)))
        (.ite (.arith .eq (.var 1) (.nat 2))
          (mk4 (.nat 1) (.nat 1) (.get (.var 2) (.nat 3))
            (mk4 (.nat 3) (.var 2) (.get (arg 0) (.nat 2)) (arg 1)))
          (mk2 (.nat 0) (mk3
            (mk2 (.call pc (mk4 (.get (.var 2) (.nat 4)) (.get (arg 0) (.nat 2))
                (.get (arg 0) (.nat 3)) (.get (.var 2) (.nat 6))))
              (.call pc (mk4 (.get (.var 2) (.nat 5)) (.get (arg 0) (.nat 2)) (arg 1)
                (.get (.var 2) (.nat 6)))))
            .nil (.var 2)))))))

/-- The cost bound of the cheap stages, for inputs of weight at most `W`. -/
def itHvBC (W : ℕ) : ℕ := 1000 * (8 * W + 101)

/-- A value is lighter than a list that holds it. -/
theorem itHv_wt_mem {vs : List Val} {j : ℕ} {v : Val} (h : vs[j]? = some v) :
    v.wt < (Val.list vs).wt :=
  wt_le_wt_list (List.mem_of_getElem? h)

/-- The common start of the later stages: the stage `s` and the kept value. -/
theorem itHv_late {P : Program} (kst u : Val) {ks : List Val} (hk : kst = .list ks) {s : ℕ} {wv : Val}
    (h0 : ks[0]? = some (.nat s)) (h1 : ks[1]? = some wv) {W : ℕ}
    (hW : (Val.list [kst, u]).wt ≤ W) (h5 : 5 ≤ W) :
    StDC P [Val.list [kst, u]] (.arith .eq (.length (.var 0)) (.nat 3)) (.nat 0) 4 0 W ∧
    StDC P [Val.list [kst, u]] (.get (arg 0) (.nat 0)) (.nat s) 5 0 W ∧
    StDC P [Val.list [kst, u], .nat s] (.get (arg 0) (.nat 1)) wv 5 0 W := by
  subst hk
  have hks : (Val.list ks).wt < (Val.list [.list ks, u]).wt := itHv_wt_mem (j := 0) rfl
  have hs : (Val.nat s).wt < (Val.list ks).wt := itHv_wt_mem h0
  have hw : wv.wt < (Val.list ks).wt := itHv_wt_mem h1
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le 1
  have w3 := wt_nat_le 3
  refine ⟨?_, ?_, ?_⟩
  · have dl := StDC.length (vs := [.list ks, u])
      (StDC.var' (P := P) (env := [Val.list [.list ks, u]]) (i := 0) (W := W) rfl hW)
      (by simp; omega)
    exact StDC.arith' dl (StDC.nat 3 (by omega)) (by rfl) (by omega)
  · exact StDC.get (StDC.arg (vs := [.list ks, u]) rfl hW (by omega) (by omega))
      (StDC.nat 0 (by omega)) h0 (by omega)
  · exact StDC.get (StDC.arg (vs := [.list ks, u]) rfl hW (by omega) (by omega))
      (StDC.nat 1 (by omega)) h1 (by omega)

theorem itHv_wt_two (a b : Val) : a.wt + b.wt < (Val.list [a, b]).wt := by
  have := sum_wt_lt_wt_list [a, b]
  simpa using this

theorem itHv_wt_three (a b c : Val) : a.wt + b.wt + c.wt < (Val.list [a, b, c]).wt := by
  have := sum_wt_lt_wt_list [a, b, c]
  simp at this
  omega

theorem itHv_wt_four (a b c d : Val) :
    a.wt + b.wt + c.wt + d.wt < (Val.list [a, b, c, d]).wt := by
  have := sum_wt_lt_wt_list [a, b, c, d]
  simp at this
  omega

section Stages

variable {P : Program} {fb pc : ℕ} (hfb : P.funs[fb]? = some (itHvBF pc))
include hfb

/-- **Stage 0 with the empty item.** -/
theorem it_hvB_s0n (v tb : Val) :
    FunDet P fb (.list [v, tb, .list [.nat 0]])
      (.list [.nat 0, .list [.list [], .list [], .list [.nat 0]]])
      (itHvBC (Val.list [v, tb, .list [.nat 0]]).wt) := by
  obtain ⟨W, hW⟩ : ∃ W, W = 8 * (Val.list [v, tb, .list [.nat 0]]).wt + 100 := ⟨_, rfl⟩
  have hw0 : (Val.list [.nat 0]).wt < (Val.list [v, tb, .list [.nat 0]]).wt :=
    itHv_wt_mem (j := 2) rfl
  have w0 := wt_nat_le 0
  have w3 := wt_nat_le 3
  have hW4 : 4 ≤ W := by omega
  have g2 : StDC P [Val.list [v, tb, .list [.nat 0]]] (arg 2) (.list [.nat 0]) 3 0 W :=
    StDC.arg (vs := [v, tb, .list [.nat 0]]) rfl (by omega) (by omega) (by omega)
  have dl := StDC.length (vs := [v, tb, .list [.nat 0]])
    (StDC.var' (P := P) (env := [Val.list [v, tb, .list [.nat 0]]]) (i := 0) (W := W) rfl (by omega))
    (by simp; omega)
  have dc : StDC P [Val.list [v, tb, .list [.nat 0]]] (.arith .eq (.length (.var 0)) (.nat 3))
      (.nat 1) 4 0 W :=
    StDC.arith' dl (StDC.nat 3 (by omega)) (by rfl) (by omega)
  have dg := StDC.get g2 (StDC.nat 0 (by omega)) (vs := [.nat 0]) (v := .nat 0) rfl (by omega)
  have wo1 := wt_list3_le (.list []) (.list []) (.list [.nat 0])
  have wo2 := wt_list2_le (.nat 0) (.list [.list [], .list [], .list [.nat 0]])
  have hn : (Val.list []).wt = 4 := wt_list_nil
  have hout : (Val.list [.nat 0, .list [.list [], .list [], .list [.nat 0]]]).wt ≤ W := by omega
  have d0 := itHv_ite0 (t := mk4 (.nat 1) (.nat 1) (.get (arg 2) (.nat 1)) (mk2 (.nat 1) (arg 2)))
    dg (StDC.mk2 (StDC.nat 0 (by omega)) (StDC.mk3 (StDC.nil hW4) (StDC.nil hW4) g2 (by omega) hW4)
      hout hW4) hout
  exact StDC.funDet hfb (itHv_ite1 dc one_ne_zero d0 hout) (by unfold itHvBC; omega)

/-- **Stage 0 with the halving item**: ask the call on `arg₀`. -/
theorem it_hvB_s0 (v tb : Val) {ws : List Val} {a0 : Val} (h0 : ws[0]? = some (.nat 1))
    (h1 : ws[1]? = some a0) :
    FunDet P fb (.list [v, tb, .list ws])
      (.list [.nat 1, .nat 1, a0, .list [.nat 1, .list ws]])
      (itHvBC (Val.list [v, tb, .list ws]).wt) := by
  obtain ⟨W, hW⟩ : ∃ W, W = 8 * (Val.list [v, tb, .list ws]).wt + 100 := ⟨_, rfl⟩
  have hw0 : (Val.list ws).wt < (Val.list [v, tb, .list ws]).wt := itHv_wt_mem (j := 2) rfl
  have ha0 : a0.wt < (Val.list ws).wt := itHv_wt_mem h1
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le 1
  have w3 := wt_nat_le 3
  have hW4 : 4 ≤ W := by omega
  have g2 : StDC P [Val.list [v, tb, .list ws]] (arg 2) (.list ws) 3 0 W :=
    StDC.arg (vs := [v, tb, .list ws]) rfl (by omega) (by omega) (by omega)
  have dl := StDC.length (vs := [v, tb, .list ws])
    (StDC.var' (P := P) (env := [Val.list [v, tb, .list ws]]) (i := 0) (W := W) rfl (by omega))
    (by simp; omega)
  have dc : StDC P [Val.list [v, tb, .list ws]] (.arith .eq (.length (.var 0)) (.nat 3))
      (.nat 1) 4 0 W :=
    StDC.arith' dl (StDC.nat 3 (by omega)) (by rfl) (by omega)
  have dg := StDC.get g2 (StDC.nat 0 (by omega)) h0 (by omega)
  have da := StDC.get g2 (StDC.nat 1 (by omega)) h1 (by omega)
  have wk := wt_list2_le (.nat 1) (.list ws)
  have wo := wt_list4_le (.nat 1) (.nat 1) a0 (.list [.nat 1, .list ws])
  have hout : (Val.list [.nat 1, .nat 1, a0, .list [.nat 1, .list ws]]).wt ≤ W := by omega
  have d0 := itHv_ite1 (e := mk2 (.nat 0) (mk3 .nil .nil (arg 2))) dg one_ne_zero
    (StDC.mk4 (StDC.nat 1 (by omega)) (StDC.nat 1 (by omega)) da
      (StDC.mk2 (StDC.nat 1 (by omega)) g2 (by omega) hW4) hout hW4) hout
  exact StDC.funDet hfb (itHv_ite1 dc one_ne_zero d0 hout) (by unfold itHvBC; omega)

/-- **Stage 1**: ask the call on `arg₁`. -/
theorem it_hvB_s1 {ws : List Val} {a1 : Val} (h2 : ws[2]? = some a1) (u : Val) :
    FunDet P fb (.list [.list [.nat 1, .list ws], u])
      (.list [.nat 1, .nat 1, a1, .list [.nat 2, .list ws, u]])
      (itHvBC (Val.list [.list [.nat 1, .list ws], u]).wt) := by
  obtain ⟨W, hW⟩ : ∃ W, W = 8 * (Val.list [.list [.nat 1, .list ws], u]).wt + 100 := ⟨_, rfl⟩
  have hk : (Val.list [.nat 1, .list ws]).wt < (Val.list [.list [.nat 1, .list ws], u]).wt :=
    itHv_wt_mem (j := 0) rfl
  have hu : u.wt < (Val.list [.list [.nat 1, .list ws], u]).wt := itHv_wt_mem (j := 1) rfl
  have hs2 := itHv_wt_two (.list [.nat 1, .list ws]) u
  have hw : (Val.list ws).wt < (Val.list [.nat 1, .list ws]).wt := itHv_wt_mem (j := 1) rfl
  have ha : a1.wt < (Val.list ws).wt := itHv_wt_mem h2
  have w1 := wt_nat_le 1
  have w2 := wt_nat_le 2
  have hW4 : 4 ≤ W := by omega
  obtain ⟨dc, ds, dw⟩ := itHv_late (P := P) (.list [.nat 1, .list ws]) u rfl
    (ks := [.nat 1, .list ws]) (s := 1) rfl rfl (W := W) (by omega) (by omega)
  set E := [Val.list [.list [.nat 1, .list ws], u], .nat 1, .list ws]
  have v1 : StDC P E (.var 1) (.nat 1) 1 0 W := StDC.var' rfl (by omega)
  have v2 : StDC P E (.var 2) (.list ws) 1 0 W := StDC.var' rfl (by omega)
  have g1 : StDC P E (arg 1) u 3 0 W :=
    StDC.arg (vs := [.list [.nat 1, .list ws], u]) rfl (by omega) (by omega) (by omega)
  have de : StDC P E (.arith .eq (.var 1) (.nat 1)) (.nat 1) 3 0 W :=
    StDC.arith' v1 (StDC.nat 1 (by omega)) (by rfl) (by omega)
  have da := StDC.get v2 (StDC.nat 2 (by omega)) h2 (by omega)
  have wk := wt_list3_le (.nat 2) (.list ws) u
  have wo := wt_list4_le (.nat 1) (.nat 1) a1 (.list [.nat 2, .list ws, u])
  have hout : (Val.list [.nat 1, .nat 1, a1, .list [.nat 2, .list ws, u]]).wt ≤ W := by omega
  have d4 := StDC.mk4 (StDC.nat 1 (by omega)) (StDC.nat 1 (by omega)) da
      (StDC.mk3 (StDC.nat 2 (by omega)) v2 g1 (by omega) hW4) hout hW4
  exact StDC.funDet hfb (itHv_ite0 dc (StDC.letE ds (StDC.letE dw
    (itHv_ite1 de one_ne_zero d4 hout) hout) hout) hout) (by unfold itHvBC; omega)

/-- **Stage 2**: ask the call on `arg₂`. -/
theorem it_hvB_s2 {ws : List Val} {a2 : Val} (h3 : ws[3]? = some a2) (u0 u : Val) :
    FunDet P fb (.list [.list [.nat 2, .list ws, u0], u])
      (.list [.nat 1, .nat 1, a2, .list [.nat 3, .list ws, u0, u]])
      (itHvBC (Val.list [.list [.nat 2, .list ws, u0], u]).wt) := by
  obtain ⟨W, hW⟩ : ∃ W, W = 8 * (Val.list [.list [.nat 2, .list ws, u0], u]).wt + 100 :=
    ⟨_, rfl⟩
  have hk : (Val.list [.nat 2, .list ws, u0]).wt <
      (Val.list [.list [.nat 2, .list ws, u0], u]).wt := itHv_wt_mem (j := 0) rfl
  have hu : u.wt < (Val.list [.list [.nat 2, .list ws, u0], u]).wt := itHv_wt_mem (j := 1) rfl
  have hs2 := itHv_wt_two (.list [.nat 2, .list ws, u0]) u
  have hs3 := itHv_wt_three (.nat 2) (.list ws) u0
  have hw : (Val.list ws).wt < (Val.list [.nat 2, .list ws, u0]).wt := itHv_wt_mem (j := 1) rfl
  have hu0 : u0.wt < (Val.list [.nat 2, .list ws, u0]).wt := itHv_wt_mem (j := 2) rfl
  have ha : a2.wt < (Val.list ws).wt := itHv_wt_mem h3
  have w1 := wt_nat_le 1
  have w2 := wt_nat_le 2
  have w3 := wt_nat_le 3
  have hW4 : 4 ≤ W := by omega
  obtain ⟨dc, ds, dw⟩ := itHv_late (P := P) (.list [.nat 2, .list ws, u0]) u rfl
    (ks := [.nat 2, .list ws, u0]) (s := 2) rfl rfl (W := W) (by omega) (by omega)
  set E := [Val.list [.list [.nat 2, .list ws, u0], u], .nat 2, .list ws]
  have v1 : StDC P E (.var 1) (.nat 2) 1 0 W := StDC.var' rfl (by omega)
  have v2 : StDC P E (.var 2) (.list ws) 1 0 W := StDC.var' rfl (by omega)
  have g1 : StDC P E (arg 1) u 3 0 W :=
    StDC.arg (vs := [.list [.nat 2, .list ws, u0], u]) rfl (by omega) (by omega) (by omega)
  have g0 : StDC P E (arg 0) (.list [.nat 2, .list ws, u0]) 3 0 W :=
    StDC.arg (vs := [.list [.nat 2, .list ws, u0], u]) rfl (by omega) (by omega) (by omega)
  have gu0 := StDC.get g0 (StDC.nat 2 (by omega)) (vs := [.nat 2, .list ws, u0]) (v := u0) rfl
    (by omega)
  have de1 : StDC P E (.arith .eq (.var 1) (.nat 1)) (.nat 0) 3 0 W :=
    StDC.arith' v1 (StDC.nat 1 (by omega)) (by rfl) (by omega)
  have de2 : StDC P E (.arith .eq (.var 1) (.nat 2)) (.nat 1) 3 0 W :=
    StDC.arith' v1 (StDC.nat 2 (by omega)) (by rfl) (by omega)
  have da := StDC.get v2 (StDC.nat 3 (by omega)) h3 (by omega)
  have wk := wt_list4_le (.nat 3) (.list ws) u0 u
  have wo := wt_list4_le (.nat 1) (.nat 1) a2 (.list [.nat 3, .list ws, u0, u])
  have hout : (Val.list [.nat 1, .nat 1, a2, .list [.nat 3, .list ws, u0, u]]).wt ≤ W := by
    omega
  have d5 := StDC.mk4 (StDC.nat 1 (by omega)) (StDC.nat 1 (by omega))
      da (StDC.mk4 (StDC.nat 3 (by omega)) v2 gu0 g1 (by omega) hW4) hout hW4
  exact StDC.funDet hfb (itHv_ite0 dc (StDC.letE ds (StDC.letE dw
    (itHv_ite0 de1 (itHv_ite1 de2 one_ne_zero d5 hout) hout) hout) hout) hout)
    (by unfold itHvBC; omega)

/-- The cost bound of the last stage, with the cost `Cp` of each piece. -/
def itHvB3C (W Cp : ℕ) : ℕ := 1000 * (8 * W + 16 * Cp + 101) + 2 * Cp

set_option maxHeartbeats 1000000 in
/-- **Stage 3**: the two pieces. -/
theorem it_hvB_s3 {ws : List Val} {r0 r1 gv : Val} (h4 : ws[4]? = some r0)
    (h5 : ws[5]? = some r1) (h6 : ws[6]? = some gv) (u0 u1 u : Val) {p1 p2 : Val} {Cp : ℕ}
    (hp1 : FunDet P pc (.list [r0, u0, u1, gv]) p1 Cp)
    (hp2 : FunDet P pc (.list [r1, u0, u, gv]) p2 Cp) :
    FunDet P fb (.list [.list [.nat 3, .list ws, u0, u1], u])
      (.list [.nat 0, .list [.list [p1, p2], .list [], .list ws]])
      (itHvB3C (Val.list [.list [.nat 3, .list ws, u0, u1], u]).wt Cp) := by
  have wp1 := FunDet.wt_lt hp1
  have wp2 := FunDet.wt_lt hp2
  obtain ⟨W, hW⟩ : ∃ W, W = 8 * (Val.list [.list [.nat 3, .list ws, u0, u1], u]).wt + 16 * Cp + 100 := ⟨_, rfl⟩
  have hk : (Val.list [.nat 3, .list ws, u0, u1]).wt < (Val.list [.list [.nat 3, .list ws, u0, u1], u]).wt := itHv_wt_mem (j := 0) rfl
  have hu : u.wt < (Val.list [.list [.nat 3, .list ws, u0, u1], u]).wt := itHv_wt_mem (j := 1) rfl
  have hs2 := itHv_wt_two (.list [.nat 3, .list ws, u0, u1]) u
  have hs4 := itHv_wt_four (.nat 3) (.list ws) u0 u1
  have hr0 : r0.wt < (Val.list ws).wt := itHv_wt_mem h4
  have hr1 : r1.wt < (Val.list ws).wt := itHv_wt_mem h5
  have hg : gv.wt < (Val.list ws).wt := itHv_wt_mem h6
  have w1 := wt_nat_le 1
  have w2 := wt_nat_le 2
  have w3 := wt_nat_le 3
  have w4 := wt_nat_le 4
  have w5 := wt_nat_le 5
  have w6 := wt_nat_le 6
  have hW4 : 4 ≤ W := by omega
  obtain ⟨dc, ds, dw⟩ := itHv_late (P := P) (.list [.nat 3, .list ws, u0, u1]) u rfl
    (ks := [.nat 3, .list ws, u0, u1]) (s := 3) rfl rfl (W := W) (by omega) (by omega)
  set E := [(Val.list [.list [.nat 3, .list ws, u0, u1], u]), .nat 3, .list ws]
  have v1 : StDC P E (.var 1) (.nat 3) 1 0 W := StDC.var' rfl (by omega)
  have v2 : StDC P E (.var 2) (.list ws) 1 0 W := StDC.var' rfl (by omega)
  have g1 : StDC P E (arg 1) u 3 0 W :=
    StDC.arg (vs := [.list [.nat 3, .list ws, u0, u1], u]) rfl (by omega) (by omega) (by omega)
  have g0 : StDC P E (arg 0) (.list [.nat 3, .list ws, u0, u1]) 3 0 W :=
    StDC.arg (vs := [.list [.nat 3, .list ws, u0, u1], u]) rfl (by omega) (by omega) (by omega)
  have gu0 := StDC.get g0 (StDC.nat 2 (by omega)) (vs := [.nat 3, .list ws, u0, u1]) (v := u0)
    rfl (by omega)
  have gu1 := StDC.get g0 (StDC.nat 3 (by omega)) (vs := [.nat 3, .list ws, u0, u1]) (v := u1)
    rfl (by omega)
  have de1 : StDC P E (.arith .eq (.var 1) (.nat 1)) (.nat 0) 3 0 W :=
    StDC.arith' v1 (StDC.nat 1 (by omega)) (by rfl) (by omega)
  have de2 : StDC P E (.arith .eq (.var 1) (.nat 2)) (.nat 0) 3 0 W :=
    StDC.arith' v1 (StDC.nat 2 (by omega)) (by rfl) (by omega)
  have dr0 := StDC.get v2 (StDC.nat 4 (by omega)) h4 (by omega)
  have dr1 := StDC.get v2 (StDC.nat 5 (by omega)) h5 (by omega)
  have dgv := StDC.get v2 (StDC.nat 6 (by omega)) h6 (by omega)
  have wi1 := wt_list4_le r0 u0 u1 gv
  have wi2 := wt_list4_le r1 u0 u gv
  have dP1 := StDC.call (StDC.mk4 dr0 gu0 gu1 dgv (by omega) hW4) hp1 (by omega)
  have dP2 := StDC.call (StDC.mk4 dr1 gu0 g1 dgv (by omega) hW4) hp2 (by omega)
  have wq := wt_list2_le p1 p2
  have wr := wt_list3_le (.list [p1, p2]) (.list []) (.list ws)
  have hn : (Val.list []).wt = 4 := wt_list_nil
  have w0 := wt_nat_le 0
  have wo := wt_list2_le (.nat 0) (.list [.list [p1, p2], .list [], .list ws])
  have hout : (Val.list [.nat 0, .list [.list [p1, p2], .list [], .list ws]]).wt ≤ W := by
    omega
  have d6 := StDC.mk2 (StDC.nat 0 (by omega)) (StDC.mk3 (StDC.mk2 dP1 dP2 (by omega) hW4)
    (StDC.nil hW4) v2 (by omega) hW4) hout hW4
  refine StDC.funDet hfb (itHv_ite0 dc (StDC.letE ds (StDC.letE dw
    (itHv_ite0 de1 (itHv_ite0 de2 d6 hout) hout) hout) hout) hout) ?_
  unfold itHvB3C
  omega

end Stages

end GI.Impl
