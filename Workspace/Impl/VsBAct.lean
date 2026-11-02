import Workspace.Impl.VsQApp
import Workspace.Impl.VsWProgCo
import Workspace.Lang.Lib.LinIntTail

/-!
# The affine action on local coordinates

A point of `(x + W)/W'` is written `x + ∑ c_j cs_j` with local coordinates `c` (`cs` the
complement of the frame). An element `g` moves the point with coordinates `c` to the point with
coordinates `vsBAct I ws' cs x g c`, the coordinates of `φ(g)(x + ∑ c_j cs_j) - x`.

* `vsBActFuns b phi` (57 functions), `vsBAct_spec`: on `[[Γ, fr, x], g, 0 :: c]` the key
  `0 :: vsBAct I ws' cs x g c`, as the small orbit transporter needs.
-/

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The point `x + ∑ c_j cs_j`. -/
def vsBPt (p d : ℕ) (cs : List (List ℕ)) (x c : List ℕ) : List ℕ :=
  vsLin p 1 1 x (vsFRowMul p c cs (vsWZ d))

/-- The coordinates of the image of the point with coordinates `c` under `g`. -/
noncomputable def vsBAct (I : VecStabInst) (ws' cs : List (List ℕ)) (x : List ℕ)
    (g : Perm (Fin I.n)) (c : List ℕ) : List ℕ :=
  vsWCo I.p ws' cs (vsLin I.p 1 (I.p - 1) (vsQApp I g⁻¹ (vsBPt I.p I.d cs x c)) x)

/-- Entry `k` of the frame in the context. -/
def vsBFr : Expr := .get (arg 0) (.nat 1)

/-- The action, on `[[Γ, fr, x], g, 0 :: c]`. -/
def vsBActF (tail row lin app inv co appd : ℕ) : Expr :=
  .call appd (mk2 (mk1 (.nat 0))
    (.call co (mk2 vsBFr
      (.call lin (.snoc (mk4 (.get (.get vsBFr (.nat 0)) (.nat 0)) (.nat 1)
          (.arith .sub (.get (.get vsBFr (.nat 0)) (.nat 0)) (.nat 1))
          (.call app (mk3 (.get (arg 0) (.nat 0)) (.call inv (arg 1))
            (.call lin (.snoc (mk4 (.get (.get vsBFr (.nat 0)) (.nat 0)) (.nat 1) (.nat 1)
              (.get (arg 0) (.nat 2)))
              (.call row (mk2 (mk3 (.get (.get vsBFr (.nat 0)) (.nat 0)) (.get vsBFr (.nat 2))
                (.get (.get vsBFr (.nat 0)) (.nat 2))) (.call tail (arg 2)))))))))
        (.get (arg 0) (.nat 2)))))))

/-- The action program at base `b` (57 functions); `phi` is outside. -/
def vsBActFuns (b phi : ℕ) : List Expr :=
  [vsBActF (b + 1) (b + 7) (b + 20) (b + 28) (b + 29) (b + 41) (b + 54)] ++ linTailFuns (b + 1) ++
    vsFMatMulFuns (b + 4) ++ vsLinFuns (b + 20) ++ [vsQAppE (b + 29) phi (b + 7)] ++
    invFuns (b + 29) ++ vsWCoFuns (b + 41) ++ appendFuns (b + 54)

theorem vsBActFuns_length (b phi : ℕ) : (vsBActFuns b phi).length = 57 := rfl

theorem vsFRowMul_fit {p d : ℕ} (hp : 0 < p) (c : List ℕ) (cs : List (List ℕ)) :
    VsWFit p d [vsFRowMul p c cs (vsWZ d)] := by
  intro u hu
  rw [List.mem_singleton] at hu
  subst hu
  refine ⟨vsFMulAcc_foldl_lt hp c cs (acc := (0, vsWZ d)) (fun z hz => ?_), ?_⟩
  · simp only [vsWZ] at hz
    rw [List.eq_of_mem_replicate hz]; exact hp
  · rw [vsFRowMul, vsFMulAcc_foldl_length]; simp [vsWZ]

theorem vsLin_fit {p d a b' : ℕ} (hp : 0 < p) {v u : List ℕ} (hv : VsWFit p d [v]) :
    VsWFit p d [vsLin p a b' v u] := by
  intro w hw
  rw [List.mem_singleton] at hw
  subst hw
  exact ⟨vsLin_lt hp _ _, by rw [vsLin_length]; exact (hv v (by simp)).2⟩

theorem vsBPt_fit {p d : ℕ} (hp : 0 < p) (cs : List (List ℕ)) {x : List ℕ} (hx : VsWFit p d [x])
    (c : List ℕ) : VsWFit p d [vsBPt p d cs x c] := vsLin_fit hp hx

theorem vsBAct_fit (ws' cs : List (List ℕ)) (x : List ℕ) (g : Perm (Fin I.n)) (c : List ℕ) :
    (∀ y ∈ vsBAct I ws' cs x g c, y < I.p) ∧ (vsBAct I ws' cs x g c).length = cs.length := by
  have := vsWCo_fit I.prime.pos ws' cs
    (vsLin I.p 1 (I.p - 1) (vsQApp I g⁻¹ (vsBPt I.p I.d cs x c)) x) _ (List.mem_singleton_self _)
  exact ⟨this.1, this.2⟩

end GI.Impl

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

theorem vsB_tail_cost {N W : ℕ} (hW : W ≤ 20 * (N + 1) ^ 2) : linTailCost W ≤ 10 ^ 8 * (N + 1) ^ 6 := by
  unfold linTailCost
  have h1 : W + 1 ≤ 21 * (N + 1) ^ 2 := by have : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega); omega
  have h2 := Nat.pow_le_pow_left h1 3
  have e : (21 * (N + 1) ^ 2) ^ 3 = 9261 * (N + 1) ^ 6 := by ring
  omega

set_option maxHeartbeats 4000000 in
/-- **The action program.** -/
theorem vsBAct_spec {P : Program} {b phi Cφ N : ℕ} (h : P.HasAt b (vsBActFuns b phi))
    (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
      (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
    (hsz : VsQSz I.p I.d (vsQExp I) N) (hn : I.n ≤ N) (hΓ : (vsQGam I).wt ≤ N)
    {ws' cs : List (List ℕ)} (H : VsWFrOK I.p N I.d ws' cs) {x : List ℕ}
    (hx : VsWFit I.p I.d [x]) {g : Perm (Fin I.n)} (hg : g ∈ gens I.gs) {c : List ℕ}
    (hc : ∀ y ∈ c, y < I.p) (hcl : c.length = cs.length) :
    FunDet P b (.list [.list [vsQGam I, vsWFrVal I.p I.d ws' cs, natList x], encPerm g,
      natList (0 :: c)]) (natList (0 :: vsBAct I ws' cs x g c)) (Cφ + 10 ^ 9 * (N + 1) ^ 6) := by
  have hp := I.prime.pos
  obtain ⟨hp1, hpN, hdN, h', hcs, hl⟩ := H
  have h0 : P.funs[b]? = some (vsBActF (b + 1) (b + 7) (b + 20) (b + 28) (b + 29) (b + 41) (b + 54)) :=
    h.get (j := 0) (by simp [vsBActFuns])
  have htl : P.HasAt (b + 1) (linTailFuns (b + 1)) := h.block 1 rfl
  have hmm : P.HasAt (b + 4) (vsFMatMulFuns (b + 4)) := h.block 4 rfl
  have hrow : P.funs[b + 7]? = some (vsFRowF (b + 8)) :=
    hmm.get (j := 3) (by rw [vsFMatMulFuns_length]; omega)
  have hfo : P.HasAt (b + 8) (foldlFuns (b + 8) (b + 11)) := hmm.block 4 rfl
  have hst : P.funs[b + 11]? = some (vsFMulStepF (b + 12)) :=
    hmm.get (j := 7) (by rw [vsFMatMulFuns_length]; omega)
  have hl12 : P.HasAt (b + 12) (vsLinFuns (b + 12)) := hmm.block 8 rfl
  have hlin : P.HasAt (b + 20) (vsLinFuns (b + 20)) := h.block 20 rfl
  have happ : P.funs[b + 28]? = some (vsQAppE (b + 29) phi (b + 4 + 3)) :=
    h.get (j := 28) (by rw [vsBActFuns_length]; omega)
  have hinv : P.HasAt (b + 29) (invFuns (b + 29)) := h.block 29 rfl
  have hco : P.HasAt (b + 41) (vsWCoFuns (b + 41)) := h.block 41 rfl
  have hapd : P.HasAt (b + 54) (appendFuns (b + 54)) := h.block 54 rfl
  set Γ := vsQGam I
  set fr := vsWFrVal I.p I.d ws' cs
  set ac := Val.list [Γ, fr, natList x]
  have hxf := hx x (List.mem_singleton_self _)
  have a0 := Det.arg' (P := P) (rest := []) (vs := [ac, encPerm g, natList (0 :: c)]) (j := 0) rfl
  have a1 := Det.arg' (P := P) (rest := []) (vs := [ac, encPerm g, natList (0 :: c)]) (j := 1) rfl
  have a2 := Det.arg' (P := P) (rest := []) (vs := [ac, encPerm g, natList (0 :: c)]) (j := 2) rfl
  have dΓ := Det.get' a0 (Det.nat 0) (show [Γ, fr, natList x][0]? = some Γ from rfl)
  have dfr := Det.get' a0 (Det.nat 1) (show [Γ, fr, natList x][1]? = some fr from rfl)
  have dx := Det.get' a0 (Det.nat 2) (show [Γ, fr, natList x][2]? = some (natList x) from rfl)
  set F0 := Val.list [.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ cs.length)]
  have dF0 := Det.get' dfr (Det.nat 0)
    (show [F0, vsWVs ws', vsWVs cs, .list ((vsWFrRows I.p ws' cs).map VsRow.val)][0]? = some F0 from rfl)
  have dcs := Det.get' dfr (Det.nat 2)
    (show [F0, vsWVs ws', vsWVs cs, .list ((vsWFrRows I.p ws' cs).map VsRow.val)][2]? =
      some (.list (cs.map natList)) from rfl)
  have dp := Det.get' dF0 (Det.nat 0)
    (show [Val.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ cs.length)][0]? = some (.nat I.p)
      from rfl)
  have dzd := Det.get' dF0 (Det.nat 2)
    (show [Val.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ cs.length)][2]? =
      some (natList (vsWZ I.d)) from rfl)
  have dtl : Det P _ (.call (b + 1) (arg 2)) (natList c) _ :=
    Det.call a2 (linTail_spec htl (.nat 0 :: c.map .nat))
  have hz : ∀ y ∈ vsWZ I.d, y < I.p := fun y hy => by simp [vsWZ] at hy; omega
  have hzl : (vsWZ I.d).length = I.d := by simp [vsWZ]
  have hRF : VsFRowFits I.p N c cs (vsWZ I.d) :=
    ⟨hc, by omega, hz, by omega, fun r hr y hy => ((hcs r hr).1 y hy).le.trans hpN,
      fun r hr => by rw [(hcs r hr).2]; exact hdN, fun r hr => by rw [(hcs r hr).2, hzl],
      by omega⟩
  have drow := Det.call (Det.mk2 (Det.mk3 dp dcs dzd) dtl) (vsFRow_spec hrow hfo hst hl12 hp hpN hRF)
  have hrf := vsFRowMul_fit (d := I.d) hp c cs _ (List.mem_singleton_self _)
  have dpt := Det.call (Det.snoc (Det.mk4 dp (Det.nat 1) (Det.nat 1) dx) drow)
    (vsLin_spec hlin (v := x) (u := vsFRowMul I.p c cs (vsWZ I.d)) (a := 1) (b := 1) hp
      (fun y hy => (hxf.1 y hy).le.trans hpN) (fun y hy => (hrf.1 y hy).le.trans hpN)
      (by omega) (by omega) (by omega) hpN (by omega) (by omega))
  have hpt := vsBPt_fit (d := I.d) hp cs hx c
  have dinv := Det.call a1 (inv_spec hinv g)
  have dapp := Det.call (Det.mk3 dΓ dinv dpt)
    (vsQApp_spec happ hinv hmm hphi hsz hn hΓ (inv_mem hg) (y := vsBPt I.p I.d cs x c) hpt)
  have hu := vsQApp_fit (t := g⁻¹) hpt _ (List.mem_singleton_self _)
  have dsub := Det.arith' (op := .sub) dp (Det.nat 1) (z := I.p - 1) rfl
  have dL := Det.call (Det.snoc (Det.mk4 dp (Det.nat 1) dsub dapp) dx)
    (vsLin_spec hlin (v := vsQApp I g⁻¹ (vsBPt I.p I.d cs x c)) (u := x) (a := 1) (b := I.p - 1) hp
      (fun y hy => (hu.1 y hy).le.trans hpN) (fun y hy => (hxf.1 y hy).le.trans hpN)
      (by omega) (by omega) (by omega) hpN (by omega) (by omega))
  have hLf := vsLin_fit (a := 1) (b' := I.p - 1) (u := x) hp
    (vsQApp_fit (t := g⁻¹) hpt)
  have dco := Det.call (Det.mk2 dfr dL) (vsWCo_spec hco ⟨hp1, hpN, hdN, h', hcs, hl⟩ hLf)
  have hcf := (vsBAct_fit (I := I) ws' cs x g c)
  have wco := wt_natList_le_sq (B := N) (xs := (vsBAct I ws' cs x g c)) (fun y hy => (hcf.1 y hy).le.trans hpN)
    (by rw [hcf.2]; omega)
  have hK : loopModK = 1000 := rfl
  have kap : loopModK * (((vsBAct I ws' cs x g c).map Val.nat).length + 1) *
      ((Val.list [.list [.nat 0], .list ((vsBAct I ws' cs x g c).map Val.nat)]).wt + ((vsBAct I ws' cs x g c).map Val.nat).length +
        (Val.list ([Val.nat 0] ++ (vsBAct I ws' cs x g c).map Val.nat)).wt + 1) ≤ 1000 * (N + 1) * (100 * (N + 1) ^ 2) := by
    have w2 := wt_list2_le (.list [.nat 0]) (.list ((vsBAct I ws' cs x g c).map Val.nat))
    have w1 : (Val.list [.nat 0]).wt ≤ 10 := by decide
    have e1 : (Val.list ((vsBAct I ws' cs x g c).map Val.nat)).wt = (natList (vsBAct I ws' cs x g c)).wt := rfl
    have wo := wt_natList_le_sq (B := N + 1) (xs := 0 :: (vsBAct I ws' cs x g c)) (fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact (hcf.1 y hy).le.trans (by omega)) (by simp; rw [hcf.2]; omega)
    have q2 : (N + 1 + 1) ^ 2 ≤ 4 * (N + 1) ^ 2 := by
      have := Nat.pow_le_pow_left (show N + 1 + 1 ≤ 2 * (N + 1) by omega) 2
      have e : (2 * (N + 1)) ^ 2 = 4 * (N + 1) ^ 2 := by ring
      omega
    have e2 : (Val.list ([Val.nat 0] ++ (vsBAct I ws' cs x g c).map Val.nat)).wt = (natList (0 :: (vsBAct I ws' cs x g c))).wt := rfl
    have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    rw [hK, List.length_map]
    have hkN : (vsBAct I ws' cs x g c).length + 1 ≤ N + 1 := by rw [hcf.2]; omega
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 1000 hkN) (by omega)
  have dout := Det.call (Det.mk2 (Det.snoc Det.nil (Det.nat 0)) dco)
    ((append_spec hapd [.nat 0] ((vsBAct I ws' cs x g c).map Val.nat)).mono fun w c hw => ⟨hw.1, hw.2.trans (hw.1 ▸ kap)⟩)
  refine FunDet.intro h0 (dout.mono ?_)
  have wfr := wt_vsWFrVal_le (p := I.p) ⟨hp1, hpN, hdN, h', hcs, hl⟩
  have wx := wt_natList_le_sq (B := N) (xs := x) (fun y hy => (hxf.1 y hy).le.trans hpN)
    (by rw [hxf.2]; exact hdN)
  have wac := wt_list3_le Γ fr (natList x)
  have wg := wt_encPerm_le g
  have wgi := wt_encPerm_le g⁻¹
  have wc := wt_natList_le_sq (B := N + 1) (xs := 0 :: c) (fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact (hc y hy).le.trans (by omega)) (by simp; omega)
  have wc0 := wt_natList_le_sq (B := N) (xs := c) (fun y hy => (hc y hy).le.trans hpN) (by omega)
  have wenv := wt_list3_le ac (encPerm g) (natList (0 :: c))
  have eac : ac.wt = (Val.list [Γ, fr, natList x]).wt := rfl
  have wF0 : F0.wt ≤ 40 * (N + 1) ^ 2 := by
    have := wt_list4_le (.nat I.p) (.nat I.d) (natList (vsWZ I.d)) (natList (vsWZ cs.length))
    have := wt_nat_le I.p
    have := wt_nat_le I.d
    have := wt_natList_le_sq (B := N) (xs := vsWZ I.d) (fun y hy => by simp [vsWZ] at hy; omega)
      (by simp [vsWZ]; omega)
    have := wt_natList_le_sq (B := N) (xs := vsWZ cs.length) (fun y hy => by simp [vsWZ] at hy; omega)
      (by simp [vsWZ]; omega)
    have : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
    show (Val.list [.nat I.p, .nat I.d, natList (vsWZ I.d), natList (vsWZ cs.length)]).wt ≤ _
    omega
  have wfrF : F0.wt < fr.wt := wt_le_wt_list (by simp [fr, vsWFrVal, F0])
  have wcs : (vsWVs cs).wt < fr.wt :=
    wt_le_wt_list (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have ecs : (Val.list (cs.map natList)).wt = (vsWVs cs).wt := rfl
  have wzd := wt_natList_le_sq (B := N) (xs := vsWZ I.d) (fun y hy => by simp [vsWZ] at hy; omega)
    (by simp [vsWZ]; omega)
  have wrow := wt_natList_le_sq (B := N) (xs := vsFRowMul I.p c cs (vsWZ I.d))
    (fun y hy => (hrf.1 y hy).le.trans hpN) (by rw [hrf.2]; omega)
  have wpt := wt_natList_le_sq (B := N) (xs := vsBPt I.p I.d cs x c)
    (fun y hy => ((hpt _ (List.mem_singleton_self _)).1 y hy).le.trans hpN)
    (by rw [(hpt _ (List.mem_singleton_self _)).2]; omega)
  have wu := wt_natList_le_sq (B := N) (xs := vsQApp I g⁻¹ (vsBPt I.p I.d cs x c))
    (fun y hy => (hu.1 y hy).le.trans hpN) (by rw [hu.2]; omega)
  have hLf' := hLf _ (List.mem_singleton_self _)
  have wL := wt_natList_le_sq (B := N) (xs := vsLin I.p 1 (I.p - 1) (vsQApp I g⁻¹ (vsBPt I.p I.d cs x c)) x)
    (fun y hy => (hLf'.1 y hy).le.trans hpN) (by rw [hLf'.2]; omega)
  have wp := wt_nat_le I.p
  have wp1 := wt_nat_le (I.p - 1)
  have w0 := wt_nat_le 0
  have w1 := wt_nat_le 1
  have w2 := wt_nat_le 2
  have wA1 := wt_vsLinArg_le (p := I.p) (a := 1) (b := 1) (v := x) (u := vsFRowMul I.p c cs (vsWZ I.d))
    (fun y hy => (hxf.1 y hy).le.trans hpN) (fun y hy => (hrf.1 y hy).le.trans hpN)
    (by omega) (by omega) hpN (by omega) (by omega)
  have wA2 := wt_vsLinArg_le (p := I.p) (a := 1) (b := I.p - 1)
    (v := vsQApp I g⁻¹ (vsBPt I.p I.d cs x c)) (u := x)
    (fun y hy => (hu.1 y hy).le.trans hpN) (fun y hy => (hxf.1 y hy).le.trans hpN)
    (by omega) (by omega) hpN (by omega) (by omega)
  have wCtx := wt_list3_le (.nat I.p) (.list (cs.map natList)) (natList (vsWZ I.d))
  have wR2 := wt_list2_le (.list [.nat I.p, .list (cs.map natList), natList (vsWZ I.d)]) (natList c)
  have wP3 := wt_list3_le Γ (encPerm g⁻¹) (natList (vsBPt I.p I.d cs x c))
  have wC2 := wt_list2_le fr (natList (vsLin I.p 1 (I.p - 1) (vsQApp I g⁻¹ (vsBPt I.p I.d cs x c)) x))
  have wO := wt_natList_le_sq (B := N + 1) (xs := 0 :: vsBAct I ws' cs x g c) (fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact (hcf.1 y hy).le.trans (by omega)) (by simp; rw [hcf.2]; omega)
  have wco1 := wt_natList_le_sq (B := N) (xs := vsBAct I ws' cs x g c)
    (fun y hy => (hcf.1 y hy).le.trans hpN) (by rw [hcf.2]; omega)
  have wA0 := wt_list2_le (.list [.nat 0]) (natList (vsBAct I ws' cs x g c))
  have w10 : (Val.list [.nat 0]).wt ≤ 10 := by decide
  have q2' : (N + 1 + 1) ^ 2 ≤ 4 * (N + 1) ^ 2 := by
    have := Nat.pow_le_pow_left (show N + 1 + 1 ≤ 2 * (N + 1) by omega) 2
    have e : (2 * (N + 1)) ^ 2 = 4 * (N + 1) ^ 2 := by ring
    omega
  have tcost := vsB_tail_cost (N := N) (W := (Val.list (.nat 0 :: c.map Val.nat)).wt) (by
    show (natList (0 :: c)).wt ≤ _; omega)
  have hinvK : invK * (I.n + 1) ^ 4 ≤ 10 ^ 5 * (N + 1) ^ 4 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
  have hwg : 4 * (I.n + 1) ^ 2 ≤ 4 * (N + 1) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
  have q1 : N + 1 ≤ (N + 1) ^ 2 := Nat.le_self_pow (by omega) _
  have q2 : (N + 1) ^ 2 ≤ (N + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have q3 : (N + 1) ^ 3 ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have q4 : (N + 1) ^ 4 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have q0 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hinvK' : invK = 100000 := rfl
  have eA : vsQAppCost Cφ N = Cφ + 10 ^ 8 * (N + 1) ^ 6 := rfl
  have efr : fr.wt = (vsWFrVal I.p I.d ws' cs).wt := rfl
  have eL1 : (vsLinArg I.p 1 1 x (vsFRowMul I.p c cs (vsWZ I.d))).wt =
    (Val.list ([Val.nat I.p, Val.nat 1, Val.nat 1, natList x] ++
      [natList (vsFRowMul I.p c cs (vsWZ I.d))])).wt := rfl
  have eL2 : (vsLinArg I.p 1 (I.p - 1) (vsQApp I g⁻¹ (vsBPt I.p I.d cs x c)) x).wt =
    (Val.list ([Val.nat I.p, Val.nat 1, Val.nat (I.p - 1),
      natList (vsQApp I g⁻¹ (vsBPt I.p I.d cs x c))] ++ [natList x])).wt := rfl
  have ept : (natList (vsLin I.p 1 1 x (vsFRowMul I.p c cs (vsWZ I.d)))).wt =
    (natList (vsBPt I.p I.d cs x c)).wt := rfl
  have ept2 : (Val.list [Γ, encPerm g⁻¹, natList (vsLin I.p 1 1 x (vsFRowMul I.p c cs (vsWZ I.d)))]).wt =
    (Val.list [Γ, encPerm g⁻¹, natList (vsBPt I.p I.d cs x c)]).wt := rfl
  have eco : (natList (vsWCo I.p ws' cs (vsLin I.p 1 (I.p - 1) (vsQApp I g⁻¹ (vsBPt I.p I.d cs x c)) x))).wt
    = (natList (vsBAct I ws' cs x g c)).wt := rfl
  have eco2 : (Val.list [Val.list ([] ++ [Val.nat 0]),
      natList (vsWCo I.p ws' cs (vsLin I.p 1 (I.p - 1) (vsQApp I g⁻¹ (vsBPt I.p I.d cs x c)) x))]).wt =
    (Val.list [Val.list [Val.nat 0], natList (vsBAct I ws' cs x g c)]).wt := rfl
  have e0 : (Val.list ([] ++ [Val.nat 0])).wt = (Val.list [Val.nat 0]).wt := rfl
  have eout : (Val.list ([Val.nat 0] ++ List.map Val.nat (vsBAct I ws' cs x g c))).wt =
    (natList (0 :: vsBAct I ws' cs x g c)).wt := rfl
  have q5 : (N + 1) ^ 3 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
  have ek : 1000 * (N + 1) * (100 * (N + 1) ^ 2) = 10 ^ 5 * (N + 1) ^ 3 := by ring
  have wb2 := wt_list4_le (.nat I.p) (.nat 1) (.nat 1) (natList x)
  have wc2 := wt_list4_le (.nat I.p) (.nat 1) (.nat (I.p - 1)) (natList (vsQApp I g⁻¹ (vsBPt I.p I.d cs x c)))
  omega

end GI.Impl
