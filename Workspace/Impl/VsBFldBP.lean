module

public import Workspace.Impl.VsBFldAP
public import Workspace.Proved.VsBFldB

@[expose] public section

/-!
# The programs of the translation chain

The translation chain needs three small programs on the context
`vsBCtxB s = [[Γ, frame, x], p, 0 :: 0^D]`:
* the action of stage `j` on `𝔽_p`, `y ↦ y + f(g)_j` (`vsB_actB_spec`);
* the point of a target `u`, `u_j` (`vsB_tkB_spec`);
* the update `u ↦ u - f(t)` (`vsB_upB_spec`).
Here `f(g) = vsBAlpha s g 0` is computed by the affine action program `vsBAct`.
-/

open Matrix

namespace GI.Impl

open GI.Lang GI.Cited GI.Proved Equiv

variable {I : VecStabInst}

/-- The context of the translation chain programs. -/
noncomputable def vsBCtxB (s : VsQSt I) : Val :=
  .list [.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x], .nat I.p,
    natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))]

/-- The key of a point of `𝔽_p`. -/
def vsBKeyB {p : ℕ} (y : ZMod p) : List ℕ := [y.val]

/-- The action, on `[[ctx, j], g, [0, y]]`. -/
def vsBActBE (act : ℕ) : Expr :=
  .letE (.call act (mk3 (.get (.get (arg 0) (.nat 0)) (.nat 0)) (arg 1)
      (.get (.get (arg 0) (.nat 0)) (.nat 2))))
    (mk2 (.nat 0) (.arith .mod (.arith .add (.get (arg 2) (.nat 1))
      (.get (.var 1) (.arith .add (.get (arg 0) (.nat 1)) (.nat 1))))
      (.get (.get (arg 0) (.nat 0)) (.nat 1))))

/-- The point of a target, on `[ctx, j, u]`. -/
def vsBTkBE : Expr := mk2 (.nat 0) (.get (arg 2) (arg 1))

/-- The update, on `[ctx, u, t]`. -/
def vsBUpBE (act tail lin : ℕ) : Expr :=
  .call lin (.snoc (mk4 (.get (arg 0) (.nat 1)) (.nat 1) (.arith .sub (.get (arg 0) (.nat 1)) (.nat 1))
    (arg 1)) (.call tail (.call act (mk3 (.get (arg 0) (.nat 0)) (arg 2) (.get (arg 0) (.nat 2))))))

/-- The translation chain programs at base `b` (60 functions). -/
def vsBBFuns (b phi : ℕ) : List Expr :=
  [vsBActBE (b + 3), vsBTkBE, vsBUpBE (b + 3) (b + 4) (b + 23)] ++ vsBActFuns (b + 3) phi

theorem vsBBFuns_length (b phi : ℕ) : (vsBBFuns b phi).length = 60 := by
  simp [vsBBFuns, vsBActFuns_length]

theorem vsBKeyB_injective {p : ℕ} [NeZero p] : Function.Injective (vsBKeyB : ZMod p → List ℕ) :=
  fun a b h => ZMod.val_injective p (List.cons.inj h).1

theorem vsB_vsQVec_sub [NeZero I.p] {D : ℕ} (u v : Fin D → ZMod I.p) :
    vsLin I.p 1 (I.p - 1) (vsQVec u) (vsQVec v) = vsQVec (u - v) := by
  have hl : (vsQVec v).length ≤ (vsQVec u).length := by simp [vsQVec_length]
  rw [vsQVec_of (d := D) (by rw [vsLin_length, vsQVec_length]) (vsLin_lt I.prime.pos _ _)]
  congr 1
  funext j
  rw [vsF_vsLin _ _ _ hl]
  have e1 := congrFun (vsWV_vsQVec (p := I.p) u) j
  have e2 := congrFun (vsWV_vsQVec (p := I.p) v) j
  simp only [vsWV_apply] at e1 e2
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e1, e2, Pi.sub_apply, Nat.cast_one, one_mul]
  have : ((I.p - 1 : ℕ) : ZMod I.p) = -1 := by
    rw [Nat.cast_sub I.prime.pos, ZMod.natCast_self, zero_sub, Nat.cast_one]
  rw [this, neg_one_mul, ← sub_eq_add_neg]

section Specs

variable {P : Program} {b phi Cφ S Tm : ℕ} (h : P.HasAt b (vsBBFuns b phi))
  (hphi : ∀ g ∈ gens I.gs, FunDet P phi (.list [vsQGam I, encPerm g])
    (vsQE I.p I.d (vsQExp I) (vsQPhi I g)) Cφ)
  (hS : VsQDSz I S Tm) {s : VsQSt I} (hs : VsQStOK s)
include h hS hs

omit h hs in
theorem vsB_szG : VsQSz I.p I.d (vsQExp I) (4 * S) := by
  have hS1 := hS.one_le
  refine ⟨by have := hS.p; omega, by have := hS.d; omega, ?_, I.prime.pos⟩
  have h1 := hS.g
  have h2 : (Val.nat (vsQExp I)).wt < (vsQE I.p I.d (vsQExp I) 1).wt :=
    wt_le_wt_list (show Val.nat (vsQExp I) ∈ [Val.nat I.p, natList (List.replicate I.d 0),
      .nat (vsQExp I), .list ((vsQL (1 : Matrix (Fin I.d) (Fin I.d) (ZMod I.p))ᵀ).map natList)]
      by simp)
  have h3 : (vsQE I.p I.d (vsQExp I) 1).wt < (vsQGam I).wt :=
    wt_le_wt_list (show vsQE I.p I.d (vsQExp I) 1 ∈ [encGroup I.gs, vsQTable I,
      vsQE I.p I.d (vsQExp I) 1] by simp)
  omega

omit h in
theorem vsB_wt_ctxB : (vsBCtxB s).wt ≤ 10 ^ 6 * S ^ 3 := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have wfr := vsQ_wt_fr hS hs
  have wΓ := hS.g
  have hS1 := hS.one_le
  have hxf := hs.fx s.x (List.mem_singleton_self _)
  have wx := wt_natList_le_sq (B := S) (xs := s.x) (fun y hy => (hxf.1 y hy).le.trans hS.p)
    (by rw [hxf.2]; have := hS.d; omega)
  have wz := (vsB_wt_vecA hS hs (0 : Fin (vsQD s) → ZMod I.p)).2
  have w3 := wt_list3_le (vsQGam I) (vsWFrVal I.p I.d s.ws' (vsQCs s)) (natList s.x)
  have w3' := wt_list3_le (.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x]) (.nat I.p)
    (natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p)))
  have := wt_nat_le I.p; have := hS.p
  have q : (S + 1) ^ 2 ≤ 4 * S ^ 3 := by
    have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
    have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
    omega
  have q13 : S ≤ S ^ 3 := Nat.le_self_pow (by norm_num) _
  have q23 : S ^ 2 ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by norm_num)
  show (Val.list _).wt ≤ _
  omega

include hphi in
/-- `f(g)` as the list `0 :: vsQVec (f g)`, from the affine action program. -/
theorem vsB_f_spec {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs) :
    FunDet P (b + 3) (.list [.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x], encPerm g,
      natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))])
      (natList (0 :: vsQVec (vsBAlpha s g 0))) (Cφ + 10 ^ 15 * S ^ 6) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have hact : P.HasAt (b + 3) (vsBActFuns (b + 3) phi) := h.block 3 rfl
  have hS1 := hS.one_le
  have hΓ : (vsQGam I).wt ≤ 4 * S := by have := hS.g; omega
  have := vsBAct_spec hact hphi (vsB_szG hS) (by have := hS.n; omega) hΓ (vsQ_frOK hS hs) hs.fx
    (hs.prob.le hg) (vsQVec_lt (0 : Fin (vsQD s) → ZMod I.p)) (by rw [vsQVec_length])
  rw [vsBAct_vsQVec hs] at this
  refine this.mono ?_
  have p6 := vsQ_four_pow 6 hS1
  norm_num at p6
  omega

include hphi in
set_option maxHeartbeats 2000000 in
/-- **The action of stage `j`.** -/
theorem vsB_actB_spec {j : ℕ} (hj : j < vsQD s) {g : Perm (Fin I.n)} (hg : g ∈ gens s.hs)
    (y : ZMod I.p) :
    FunDet P b (.list [.list [vsBCtxB s, .nat j], encPerm g, natList (0 :: vsBKeyB y)])
      (natList (0 :: vsBKeyB (vsBAj s j g y))) (Cφ + 10 ^ 16 * S ^ 6) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have h0 : P.funs[b]? = some (vsBActBE (b + 3)) := h.get (j := 0) (by rw [vsBBFuns_length]; omega)
  have hS1 := hS.one_le
  set c := vsBCtxB s
  set ac := Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x]
  set z0 := natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))
  set fv := natList (0 :: vsQVec (vsBAlpha s g 0))
  set a := Val.list [.list [c, .nat j], encPerm g, natList (0 :: vsBKeyB y)]
  have g0 := Det.arg' (P := P) (rest := []) (vs := [.list [c, .nat j], encPerm g, natList (0 :: vsBKeyB y)])
    (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [.list [c, .nat j], encPerm g, natList (0 :: vsBKeyB y)])
    (j := 1) rfl
  have dc := Det.get' g0 (Det.nat 0) (show [c, Val.nat j][0]? = some c from rfl)
  have dac := Det.get' dc (Det.nat 0) (show [ac, .nat I.p, z0][0]? = some ac from rfl)
  have dz := Det.get' dc (Det.nat 2) (show [ac, .nat I.p, z0][2]? = some z0 from rfl)
  have df := Det.call (Det.mk3 dac g1 dz) (vsB_f_spec h hphi hS hs hg)
  -- in the environment `[a, fv]`
  have g0' := Det.arg' (P := P) (rest := [fv]) (vs := [.list [c, .nat j], encPerm g, natList (0 :: vsBKeyB y)])
    (j := 0) rfl
  have g2' := Det.arg' (P := P) (rest := [fv]) (vs := [.list [c, .nat j], encPerm g, natList (0 :: vsBKeyB y)])
    (j := 2) rfl
  have dc' := Det.get' g0' (Det.nat 0) (show [c, Val.nat j][0]? = some c from rfl)
  have dj' := Det.get' g0' (Det.nat 1) (show [c, Val.nat j][1]? = some (.nat j) from rfl)
  have dp' := Det.get' dc' (Det.nat 1) (show [ac, .nat I.p, z0][1]? = some (.nat I.p) from rfl)
  have dy := Det.get' g2' (Det.nat 1) (show [Val.nat 0, .nat y.val][1]? = some (.nat y.val) from rfl)
  have dj1 := Det.arith' (op := .add) dj' (Det.nat 1) (z := j + 1) rfl
  have hjl : j < (vsQVec (vsBAlpha s g 0)).length := by rw [vsQVec_length]; exact hj
  have dfj := Det.get' (Det.var' (P := P) (env := [a, fv]) (i := 1) rfl) dj1
    (v := .nat (vsBAlpha s g 0 ⟨j, hj⟩).val) (by
      show ((0 :: vsQVec (vsBAlpha s g 0)).map Val.nat)[j + 1]? = _
      simp [vsQVec, hj])
  have dsum := Det.arith' (op := .add) dy dfj (z := y.val + (vsBAlpha s g 0 ⟨j, hj⟩).val) rfl
  have dmod := Det.arith' (op := .mod) dsum dp' (z := (y + vsBAlpha s g 0 ⟨j, hj⟩).val) (by
    show (y.val + (vsBAlpha s g 0 ⟨j, hj⟩).val) % I.p = _
    rw [ZMod.val_add])
  have dall := Det.letE df (Det.mk2 (Det.nat 0) dmod)
  have ev : Val.list [.nat 0, .nat (y + vsBAlpha s g 0 ⟨j, hj⟩).val] =
      natList (0 :: vsBKeyB (vsBAj s j g y)) := by
    simp [natList, vsBKeyB, vsBAj, hj]
  rw [ev] at dall
  refine FunDet.intro h0 (dall.mono ?_)
  have wc := vsB_wt_ctxB hS hs
  have ec : c.wt = (vsBCtxB s).wt := rfl
  have wac : ac.wt < c.wt := wt_le_wt_list (by simp [c, vsBCtxB, ac])
  have wz0 : z0.wt < c.wt := wt_le_wt_list (by simp [c, vsBCtxB, z0])
  have wpc : (Val.nat I.p).wt < c.wt := wt_le_wt_list (by simp [c, vsBCtxB])
  have wfv := (vsB_wt_vecA hS hs (vsBAlpha s g 0)).2
  have efv : fv.wt = (natList (0 :: vsQVec (vsBAlpha s g 0))).wt := rfl
  have wg := hS.wt_perm g
  have hyp : y.val < I.p := ZMod.val_lt y
  have hfp : (vsBAlpha s g 0 ⟨j, hj⟩).val < I.p := ZMod.val_lt _
  have hzp : (y + vsBAlpha s g 0 ⟨j, hj⟩).val < I.p := ZMod.val_lt _
  have hpS := hS.p
  have hDd := vsQD_le hs
  have hdS := hS.d
  have wky := wt_natList_le_sq (B := S) (xs := 0 :: vsBKeyB y) (fun z hz => by
    simp [vsBKeyB] at hz; rcases hz with rfl | rfl <;> omega) (by simp [vsBKeyB]; omega)
  have wko := wt_natList_le_sq (B := S) (xs := 0 :: vsBKeyB (vsBAj s j g y)) (fun z hz => by
    simp only [vsBKeyB, List.mem_cons, List.mem_nil_iff, or_false] at hz
    rcases hz with rfl | rfl
    · omega
    · exact (ZMod.val_lt _).le.trans hpS) (by simp [vsBKeyB]; omega)
  have w2 := wt_list2_le c (.nat j)
  have wa := wt_list3_le (.list [c, .nat j]) (encPerm g) (natList (0 :: vsBKeyB y))
  have ea : (Val.list [.list [c, .nat j], encPerm g, natList (0 :: vsBKeyB y)]).wt = a.wt := rfl
  have w3 := wt_list3_le ac (encPerm g) z0
  have wenv := wt_list2_le a fv
  have wo2 := wt_list2_le (.nat 0) (.nat (y + vsBAlpha s g 0 ⟨j, hj⟩).val)
  have eo : (natList (0 :: vsBKeyB (vsBAj s j g y))).wt =
    (Val.list [.nat 0, .nat (y + vsBAlpha s g 0 ⟨j, hj⟩).val]).wt := by rw [ev]
  have := wt_nat_le j; have := wt_nat_le (j + 1); have := wt_nat_le y.val
  have := wt_nat_le (vsBAlpha s g 0 ⟨j, hj⟩).val
  have := wt_nat_le (y.val + (vsBAlpha s g 0 ⟨j, hj⟩).val)
  have := wt_nat_le (y + vsBAlpha s g 0 ⟨j, hj⟩).val
  have := wt_nat_le I.p; have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2
  have q : (S + 1) ^ 2 ≤ 4 * S ^ 6 := by
    have h1 : (S + 1) ^ 2 ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
    have e : (2 * S) ^ 2 = 4 * S ^ 2 := by ring
    omega
  have es : (Val.list ((0 :: vsQVec (vsBAlpha s g 0)).map Val.nat)).wt = fv.wt := rfl
  have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q16 : S ≤ S ^ 6 := Nat.le_self_pow (by norm_num) _
  omega

omit hS hs in
/-- **The point of a target.** -/
theorem vsB_tkB_spec {j : ℕ} (hj : j < vsQD s) (u : Multiplicative (Fin (vsQD s) → ZMod I.p)) :
    FunDet P (b + 1) (.list [vsBCtxB s, .nat j, natList (vsQVec (Multiplicative.toAdd u))])
      (natList (0 :: vsBKeyB (vsBTj s j u)))
      (10 * (Val.list [vsBCtxB s, .nat j, natList (vsQVec (Multiplicative.toAdd u))]).wt + 100) := by
  have h1 : P.funs[b + 1]? = some vsBTkBE := h.get (j := 1) (by rw [vsBBFuns_length]; omega)
  set a := Val.list [vsBCtxB s, .nat j, natList (vsQVec (Multiplicative.toAdd u))]
  have g1 := Det.arg' (P := P) (rest := [])
    (vs := [vsBCtxB s, .nat j, natList (vsQVec (Multiplicative.toAdd u))]) (j := 1) rfl
  have g2 := Det.arg' (P := P) (rest := [])
    (vs := [vsBCtxB s, .nat j, natList (vsQVec (Multiplicative.toAdd u))]) (j := 2) rfl
  have dg := Det.get' g2 g1 (v := .nat (Multiplicative.toAdd u ⟨j, hj⟩).val) (by
    show ((vsQVec (Multiplicative.toAdd u)).map Val.nat)[j]? = _
    simp [vsQVec, hj])
  have dall := Det.mk2 (Det.nat (P := P) (env := [a]) 0) dg
  have ev : Val.list [.nat 0, .nat (Multiplicative.toAdd u ⟨j, hj⟩).val] =
      natList (0 :: vsBKeyB (vsBTj s j u)) := by
    simp [natList, vsBKeyB, vsBTj, hj]
  rw [ev] at dall
  refine FunDet.intro h1 (dall.mono ?_)
  have wv : (Val.nat (Multiplicative.toAdd u ⟨j, hj⟩).val).wt < (natList (vsQVec (Multiplicative.toAdd u))).wt :=
    wt_le_wt_list (by simp [natList, vsQVec])
  have wu : (natList (vsQVec (Multiplicative.toAdd u))).wt < a.wt := wt_le_wt_list (by simp [a])
  have wj : (Val.nat j).wt < a.wt := wt_le_wt_list (by simp [a])
  have w2 := wt_list2_le (.nat 0) (.nat (Multiplicative.toAdd u ⟨j, hj⟩).val)
  have eo : (natList (0 :: vsBKeyB (vsBTj s j u))).wt =
    (Val.list [.nat 0, .nat (Multiplicative.toAdd u ⟨j, hj⟩).val]).wt := by rw [ev]
  have := wt_nat_le 0; have := wt_nat_le 1; have := wt_nat_le 2
  have ea : (Val.list [vsBCtxB s, .nat j, natList (vsQVec (Multiplicative.toAdd u))]).wt = a.wt := rfl
  omega

omit h hS hs in
theorem vsBPsiB_inv_mul (t : Perm (Fin I.n)) (u : Multiplicative (Fin (vsQD s) → ZMod I.p)) :
    Multiplicative.toAdd ((vsBPsiB s t)⁻¹ * u) = Multiplicative.toAdd u - vsBAlpha s t 0 := by
  simp [vsBPsiB, sub_eq_add_neg, add_comm]

include hphi in
set_option maxHeartbeats 2000000 in
/-- **The update** `u ↦ u - f(t)`. -/
theorem vsB_upB_spec (u : Multiplicative (Fin (vsQD s) → ZMod I.p)) {t : Perm (Fin I.n)}
    (ht : t ∈ gens s.hs) :
    FunDet P (b + 2) (.list [vsBCtxB s, natList (vsQVec (Multiplicative.toAdd u)), encPerm t])
      (natList (vsQVec (Multiplicative.toAdd ((vsBPsiB s t)⁻¹ * u)))) (Cφ + 10 ^ 16 * S ^ 6) := by
  haveI : NeZero I.p := ⟨I.prime.ne_zero⟩
  have h2 : P.funs[b + 2]? = some (vsBUpBE (b + 3) (b + 4) (b + 23)) :=
    h.get (j := 2) (by rw [vsBBFuns_length]; omega)
  have hact : P.HasAt (b + 3) (vsBActFuns (b + 3) phi) := h.block 3 rfl
  have htl : P.HasAt (b + 4) (linTailFuns (b + 4)) := hact.block 1 rfl
  have hlin : P.HasAt (b + 23) (vsLinFuns (b + 23)) := hact.block 20 rfl
  have hS1 := hS.one_le
  set c := vsBCtxB s
  set ac := Val.list [vsQGam I, vsWFrVal I.p I.d s.ws' (vsQCs s), natList s.x]
  set z0 := natList (0 :: vsQVec (0 : Fin (vsQD s) → ZMod I.p))
  set U := Multiplicative.toAdd u
  set F := vsBAlpha s t 0
  set a := Val.list [c, natList (vsQVec U), encPerm t]
  have g0 := Det.arg' (P := P) (rest := []) (vs := [c, natList (vsQVec U), encPerm t]) (j := 0) rfl
  have g1 := Det.arg' (P := P) (rest := []) (vs := [c, natList (vsQVec U), encPerm t]) (j := 1) rfl
  have g2 := Det.arg' (P := P) (rest := []) (vs := [c, natList (vsQVec U), encPerm t]) (j := 2) rfl
  have dac := Det.get' g0 (Det.nat 0) (show [ac, .nat I.p, z0][0]? = some ac from rfl)
  have dz := Det.get' g0 (Det.nat 2) (show [ac, .nat I.p, z0][2]? = some z0 from rfl)
  have dp := Det.get' g0 (Det.nat 1) (show [ac, .nat I.p, z0][1]? = some (.nat I.p) from rfl)
  have df := Det.call (Det.mk3 dac g2 dz) (vsB_f_spec h hphi hS hs ht)
  have dtl := Det.call df (linTail_spec htl (.nat 0 :: (vsQVec F).map Val.nat))
  have edrop : Val.list (List.drop 1 (Val.nat 0 :: (vsQVec F).map Val.nat)) = natList (vsQVec F) := rfl
  rw [edrop] at dtl
  have dsub := Det.arith' (op := .sub) dp (Det.nat 1) (z := I.p - 1) rfl
  have hpS := hS.p
  have hDd := vsQD_le hs
  have hdS := hS.d
  have dl := Det.call (Det.snoc (Det.mk4 dp (Det.nat 1) dsub g1) dtl)
    (vsLin_spec hlin (N := S) (a := 1) (b := I.p - 1) (v := vsQVec U) (u := vsQVec F) I.prime.pos
      (fun x hx => (vsQVec_lt U x hx).le.trans hpS) (fun x hx => (vsQVec_lt F x hx).le.trans hpS)
      (by rw [vsQVec_length]; omega) (by rw [vsQVec_length]; omega) (by simp [vsQVec_length])
      hpS (by omega) (by omega))
  rw [vsB_vsQVec_sub, ← vsBPsiB_inv_mul] at dl
  refine FunDet.intro h2 (dl.mono ?_)
  have wc := vsB_wt_ctxB hS hs
  have ec : c.wt = (vsBCtxB s).wt := rfl
  have wac : ac.wt < c.wt := wt_le_wt_list (by simp [c, vsBCtxB, ac])
  have wz0 : z0.wt < c.wt := wt_le_wt_list (by simp [c, vsBCtxB, z0])
  have wpc : (Val.nat I.p).wt < c.wt := wt_le_wt_list (by simp [c, vsBCtxB])
  have wF := vsB_wt_vecA hS hs F
  have wU := vsB_wt_vecA hS hs U
  have wO := vsB_wt_vecA hS hs (Multiplicative.toAdd ((vsBPsiB s t)⁻¹ * u))
  have wg := hS.wt_perm t
  have wa := wt_list3_le c (natList (vsQVec U)) (encPerm t)
  have ea : (Val.list [c, natList (vsQVec U), encPerm t]).wt = a.wt := rfl
  have w3 := wt_list3_le ac (encPerm t) z0
  have w4 := wt_list4_le (.nat I.p) (.nat 1) (.nat (I.p - 1)) (natList (vsQVec U))
  have w5 := wt_list_snoc_le [Val.nat I.p, .nat 1, .nat (I.p - 1), natList (vsQVec U)] (natList (vsQVec F))
  have hlt : linTailCost (Val.list (Val.nat 0 :: (vsQVec F).map Val.nat)).wt ≤ 10 ^ 8 * S ^ 6 := by
    unfold linTailCost
    have e : (Val.list (Val.nat 0 :: (vsQVec F).map Val.nat)).wt = (natList (0 :: vsQVec F)).wt := rfl
    rw [e]
    have h1 : (natList (0 :: vsQVec F)).wt + 1 ≤ 21 * S ^ 2 := by
      have := Nat.one_le_pow 2 S hS1; omega
    have := Nat.pow_le_pow_left h1 3
    have e2 : (21 * S ^ 2) ^ 3 = 9261 * S ^ 6 := by ring
    omega
  have hS3 : (S + 1) ^ 3 ≤ 8 * S ^ 3 := by
    have h1 : (S + 1) ^ 3 ≤ (2 * S) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have e : (2 * S) ^ 3 = 8 * S ^ 3 := by ring
    omega
  have q36 : S ^ 3 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q26 : S ^ 2 ≤ S ^ 6 := Nat.pow_le_pow_right hS1 (by norm_num)
  have q16 : S ≤ S ^ 6 := Nat.le_self_pow (by norm_num) _
  have e1 : (natList (vsQVec F)).wt = (Val.list (List.drop 1 (Val.nat 0 :: (vsQVec F).map Val.nat))).wt := rfl
  have := wt_nat_le I.p; have := wt_nat_le (I.p - 1); have := wt_nat_le 0; have := wt_nat_le 1
  have := wt_nat_le 2
  have eF : (natList (0 :: vsQVec (vsBAlpha s t 0))).wt = (natList (0 :: vsQVec F)).wt := rfl
  omega

end Specs

end GI.Impl
