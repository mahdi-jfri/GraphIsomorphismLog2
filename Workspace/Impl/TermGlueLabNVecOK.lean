import Workspace.Impl.TermGlueLabNVec

/-!
# The vector wrapper of the label driver: the contract

Proof of Theorem A.23, step 6. `tmGLN_vec_ok`: the vector wrapper
`tmGLNVecFuns` meets `Iface.TmGLNVecOK`. In each case of step 5 it returns the vectors of the
label (plain case, `tmGLN_vv_plain`) or of the label point (orientation case, `tmGLN_vv_or`)
of the program-aligned target `y'` and of `x`. Those of `y'` equal those of `tmGLAlign I τ`
by `tmGLN_lab_align` and `tmGLP_align_any`.
-/

namespace GI.Impl

open GI.Algorithm GI.Assembly GI.Multicoset GI.Lang GI.Paper Equiv
open GI.Cited (Val encPerm encGroup encIntMatrix gens encInt)

attribute [local instance] stringRAct

section Math

variable {Ω C : Type} {Pp : Params} {S : State Ω C} {L : GiantLabels S} {label : Ω → Fin L.q}
  (hnat : NaturalRows S L label) (hq : 5 ≤ L.q) {m : ℕ} (h0 : 0 < m)
  (E : Fin m × Fin L.q ≃ S.dom) (hP : PureCoords S L label E)
  (htr : MulAction.IsPretransitive (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).Nl
    (RowForm.ofPure hnat hq E hP ⟨0, h0⟩).B)
  (hcard : Fintype.card (Fin m) * L.q = S.size) (hsN : S.size ≤ S.N) (hN : 0 < S.N)
  (hqα : (S.N : ℝ) ^ Pp.α < L.q)

local notation "𝕀" => tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα
set_option quotPrecheck false in
local notation "𝕩" => @id (Fin L.q → Fin m → C) (rowTuple (𝕀).e S.x)
set_option quotPrecheck false in
local notation "ℕb" => @id (Subgroup (Perm (Fin m))) (𝕀).Nb
set_option quotPrecheck false in
local notation "ℤr" y => @id (Fin L.q → Fin m → C) (rowAct (fun i => (y i)⁻¹) 1 (rowTuple (𝕀).e S.y))

/-- **The label vector of `y'`** (plain case): the program's value is the vector of the label
of `tmGLAlign I τ`. -/
theorem tmGLN_vv_plain {σN : List (Perm (Fin m))} (hσN : gens σN = ℕb) {r τ : Perm (Fin m)}
    (hτ : τ ∈ tmGlRes 𝕀 r) {y : Fin L.q → Perm (Fin m)} (hy : cleanRowPerm E y ∈ S.domGroup)
    (hy0 : y (𝕀).i0 = τ) {V D : Matrix (Fin σN.length) (Fin σN.length) ℤ}
    (hpos : ∀ i, 0 < D i i) {J : Fin L.q → Fin L.q} {a : Fin L.q → Perm (Fin m)}
    (ha : ∀ k, a k ∈ gens σN) (hJ : ∀ k, TmGLPFirst (gens σN) (𝕩) ((ℤr y) k) (J k))
    (haz : ∀ k, (𝕩) (J k) ↼ a k = (ℤr y) k) {zs : List (Fin σN.length → ℤ)}
    (hzs : List.Forall₂ (TmGLPCoordOf σN) (1 :: List.ofFn a) zs)
    (Ev : Additive (tmGLV ℕb (𝕀).φ (𝕩)) ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ z, Ev (tmGLPg ℕb (𝕀).φ (𝕩) (fun i => σN[i.val]'i.isLt) z) = tmGLQMap V D z) :
    linVecVal (fun i => Matrix.vecMul zs.sum V i % D i i) =
      linVecVal (tmGLVecZ (Ev (Additive.ofMul (tmGLLab ℕb (𝕀).φ (𝕩)
        (tmGLPRep ℕb (𝕩) (𝕀).i0) (@id (Fin L.q → Fin m → C) (tmGLAlign 𝕀 τ)))))) := by
  have hz : types ℕb (ℤr y) = types ℕb (𝕩) := tmGLN_align_types hτ hy hy0
  rw [hσN] at ha hJ
  rw [tmGLS_lab_vec (𝕀).i0 hσN hpos Ev hE hz ha hJ haz hzs]
  exact congrArg (fun p => linVecVal (tmGLVecZ (Ev (Additive.ofMul p))))
    (tmGLN_lab_align hτ (tmGLP_rep_ok (Ω := Fin m → C) ℕb (𝕩) (𝕀).i0) hy hy0)

/-- **The label vector of `x`** (plain case). -/
theorem tmGLN_ww_plain {σN : List (Perm (Fin m))} (hσN : gens σN = ℕb)
    {V D : Matrix (Fin σN.length) (Fin σN.length) ℤ}
    (hpos : ∀ i, 0 < D i i) {J : Fin L.q → Fin L.q} {a : Fin L.q → Perm (Fin m)}
    (ha : ∀ k, a k ∈ gens σN) (hJ : ∀ k, TmGLPFirst (gens σN) (𝕩) ((𝕩) k) (J k))
    (haz : ∀ k, (𝕩) (J k) ↼ a k = (𝕩) k) {zs : List (Fin σN.length → ℤ)}
    (hzs : List.Forall₂ (TmGLPCoordOf σN) (1 :: List.ofFn a) zs)
    (Ev : Additive (tmGLV ℕb (𝕀).φ (𝕩)) ≃+ tmGLVec (tmGLQMod D))
    (hE : ∀ z, Ev (tmGLPg ℕb (𝕀).φ (𝕩) (fun i => σN[i.val]'i.isLt) z) = tmGLQMap V D z) :
    linVecVal (fun i => Matrix.vecMul zs.sum V i % D i i) =
      linVecVal (tmGLVecZ (Ev (Additive.ofMul (tmGLLab ℕb (𝕀).φ (𝕩)
        (tmGLPRep ℕb (𝕩) (𝕀).i0) (𝕩))))) := by
  rw [hσN] at ha hJ
  rw [tmGLS_lab_vec (𝕀).i0 hσN hpos Ev hE rfl ha hJ haz hzs]

/-- **The label point vector of `y'`** (orientation case). -/
theorem tmGLN_vv_or {σN : List (Perm (Fin m))} (hσN : gens σN = ℕb) {r τ : Perm (Fin m)}
    (hτ : τ ∈ tmGlRes 𝕀 r) {y : Fin L.q → Perm (Fin m)} (hy : cleanRowPerm E y ∈ S.domGroup)
    (hy0 : y (𝕀).i0 = τ) {V D : Matrix (Fin σN.length) (Fin σN.length) ℤ}
    (hpos : ∀ i, 0 < D i i) (hT : (types ℕb (𝕩)).Nodup) {J : Fin L.q → Fin L.q}
    {a : Fin L.q → Perm (Fin m)}
    (ha : ∀ k, a k ∈ gens σN) (hJ : ∀ k, TmGLPFirst (gens σN) (𝕩) ((ℤr y) k) (J k))
    (haz : ∀ k, (𝕩) (J k) ↼ a k = (ℤr y) k) {zs : List (Fin σN.length → ℤ)}
    (hzs : List.Forall₂ (TmGLPCoordOf σN) (1 :: List.ofFn a) zs)
    {ρ : Perm (Fin L.q)} (hρ : ∀ k, ρ k = J k)
    (E' : Additive (tmGLV ℕb (𝕀).φ (𝕩)) ≃+ tmGLVec (tmGLQMod D))
    (Ev : Additive (tmGLV ℕb (𝕀).φ (𝕩) × ℤˣ) ≃+
      tmGLVec (Fin.cons 2 (tmGLQMod D) : Fin (σN.length + 1) → ℕ))
    (hE : ∀ z, E' (tmGLPg ℕb (𝕀).φ (𝕩) (fun i => σN[i.val]'i.isLt) z) = tmGLQMap V D z)
    (hEv : ∀ p, Ev (Additive.ofMul p) = tmGLPCons 2 (tmGLQMod D)
      (tmGLPUnits (Additive.ofMul p.2), E' (Additive.ofMul p.1))) :
    Val.list (encInt ((itpNInv ρ % 2 : ℕ) : ℤ) ::
        (List.finRange σN.length).map fun i => encInt (Matrix.vecMul zs.sum V i % D i i)) =
      linVecVal (tmGLVecZ (Ev (Additive.ofMul (tmGLPt ℕb (𝕀).φ (𝕩)
        (tmGLPRep ℕb (𝕩) (𝕀).i0) (@id (Fin L.q → Fin m → C) (tmGLAlign 𝕀 τ)))))) := by
  have hz : types ℕb (ℤr y) = types ℕb (𝕩) := tmGLN_align_types hτ hy hy0
  rw [hσN] at ha hJ
  rw [tmGLS_pt_vec (𝕀).i0 hσN hpos E' hE Ev hEv hT hz ha hJ haz hzs hρ]
  exact congrArg (fun p => linVecVal (tmGLVecZ (Ev (Additive.ofMul p))))
    (tmGLP_align_any hτ (tmGLP_rep_ok (Ω := Fin m → C) ℕb (𝕩) (𝕀).i0) hy hy0)

/-- **The label point vector of `x`** (orientation case). -/
theorem tmGLN_ww_or {σN : List (Perm (Fin m))} (hσN : gens σN = ℕb)
    {V D : Matrix (Fin σN.length) (Fin σN.length) ℤ}
    (hpos : ∀ i, 0 < D i i) (hT : (types ℕb (𝕩)).Nodup) {J : Fin L.q → Fin L.q}
    {a : Fin L.q → Perm (Fin m)}
    (ha : ∀ k, a k ∈ gens σN) (hJ : ∀ k, TmGLPFirst (gens σN) (𝕩) ((𝕩) k) (J k))
    (haz : ∀ k, (𝕩) (J k) ↼ a k = (𝕩) k) {zs : List (Fin σN.length → ℤ)}
    (hzs : List.Forall₂ (TmGLPCoordOf σN) (1 :: List.ofFn a) zs)
    {ρ : Perm (Fin L.q)} (hρ : ∀ k, ρ k = J k)
    (E' : Additive (tmGLV ℕb (𝕀).φ (𝕩)) ≃+ tmGLVec (tmGLQMod D))
    (Ev : Additive (tmGLV ℕb (𝕀).φ (𝕩) × ℤˣ) ≃+
      tmGLVec (Fin.cons 2 (tmGLQMod D) : Fin (σN.length + 1) → ℕ))
    (hE : ∀ z, E' (tmGLPg ℕb (𝕀).φ (𝕩) (fun i => σN[i.val]'i.isLt) z) = tmGLQMap V D z)
    (hEv : ∀ p, Ev (Additive.ofMul p) = tmGLPCons 2 (tmGLQMod D)
      (tmGLPUnits (Additive.ofMul p.2), E' (Additive.ofMul p.1))) :
    Val.list (encInt ((itpNInv ρ % 2 : ℕ) : ℤ) ::
        (List.finRange σN.length).map fun i => encInt (Matrix.vecMul zs.sum V i % D i i)) =
      linVecVal (tmGLVecZ (Ev (Additive.ofMul (tmGLPt ℕb (𝕀).φ (𝕩)
        (tmGLPRep ℕb (𝕩) (𝕀).i0) (𝕩))))) := by
  rw [hσN] at ha hJ
  rw [tmGLS_pt_vec (𝕀).i0 hσN hpos E' hE Ev hEv hT rfl ha hJ haz hzs hρ]

end Math

/-! ### The contract -/

private theorem tmGLN_cost_pl {Cs Ds Cv Dv c W B : ℕ}
    (hc : c ≤ 10 * W + 4 * (300 * (5 * W + tmGLSVecC Cs Ds Cv Dv (10 * W + 18) + 10)) + 50)
    (hWB : W ≤ B) : c ≤ tmGLNVecC Cs Ds Cv Dv B := by
  refine le_trans ?_ (tmGLNVecC_mono Cs Ds Cv Dv hWB)
  unfold tmGLNVecC
  exact hc.trans (Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_left 4 (Nat.le_add_right _ _)) _) _)

private theorem tmGLN_cost_or {Cs Ds Cv Dv c W B : ℕ}
    (hc : c ≤ 10 * W + 4 * (10 ^ 4 * (W + linTailCost W +
      tmGLSPtC Cs Ds Cv Dv (30 * W + 8 * linTailCost W + 50) + 2)) + 50)
    (hWB : W ≤ B) : c ≤ tmGLNVecC Cs Ds Cv Dv B := by
  refine le_trans ?_ (tmGLNVecC_mono Cs Ds Cv Dv hWB)
  unfold tmGLNVecC
  exact hc.trans (Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_left 4 (Nat.le_add_left _ _)) _) _)

set_option maxHeartbeats 4000000 in
/-- **The vector wrapper meets its contract.** -/
theorem tmGLN_vec_ok (hm : GI.Cited.ConstructiveMembership) {P : Program}
    {b cs vec ec add ib jm mul tr red : ℕ} (h : P.HasAt b (tmGLNVecFuns b cs vec))
    (hcs : P.HasAt cs (tmGLPCSumFuns cs ec add)) (hec : linElementCoordinatesAt P ec jm hm)
    (hib : linIntSpec P ib) (hadd : P.HasAt add (linVectorBinaryFuns add (ib + 11)))
    (hvec : P.funs[vec]? = some (tmGLPVecF mul tr red))
    (hmul : linDenseMulAt P mul) (htrp : P.HasAt tr (tmGLPTrFuns tr))
    (hred : P.HasAt red (linFiniteMatrixReduceFuns red))
    {Ce De Cs Ds Cv Dv : ℕ} (hEB : ∀ W, linElementBudget hm W ≤ Ce * (W + 2) ^ De)
    (hCS : ∀ W, tmGLPCSumC Ce De W ≤ Cs * (W + 2) ^ Ds)
    (hVC : ∀ W t, tmGLPVecC W t ≤ Cv * (W + 0 + t + 2) ^ Dv) :
    Iface.TmGLNVecOK P b (tmGLNVecC Cs Ds Cv Dv) := by
  intro Ω C Pp S L label hnat hq m h0 E hP htr hcard hsN hN hqα σN gs r τ y U V D o5 xl yl
    hσN hτ hy hy0 h5 hxl hyl B hB
  obtain ⟨hgs, ws, hpos, hc⟩ := h5
  have hf : P.funs[b]? = some (tmGLNVecF (b + 1) (b + 2)) := by
    simpa using (h.block (gs := [tmGLNVecF (b + 1) (b + 2)]) 0 rfl).single
  have hpl : P.funs[b + 1]? = some (tmGLNVPlF (b + 4)) :=
    (h.block (gs := [tmGLNVPlF (b + 4)]) 1 rfl).single
  have hor : P.funs[b + 2]? = some (tmGLNVOrF (b + 3) (b + 34)) :=
    (h.block (gs := [tmGLNVOrF (b + 3) (b + 34)]) 2 rfl).single
  have hpt : P.HasAt (b + 3) (tmGLSPtFuns (b + 3) cs vec) := h.block 3 rfl
  have hvf : P.HasAt (b + 4) (tmGLSVecFuns (b + 4) cs vec) := hpt.block 1 rfl
  have htl : P.HasAt (b + 34) (linTailFuns (b + 34)) := h.block 34 rfl
  -- the rows of `x` and of the program-aligned target
  have hxl' : TmGLPXOut (gens σN)
      (@id (Fin L.q → Fin m → C) (rowTuple (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).e
        S.x)) xl := hxl
  have hyl' : TmGLPYOut (gens σN)
      (@id (Fin L.q → Fin m → C) (rowTuple (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).e
        S.x))
      (@id (Fin L.q → Fin m → C) (rowAct (fun i => (y i)⁻¹) 1
        (rowTuple (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).e S.y))) yl := hyl
  have htyp : types (gens σN)
      (@id (Fin L.q → Fin m → C) (rowAct (fun i => (y i)⁻¹) 1
        (rowTuple (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).e S.y))) =
      types (gens σN) (@id (Fin L.q → Fin m → C)
        (rowTuple (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).e S.x)) := by
    rw [hσN]; exact tmGLN_align_types hτ hy hy0
  set X := @id (Fin L.q → Fin m → C)
    (rowTuple (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).e S.x) with hXd
  set Z := @id (Fin L.q → Fin m → C) (rowAct (fun i => (y i)⁻¹) 1
    (rowTuple (tmGLSI Pp hnat hq h0 E hP htr hcard hsN hN hqα).e S.y)) with hZd
  have henx := hxl'
  obtain ⟨lx, rfl, -⟩ := henx
  have heny := hyl'
  obtain ⟨ly, rfl, -⟩ := heny
  have hex := tmGLS_ent_x hxl'
  have hey := tmGLS_ent_y hyl' htyp
  rcases hc with ⟨hT, rfl, -⟩ | ⟨hT, rfl, -⟩
  · -- some type repeats: the label vectors
    set a : Val := .list [.list [tmGLPMCtx U V (fun i => D i i), .list ws], encGroup σN,
      .list lx, .list ly] with ha
    set W := a.wt with hW
    have wc : (tmGLPMCtx U V (fun i => D i i)).wt < W := by
      have h1 : (tmGLPMCtx U V (fun i => D i i)).wt <
          (Val.list [tmGLPMCtx U V (fun i => D i i), .list ws]).wt := wt_le_wt_list (by simp)
      have h2 : (Val.list [tmGLPMCtx U V (fun i => D i i), .list ws]).wt < W :=
        wt_le_wt_list (by simp)
      omega
    have iy := tmGLN_in_wt (ctx := tmGLPMCtx U V (fun i => D i i))
      (vs := [.list [tmGLPMCtx U V (fun i => D i i), .list ws], encGroup σN, .list lx, .list ly])
      (j := 3) rfl rfl
    have ix := tmGLN_in_wt (ctx := tmGLPMCtx U V (fun i => D i i))
      (vs := [.list [tmGLPMCtx U V (fun i => D i i), .list ws], encGroup σN, .list lx, .list ly])
      (j := 2) rfl rfl
    have hWa : (Val.list [.list [tmGLPMCtx U V (fun i => D i i), .list ws], encGroup σN,
      .list lx, .list ly]).wt = W := rfl
    have sy := tmGLSVec_spec hm hvf hcs hec hib hadd hvec hmul htrp hred hEB hCS hVC σN U V
      (fun i => D i i) hey
    have sx := tmGLSVec_spec hm hvf hcs hec hib hadd hvec hmul htrp hred hEB hCS hVC σN U V
      (fun i => D i i) hex
    have hpl' := tmGLN_vpl_spec hpl (w5 := .list ws) (C := tmGLSVecC Cs Ds Cv Dv (10 * W + 18))
      (Ry := fun w => ∃ J : Fin L.q → Fin L.q, ∃ a : Fin L.q → Perm (Fin m),
        (∀ k, a k ∈ gens σN) ∧ (∀ k, TmGLPFirst (gens σN) X (Z k) (J k)) ∧
        (∀ k, X (J k) ↼ a k = Z k) ∧
        ∃ zs : List (Fin σN.length → ℤ), List.Forall₂ (TmGLPCoordOf σN) (1 :: List.ofFn a) zs ∧
          w = linVecVal (fun i => Matrix.vecMul zs.sum V i % D i i))
      (Rx := fun w => ∃ J : Fin L.q → Fin L.q, ∃ a : Fin L.q → Perm (Fin m),
        (∀ k, a k ∈ gens σN) ∧ (∀ k, TmGLPFirst (gens σN) X (X k) (J k)) ∧
        (∀ k, X (J k) ↼ a k = X k) ∧
        ∃ zs : List (Fin σN.length → ℤ), List.Forall₂ (TmGLPCoordOf σN) (1 :: List.ofFn a) zs ∧
          w = linVecVal (fun i => Matrix.vecMul zs.sum V i % D i i))
      (sy.mono fun w c ⟨J, a, ha, hJ, haz, zs, hzs, hw, hc⟩ =>
        ⟨⟨J, a, ha, hJ, haz, zs, hzs, hw⟩, hc.trans (tmGLN_svecC_mono _ _ _ _ (by omega))⟩)
      (sx.mono fun w c ⟨J, a, ha, hJ, haz, zs, hzs, hw, hc⟩ =>
        ⟨⟨J, a, ha, hJ, haz, zs, hzs, hw⟩, hc.trans (tmGLN_svecC_mono _ _ _ _ (by omega))⟩)
    have hd := tmGLN_vec_disp hf (t := σN.length) (mU := encIntMatrix U) (mV := encIntMatrix V)
      (ds := (List.finRange σN.length).map fun i => encInt (D i i)) (b + 1) (by simp) hpl'
    refine hd.mono fun u c ⟨⟨vv, ww, hu, ⟨J, a, ha, hJ, haz, zs, hzs, hv⟩,
      ⟨J', a', ha', hJ', haz', zs', hzs', hw⟩⟩, hc⟩ => ⟨vv, ww, hu, ⟨fun _ Ev hE => ⟨?_, ?_⟩,
        fun h => absurd h hT⟩, ?_⟩
    · rw [hv]
      exact tmGLN_vv_plain hnat hq h0 E hP htr hcard hsN hN hqα hσN hτ hy hy0 hpos ha hJ haz hzs
        Ev hE
    · rw [hw]
      exact tmGLN_ww_plain hnat hq h0 E hP htr hcard hsN hN hqα hσN hpos ha' hJ' haz' hzs' Ev hE
    · have hWB : W ≤ B := hB
      exact tmGLN_cost_pl hc hWB
  · -- all types distinct: the label point vectors
    set a : Val := .list [.list [tmGLNOCtx U V (fun i => D i i), .list ws], encGroup σN,
      .list lx, .list ly] with ha
    set W := a.wt with hW
    have hWa : (Val.list [.list [tmGLNOCtx U V (fun i => D i i), .list ws], encGroup σN,
      .list lx, .list ly]).wt = W := rfl
    have wc : (tmGLNOCtx U V (fun i => D i i)).wt < W := by
      have h1 : (tmGLNOCtx U V (fun i => D i i)).wt <
          (Val.list [tmGLNOCtx U V (fun i => D i i), .list ws]).wt := wt_le_wt_list (by simp)
      have h2 : (Val.list [tmGLNOCtx U V (fun i => D i i), .list ws]).wt < W :=
        wt_le_wt_list (by simp)
      omega
    have e0 : (Val.nat σN.length).wt < (tmGLNOCtx U V (fun i => D i i)).wt :=
      wt_le_wt_list (by simp)
    have e1 : (encIntMatrix U).wt < (tmGLNOCtx U V (fun i => D i i)).wt :=
      wt_le_wt_list (by simp)
    have e2 : (encIntMatrix V).wt < (tmGLNOCtx U V (fun i => D i i)).wt :=
      wt_le_wt_list (by simp)
    have e3 : (linVecVal (Fin.cons 2 (fun i => D i i) : Fin (σN.length + 1) → ℤ)).wt <
        (tmGLNOCtx U V (fun i => D i i)).wt := wt_le_wt_list (by simp)
    have htw := tmGLP_fundet_wt (linTail_vec_spec htl
      (Fin.cons 2 (fun i => D i i) : Fin (σN.length + 1) → ℤ))
    have e : (fun i : Fin σN.length =>
        (Fin.cons 2 (fun i => D i i) : Fin (σN.length + 1) → ℤ) i.succ) = fun i => D i i :=
      funext fun i => Fin.cons_succ _ _ _
    rw [e] at htw
    have hLT := linTailCost_mono (show
      (linVecVal (Fin.cons 2 (fun i => D i i) : Fin (σN.length + 1) → ℤ)).wt ≤ W by omega)
    have hc4 : (tmGLPMCtx U V (fun i => D i i)).wt ≤ 2 * ((Val.nat σN.length).wt +
        (encIntMatrix U).wt + (encIntMatrix V).wt + (linVecVal (fun i => D i i)).wt) + 8 :=
      wt_list4_le _ _ _ _
    have iy := tmGLN_in_wt (ctx := tmGLPMCtx U V (fun i => D i i))
      (vs := [.list [tmGLNOCtx U V (fun i => D i i), .list ws], encGroup σN, .list lx, .list ly])
      (j := 3) rfl rfl
    have ix := tmGLN_in_wt (ctx := tmGLPMCtx U V (fun i => D i i))
      (vs := [.list [tmGLNOCtx U V (fun i => D i i), .list ws], encGroup σN, .list lx, .list ly])
      (j := 2) rfl rfl
    have hT' : (types (gens σN) X).Nodup := by rw [hσN]; exact hT
    have sy := tmGLSPt_spec hm hpt hcs hec hib hadd hvec hmul htrp hred hEB hCS hVC σN U V
      (fun i => D i i) hT' htyp hey
    have sx := tmGLSPt_spec hm hpt hcs hec hib hadd hvec hmul htrp hred hEB hCS hVC σN U V
      (fun i => D i i) hT' rfl hex
    have hor' := tmGLN_vor_spec hor htl (w5 := .list ws)
      (C := tmGLSPtC Cs Ds Cv Dv (30 * W + 8 * linTailCost W + 50))
      (Ry := fun w => ∃ J : Fin L.q → Fin L.q, ∃ a : Fin L.q → Perm (Fin m),
        (∀ k, a k ∈ gens σN) ∧ (∀ k, TmGLPFirst (gens σN) X (Z k) (J k)) ∧
        (∀ k, X (J k) ↼ a k = Z k) ∧
        ∃ zs : List (Fin σN.length → ℤ), List.Forall₂ (TmGLPCoordOf σN) (1 :: List.ofFn a) zs ∧
        ∃ ρ : Perm (Fin L.q), (∀ k, ρ k = J k) ∧
          w = .list (encInt ((itpNInv ρ % 2 : ℕ) : ℤ) ::
            (List.finRange σN.length).map fun i => encInt (Matrix.vecMul zs.sum V i % D i i)))
      (Rx := fun w => ∃ J : Fin L.q → Fin L.q, ∃ a : Fin L.q → Perm (Fin m),
        (∀ k, a k ∈ gens σN) ∧ (∀ k, TmGLPFirst (gens σN) X (X k) (J k)) ∧
        (∀ k, X (J k) ↼ a k = X k) ∧
        ∃ zs : List (Fin σN.length → ℤ), List.Forall₂ (TmGLPCoordOf σN) (1 :: List.ofFn a) zs ∧
        ∃ ρ : Perm (Fin L.q), (∀ k, ρ k = J k) ∧
          w = .list (encInt ((itpNInv ρ % 2 : ℕ) : ℤ) ::
            (List.finRange σN.length).map fun i => encInt (Matrix.vecMul zs.sum V i % D i i)))
      (sy.mono fun w c ⟨J, a, ha, hJ, haz, zs, hzs, ρ, hρ, hw, hc⟩ =>
        ⟨⟨J, a, ha, hJ, haz, zs, hzs, ρ, hρ, hw⟩, hc.trans (tmGLN_sptC_mono _ _ _ _ (by omega))⟩)
      (sx.mono fun w c ⟨J, a, ha, hJ, haz, zs, hzs, ρ, hρ, hw, hc⟩ =>
        ⟨⟨J, a, ha, hJ, haz, zs, hzs, ρ, hρ, hw⟩, hc.trans (tmGLN_sptC_mono _ _ _ _ (by omega))⟩)
    have hd := tmGLN_vec_disp hf (t := σN.length) (mU := encIntMatrix U) (mV := encIntMatrix V)
      (ds := (List.finRange (σN.length + 1)).map fun i =>
        encInt ((Fin.cons 2 (fun i => D i i) : Fin (σN.length + 1) → ℤ) i)) (b + 2) (by simp)
      hor'
    refine hd.mono fun u c ⟨⟨vv, ww, hu, ⟨J, a, ha, hJ, haz, zs, hzs, ρ, hρ, hv⟩,
      ⟨J', a', ha', hJ', haz', zs', hzs', ρ', hρ', hw⟩⟩, hc⟩ => ⟨vv, ww, hu,
        ⟨fun h => absurd hT h, fun _ E' Ev hE hEv => ⟨?_, ?_⟩⟩, ?_⟩
    · rw [hv]
      exact tmGLN_vv_or hnat hq h0 E hP htr hcard hsN hN hqα hσN hτ hy hy0 hpos hT ha hJ haz hzs
        hρ E' Ev hE hEv
    · rw [hw]
      exact tmGLN_ww_or hnat hq h0 E hP htr hcard hsN hN hqα hσN hpos hT ha' hJ' haz' hzs' hρ'
        E' Ev hE hEv
    · have hWB : W ≤ B := hB
      exact tmGLN_cost_or hc hWB

end GI.Impl
