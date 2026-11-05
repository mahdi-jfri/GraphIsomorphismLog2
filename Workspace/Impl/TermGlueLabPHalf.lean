module

public import Workspace.Impl.TermGlueLabPHalfA

@[expose] public section

/-!
# The offset vector of one element (step 5, program)

Step 5 of the label program (proof of Theorem A.23). For an element `g` of the
supplement, the offset of the affine action is `o(g) = u(g⁻¹)`: the class of
`s_0, …, s_{q-1}, g y_0, …, g y_{q-1}`, where the `s_i ∈ N` are the row transporters for
`h = g⁻¹` and `y` is a blockwise lift of `g⁻¹` (`tmGLP_item_u`). The program
`tmGLPHalfF off l1 xs ov` runs on `[ctx, [g, g⁻¹]]`, with `ctx = [[gens N, [t, U, V, d]],
[gens N, vs, q, xl], [liftLabCtx, rows]]`:

1. the row transporters on `[gens N, vs, q, xl, g]` (`tmGLPOff_spec` with `h = g⁻¹`);
2. one lift of `g⁻¹` (`tmGLPL1_spec`, one **NormalizedFactor** call);
3. the list `s ++ g y` (`tmGLPXs_spec`);
4. its offset vector `(Σ z) V mod d` (`tmGLPOVec_spec`).

The per-generator program calls it at `[g, g⁻¹]` (offset `c g`) and at `[g⁻¹, g]` (offset
`c g⁻¹`). The math link to the contract is `tmGLP_item_off` with `tmGLP_item_u`.
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Algorithm (State)
open GI.Cited (Val encPerm encGroup gens Membership NormalizedFactor ConstructiveMembership)

/-- The context of the per-generator program:
`[[gens N, [t, U, V, d]], [gens N, vs, q, xl], lc]`, with `lc = [liftLabCtx, rows]`. -/
def tmGLPHCtx {m : ℕ} (σN : List (Perm (Fin m))) (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ)
    (d : Fin σN.length → ℤ) (vs : List Val) (q : ℕ) (xl : List Val) (lc : Val) : Val :=
  .list [.list [encGroup σN, tmGLPMCtx U V d], .list [encGroup σN, .list vs, .nat q, .list xl], lc]

/-- **The facts of the offset vector of `g`**: `w = (Σ zs) V mod d`, where `zs` are coordinate
vectors of `1 :: (s ++ g y)`, the pairs `[J_i, s_i]` are the row transporters for `g⁻¹`
(`TmGLPOItem`), and `y` is a blockwise lift of `g⁻¹`. -/
def TmGLPHalfOut {Ω C : Type} {S : State Ω C} {L : GI.Algorithm.GiantLabels S} {m : ℕ}
    (E : Fin m × Fin L.q ≃ S.dom) (i0 : Fin L.q) {Ω' : Type}
    [GI.Multicoset.RAct (Perm (Fin m)) Ω'] (σN : List (Perm (Fin m))) (X : Fin L.q → Ω')
    (V : Matrix (Fin σN.length) (Fin σN.length) ℤ) (d : Fin σN.length → ℤ) (g : Perm (Fin m))
    (w : Val) : Prop :=
  ∃ (J : Fin L.q → ℕ) (s y : Fin L.q → Perm (Fin m)) (zs : List (Fin σN.length → ℤ)),
    (∀ i, TmGLPOItem (gens σN) X g⁻¹ i (.list [.nat (J i), encPerm (s i)])) ∧
    GI.Paper.cleanRowPerm E y ∈ S.domGroup ∧ y i0 = g⁻¹ ∧
    List.Forall₂ (TmGLPCoordOf σN) (1 :: (List.ofFn s ++ List.ofFn fun i => g * y i)) zs ∧
    w = linVecVal (fun i => Matrix.vecMul zs.sum V i % d i)

/-- **The offset vector of one element**, on `[ctx, [g, g⁻¹]]`. -/
def tmGLPHalfF (off l1 xs ov : ℕ) : Expr :=
  .letE (.call off (.snoc (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 0))))
    (.letE (.call l1 (mk2 (.get (arg 0) (.nat 2)) (.get (arg 1) (.nat 1))))
      (.letE (.call xs (mk3 (.get (arg 1) (.nat 0)) (.var 1) (.var 2)))
        (.call ov (mk2 (.get (arg 0) (.nat 0)) (.var 3)))))

/-- The bound of the row-transporter call. -/
def tmGLPHalfO (pm pf : Prim) (W : ℕ) : ℕ := tmGLPOffC pm pf (6 * W + 5)

/-- The bound of the offset-list call; `Y` bounds the lift. -/
def tmGLPHalfX (pm pf : Prim) (Y W : ℕ) : ℕ := tmGLPXsC (2 * (W + tmGLPHalfO pm pf W + Y) + 7)

/-- The bound of the offset-vector call. -/
def tmGLPHalfV (pm pf : Prim) (Y Cs Ds Cv Dv W : ℕ) : ℕ :=
  tmGLPMPairC Cs Ds Cv Dv (2 * (W + tmGLPHalfX pm pf Y W) + 6)

/-- **The cost bound of the offset vector of one element.** -/
def tmGLPHalfC (pm pf : Prim) (Y Cs Ds Cv Dv W : ℕ) : ℕ :=
  1000 * (W + 1) + 10 * (tmGLPHalfO pm pf W + Y + tmGLPHalfX pm pf Y W +
    tmGLPHalfV pm pf Y Cs Ds Cv Dv W)

theorem tmGLPHalfC_mono (pm pf : Prim) (Y Cs Ds Cv Dv : ℕ) {W W' : ℕ} (h : W ≤ W') :
    tmGLPHalfC pm pf Y Cs Ds Cv Dv W ≤ tmGLPHalfC pm pf Y Cs Ds Cv Dv W' := by
  have hO : tmGLPHalfO pm pf W ≤ tmGLPHalfO pm pf W' := tmGLPOffC_mono pm pf (by omega)
  have hX : tmGLPHalfX pm pf Y W ≤ tmGLPHalfX pm pf Y W' := tmGLPXsC_mono (by omega)
  have hV : tmGLPHalfV pm pf Y Cs Ds Cv Dv W ≤ tmGLPHalfV pm pf Y Cs Ds Cv Dv W' :=
    tmGLPMPairC_mono _ _ _ _ (by omega)
  unfold tmGLPHalfC
  omega

private theorem tmGLP_snoc_wt (vs : List Val) (v : Val) :
    (Val.list (vs ++ [v])).wt ≤ 3 * ((Val.list vs).wt + v.wt) + 5 := by
  have h1 := wt_list_le (vs ++ [v])
  have h2 := sum_wt_lt_wt_list vs
  have h3 := length_lt_wt_list vs
  simp only [List.map_append, List.sum_append, List.length_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.length_cons, List.length_nil] at h1
  omega

private theorem tmGLP_h_ar1 {c ca W O : ℕ} (hca : ca ≤ 12 * W + 30) (hc : c ≤ ca + 2 * O + 1) :
    c ≤ 12 * W + 31 + 2 * O := by omega

private theorem tmGLP_h_ar {c1 c2 c3 c4 w1 w2 w3 W O Y X V : ℕ} (h1 : c1 ≤ 12 * W + 31 + 2 * O)
    (h2 : c2 ≤ 3 * W + 10 + (3 * W + 10) + 4 * (W + W) + 19 + 2 * Y + 1)
    (h3 : c3 ≤ 3 * W + 10 + (O + 1) + (Y + 1) + 3 * (2 * (W + O + Y) + 7) + 8 + 2 * X + 1)
    (h4 : c4 ≤ 3 * W + 10 + (X + 1) + 4 * (W + X) + 19 + 2 * V + 1)
    (hw1 : w1 < V) (hw2 : w2 < V) (hw3 : w3 < V) :
    c1 + (c2 + (c3 + c4 + w1 + 1) + w2 + 1) + w3 + 1 ≤ 1000 * (W + 1) + 10 * (O + Y + X + V) := by
  omega

set_option maxHeartbeats 1000000 in
/-- **The offset vector of one element.** On `[ctx, [g, g⁻¹]]` the result is
`(Σ zs) V mod d`, where `zs` are coordinate vectors of `1 :: (s ++ g y)`, the `s_i` are the
row transporters for `g⁻¹` and `y` is a blockwise lift of `g⁻¹`. -/
theorem tmGLPHalf_spec (hm : Membership) (hfac : NormalizedFactor) (hcm : ConstructiveMembership)
    {P : Program} {f off lb xs ov : ℕ} (hf : P.funs[f]? = some (tmGLPHalfF off (lb + 1) xs ov))
    (hoffA : TmGLPOffAt P off hm hfac) {hst : GI.Cited.PointwiseStab}
    (hlA : TmGLPL1At P lb hst hfac) (hxsA : TmGLPXsAt P xs) (hovA : TmGLPOVecAt P ov hcm)
    {Ce De Cs Ds Cv Dv : ℕ} (hEB : ∀ W, linElementBudget hcm W ≤ Ce * (W + 2) ^ De)
    (hCS : ∀ W, tmGLPCSumC Ce De W ≤ Cs * (W + 2) ^ Ds)
    (hVC : ∀ W t, tmGLPVecC W t ≤ Cv * (W + 0 + t + 2) ^ Dv)
    -- the lift
    {Ω C : Type} {k : ℕ} {e : Ω ≃ Fin k} {S : State Ω C} {L : GI.Algorithm.GiantLabels S}
    {label : Ω → Fin L.q} {m : ℕ} (E : Fin m × Fin L.q ≃ S.dom)
    (hnat : GI.Algorithm.NaturalRows S L label) (hE : ∀ b i, label (E (b, i)) = i)
    (i0 : Fin L.q) {ps' : List (Perm (Fin k) × Perm (Fin m))}
    (hps' : Subgroup.closure {p | p ∈ ps'} = (tmGLPχ e E hnat hE i0).range)
    {Y : ℕ} (hY : tmGLPL1C (normalizedFactorPrim hfac) (ps'.length + k + k + L.q + 2) ≤ Y)
    -- the row transporters
    {Ω' : Type} [GI.Multicoset.RAct (Perm (Fin m)) Ω'] {H : Subgroup (Perm (Fin m))}
    {σN : List (Perm (Fin m))} (hNH : gens σN ≤ H) (hn : GI.Multicoset.Normalizes H (gens σN))
    {X Z : Fin L.q → Ω'} {vs : List Val} (hT : TmCsTabOK H X Z vs)
    (hZ : ∀ j : Fin L.q, ∃ l : Fin L.q, (GI.Multicoset.Iso H (X j) (Z l)).Nonempty)
    {xl : List Val} (hxl : TmGLPXOut (gens σN) X (.list xl))
    (U V : Matrix (Fin σN.length) (Fin σN.length) ℤ) (d : Fin σN.length → ℤ)
    -- the element
    (g : Perm (Fin m)) (hD : g⁻¹ ∈ GI.Multicoset.Aut H (GI.Multicoset.types (gens σN) X))
    (hs : ∃ y : Fin L.q → Perm (Fin m), GI.Paper.cleanRowPerm E y ∈ S.domGroup ∧ y i0 = g⁻¹)
    (hyN : ∀ y : Fin L.q → Perm (Fin m), GI.Paper.cleanRowPerm E y ∈ S.domGroup → y i0 = g⁻¹ →
      ∀ i, g * y i ∈ gens σN) :
    FunAll P f (.list [tmGLPHCtx σN U V d vs L.q xl (.list [liftLabCtx k m ps', coordsVal e S E]),
        .list [encPerm g, encPerm g⁻¹]])
      (fun w c => TmGLPHalfOut E i0 σN X V d g w ∧
        c ≤ tmGLPHalfC (membershipPrim hm) (normalizedFactorPrim hfac) Y Cs Ds Cv Dv
          (Val.list [tmGLPHCtx σN U V d vs L.q xl (.list [liftLabCtx k m ps', coordsVal e S E]),
            .list [encPerm g, encPerm g⁻¹]]).wt) := by
  obtain ⟨find, rel, jm, jf, hoff, hfd, hr, hjm, hjf⟩ := hoffA
  obtain ⟨jp, jf', hL, -, hjf'⟩ := hlA
  obtain ⟨ap, mg, g1, mc, lc, cp, hxs, hap, hmg, hg1, hmc, hlc, hcp⟩ := hxsA
  obtain ⟨cs, vec, ec, add, ib, jme, mul, tr, red, hov, hcs, hec, hib, hadd, hvec, hmul, htr,
    hred⟩ := hovA
  set pm := membershipPrim hm
  set pf := normalizedFactorPrim hfac
  set mc0 : Val := .list [encGroup σN, tmGLPMCtx U V d] with hmc0
  set oc : Val := .list [encGroup σN, .list vs, .nat L.q, .list xl] with hoc
  set lc0 : Val := .list [liftLabCtx k m ps', coordsVal e S E] with hlc0
  set a : Val := .list [tmGLPHCtx σN U V d vs L.q xl lc0, .list [encPerm g, encPerm g⁻¹]] with ha
  set W := a.wt with hW
  obtain ⟨O, hO⟩ : ∃ O, tmGLPHalfO pm pf W = O := ⟨_, rfl⟩
  obtain ⟨Xc, hXc⟩ : ∃ Xc, tmGLPHalfX pm pf Y W = Xc := ⟨_, rfl⟩
  obtain ⟨Ov, hOv⟩ : ∃ Ov, tmGLPHalfV pm pf Y Cs Ds Cv Dv W = Ov := ⟨_, rfl⟩
  have hXc' : tmGLPXsC (2 * (W + O + Y) + 7) = Xc := by rw [← hXc, tmGLPHalfX, hO]
  have hOv' : tmGLPMPairC Cs Ds Cv Dv (2 * (W + Xc) + 6) = Ov := by
    rw [← hOv, tmGLPHalfV, hXc]
  unfold tmGLPHalfC
  rw [hO, hXc, hOv]
  -- weights of the parts
  have wc : (Val.list [mc0, oc, lc0]).wt < W := by
    have : (tmGLPHCtx σN U V d vs L.q xl lc0).wt < W := wt_le_wt_list (by simp)
    exact this
  have wp : (Val.list [encPerm g, encPerm g⁻¹]).wt < W := wt_le_wt_list (by simp)
  have wmc : mc0.wt < (Val.list [mc0, oc, lc0]).wt := wt_le_wt_list (by simp)
  have woc : oc.wt < (Val.list [mc0, oc, lc0]).wt := wt_le_wt_list (by simp)
  have wlc : lc0.wt < (Val.list [mc0, oc, lc0]).wt := wt_le_wt_list (by simp)
  have wg : (encPerm g).wt < (Val.list [encPerm g, encPerm g⁻¹]).wt := wt_le_wt_list (by simp)
  have wg' : (encPerm g⁻¹).wt < (Val.list [encPerm g, encPerm g⁻¹]).wt :=
    wt_le_wt_list (by simp)
  have gA : ∀ (rest : List Val) (j : ℕ) (v : Val),
      [tmGLPHCtx σN U V d vs L.q xl lc0, .list [encPerm g, encPerm g⁻¹]][j]? = some v →
      Det P (a :: rest) (arg j) v (2 * W + j + 5) := fun rest j v h => Det.arg' h
  -- the row transporters, for `h = g⁻¹`
  have hoffS := tmGLPOff_spec hm hfac hoff hfd hr hjm hjf hNH hn hT hZ hxl (g := g⁻¹)
    (GI.Multicoset.mem_aut.mp hD).1
  rw [inv_inv] at hoffS
  have wIn : (tmGLPOIn σN vs L.q xl g).wt ≤ 6 * W + 5 := by
    have h5 : (Val.list ([encGroup σN, .list vs, .nat L.q, .list xl] ++ [encPerm g])).wt ≤
        3 * (oc.wt + (encPerm g).wt) + 5 := tmGLP_snoc_wt _ _
    have e1 : tmGLPOIn σN vs L.q xl g =
        Val.list ([encGroup σN, .list vs, .nat L.q, .list xl] ++ [encPerm g]) := rfl
    rw [e1]
    omega
  have hO' : tmGLPOffC pm pf (tmGLPOIn σN vs L.q xl g).wt ≤ O := by
    rw [← hO]; exact tmGLPOffC_mono pm pf wIn
  clear_value a W
  apply FunAll.intro hf
  -- step 1
  have g0 : Det P [a] (arg 0) (.list [mc0, oc, lc0]) (2 * W + 0 + 5) := gA _ _ _ rfl
  have g1 : Det P [a] (arg 1) (.list [encPerm g, encPerm g⁻¹]) (2 * W + 1 + 5) := gA _ _ _ rfl
  have dOc := Det.get' g0 (Det.nat 1) (vs := [mc0, oc, lc0]) (v := oc) rfl
  have dG := Det.get' g1 (Det.nat 0) (vs := [encPerm g, encPerm g⁻¹]) (v := encPerm g) rfl
  have dIn : Det P [a] (.snoc (.get (arg 0) (.nat 1)) (.get (arg 1) (.nat 0)))
      (tmGLPOIn σN vs L.q xl g) (12 * W + 30) :=
    (Det.snoc dOc dG).mono (by
      have e1 : Val.list ([encGroup σN, .list vs, .nat L.q, .list xl] ++ [encPerm g]) =
        tmGLPOIn σN vs L.q xl g := rfl
      rw [e1]; omega)
  have c1 := tmGLP_callAll_le dIn le_rfl
    (R := fun u => TmGLPOOut (gens σN) X g⁻¹ u) (C := O)
    (FunAll.mono hoffS fun u c h => ⟨h.1, h.2.trans hO'⟩)
  refine EvalAll.letE c1 fun v1 c1' h1 => ?_
  obtain ⟨hv1, hc1, hw1⟩ := h1
  obtain ⟨J, s, hsN, hit, rfl⟩ := tmGLP_oout_form hn hD hv1
  -- step 2: the lift of `g⁻¹`
  set l1v : Val := Val.list ((List.finRange L.q).map fun i => .list [.nat (J i), encPerm (s i)])
    with hl1v
  have g0' : Det P [a, l1v] (arg 0) (.list [mc0, oc, lc0]) (2 * W + 0 + 5) := gA _ _ _ rfl
  have g1' : Det P [a, l1v] (arg 1) (.list [encPerm g, encPerm g⁻¹]) (2 * W + 1 + 5) :=
    gA _ _ _ rfl
  have dLc := Det.get' g0' (Det.nat 2) (vs := [mc0, oc, lc0]) (v := lc0) rfl
  have dGi := Det.get' g1' (Det.nat 1) (vs := [encPerm g, encPerm g⁻¹]) (v := encPerm g⁻¹) rfl
  have i2 := tmGLP_mk2_le dLc (A := 3 * W + 10) (by omega) dGi (B := 3 * W + 10) (by omega)
    (X := W) (Y := W) (by omega) (by omega)
  have hlS := tmGLPL1_spec E hfac hL hjf' hnat hE i0 hps' hs
  have c2 := tmGLP_callAll_le i2.1 le_rfl (C := Y)
    (R := fun w => ∃ y : Fin L.q → Perm (Fin m),
      w = .list ((List.finRange L.q).map fun i => encPerm (y i)) ∧
      GI.Paper.cleanRowPerm E y ∈ S.domGroup ∧ y i0 = g⁻¹)
    (FunAll.mono hlS fun w c h => by
      obtain ⟨y, hw, hy, hy0, hc⟩ := h
      exact ⟨⟨y, hw, hy, hy0⟩, hc.trans hY⟩)
  refine EvalAll.letE c2 fun v2 c2' h2 => ?_
  obtain ⟨⟨y, rfl, hy, hy0⟩, hc2, hw2⟩ := h2
  -- step 3: the list `s ++ g y`
  set l2v : Val := Val.list ((List.finRange L.q).map fun i => encPerm (y i)) with hl2v
  have g1'' : Det P [a, l1v, l2v] (arg 1) (.list [encPerm g, encPerm g⁻¹]) (2 * W + 1 + 5) :=
    gA _ _ _ rfl
  have dG'' := Det.get' g1'' (Det.nat 0) (vs := [encPerm g, encPerm g⁻¹]) (v := encPerm g) rfl
  have dv1 := Det.var' (P := P) (env := [a, l1v, l2v]) (i := 1) rfl
  have dv2 := Det.var' (P := P) (env := [a, l1v, l2v]) (i := 2) rfl
  have d3 := Det.mk3 dG'' dv1 dv2
  have w3 := wt_list3_le (encPerm g) l1v l2v
  have hxsS := tmGLPXs_spec hxs hap hmg hg1 hmc hlc hcp g J s y
  have hX3 : tmGLPXsC (Val.list [encPerm g, l1v, l2v]).wt ≤ Xc := by
    rw [← hXc']; exact tmGLPXsC_mono (by omega)
  have c3 := tmGLP_call_le d3 le_rfl hxsS hX3
  refine EvalAll.letE c3.1 fun v3 c3' h3 => ?_
  obtain ⟨rfl, hc3⟩ := h3
  -- step 4: the offset vector
  set xsl := List.ofFn s ++ List.ofFn fun i => g * y i with hxsl
  set l3v : Val := Val.list (xsl.map encPerm) with hl3v
  have g0''' : Det P [a, l1v, l2v, l3v] (arg 0) (.list [mc0, oc, lc0]) (2 * W + 0 + 5) :=
    gA _ _ _ rfl
  have dMc := Det.get' g0''' (Det.nat 0) (vs := [mc0, oc, lc0]) (v := mc0) rfl
  have dv3 := Det.var' (P := P) (env := [a, l1v, l2v, l3v]) (i := 3) rfl
  have i4 := tmGLP_mk2_le dMc (A := 3 * W + 10) (by omega) dv3 (B := Xc + 1) (by omega)
    (X := W) (Y := Xc) (by omega) c3.2.le
  have hx : ∀ z ∈ xsl, z ∈ gens σN := by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact hsN i
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact hyN y hy hy0 i
  have hovS := tmGLPOVec_spec hcm hov hcs hec hib hadd hvec hmul htr hred hEB hCS hVC σN U V d
    xsl hx
  have c4 := tmGLP_callAll_le i4.1 le_rfl (C := Ov)
    (R := fun w => ∃ zs : List (Fin σN.length → ℤ), List.Forall₂ (TmGLPCoordOf σN) (1 :: xsl) zs ∧
      w = linVecVal (fun i => Matrix.vecMul zs.sum V i % d i))
    (FunAll.mono hovS fun w c h => by
      obtain ⟨zs, hz, hw, hc⟩ := h
      refine ⟨⟨zs, hz, hw⟩, hc.trans ?_⟩
      rw [← hOv']
      exact tmGLPMPairC_mono _ _ _ _ i4.2)
  refine c4.mono fun w c4' h4 => ?_
  obtain ⟨⟨zs, hz, rfl⟩, hc4, hw4⟩ := h4
  refine ⟨⟨J, s, y, zs, hit, hy, hy0, hz, rfl⟩, ?_⟩
  exact tmGLP_h_ar (tmGLP_h_ar1 le_rfl hc1) hc2 (by omega) hc4 hw4 hw4 hw4

end GI.Impl
