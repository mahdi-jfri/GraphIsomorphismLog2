import Workspace.Impl.TermGlueLabNS5C
import Workspace.Impl.TermGlueLabPSup

/-!
# The label driver: discharges of the group, lift and supplement contracts

Proof of Theorem A.23. The contracts `TmGLNMkOK` (`mkGroup`), `TmGLNLcOK` (the
lift context, `tmGLPLc_spec`), `TmGLNL1OK` (one lift, `tmGLPL1_spec`) and `TmGLNSupOK` (step 4,
`tmGLPSup_spec`) follow from the specs of these programs: the cost of each spec is bounded by
its value at the input bound `B`, since every size in it is at most `B` (for the list
lengths, a list is lighter than its weight).
-/

namespace GI.Impl

open GI.Algorithm GI.Multicoset GI.Lang GI.Paper Equiv
open GI.Cited (Val encPerm encGroup gens GensOf PointwiseStab NormalizedFactor)

/-- **`mkGroup` meets its contract.** -/
theorem tmGLN_mk_ok {P : Program} {mg : ℕ} (h : P.HasAt mg (mkGroupFuns mg)) :
    Iface.TmGLNMkOK P mg (fun B => mkGroupK * ((B + 2) * (B + 1)) ^ 3) := by
  intro n hs B hB hn
  refine FunAll.mono (mkGroup_spec h hs) fun w c hwc => ⟨hwc.1, hwc.2.trans ?_⟩
  have hl := length_lt_wt_list (hs.map encPerm)
  have hl' : (Val.list (hs.map encPerm)).wt < (Val.list [.nat n, .list (hs.map encPerm)]).wt :=
    wt_le_wt_list (by simp)
  simp only [List.length_map] at hl
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (Nat.mul_le_mul (by omega) (by omega)) 3)

theorem tmGLN_LcC_mono (hst : PointwiseStab) {M M' : ℕ} (h : M ≤ M') :
    tmGLPLcC hst M ≤ tmGLPLcC hst M' := by
  unfold tmGLPLcC rowKerCost
  have h4 := Nat.pow_le_pow_left h 4
  have h12 := Nat.pow_le_pow_left h 12
  have h1 : (100 * M ^ 4 + 2) ^ (pointwiseStabPrim hst).k ≤
      (100 * M' ^ 4 + 2) ^ (pointwiseStabPrim hst).k := Nat.pow_le_pow_left (by omega) _
  have := Nat.mul_le_mul_left (pointwiseStabPrim hst).c h1
  have := Nat.mul_le_mul_left rowKerK h12
  have := Nat.mul_le_mul_left (10 ^ 20) h12
  omega

/-- **The lift context meets its contract.** -/
theorem tmGLN_lc_ok (hst : PointwiseStab) {P : Program} {b jp jf : ℕ} (h : TmGLPLiftAt P b jp jf)
    (hj : P.prims[jp]? = some (pointwiseStabPrim hst)) :
    Iface.TmGLNLcOK P b (fun B => tmGLPLcC hst (3 * B + 2)) := by
  intro Ω C n e S L label m E hnat hE i0 ps hps B hB hn hq
  refine (tmGLPLc_spec E hst h hj hnat hE i0 hps).mono fun w c ⟨ps', hw, hcl, hl, hc⟩ =>
    ⟨ps', hw, hcl, hl, hc.trans (tmGLN_LcC_mono hst ?_)⟩
  have h1 := length_lt_wt_list (ps.map pairV)
  have h2 : (Val.list (ps.map pairV)).wt < (Val.list [.list [.nat n, .nat L.q],
      .list (ps.map pairV), natList ((rowList e E i0).map Fin.val)]).wt := wt_le_wt_list (by simp)
  simp only [List.length_map] at h1
  unfold pM
  omega

/-- **One lift meets its contract.** -/
theorem tmGLN_l1_ok (hfac : NormalizedFactor) {P : Program} {b jp jf : ℕ}
    (h : TmGLPLiftAt P b jp jf) (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac)) :
    Iface.TmGLNL1OK P (b + 1) (fun B => tmGLPL1C (normalizedFactorPrim hfac) (4 * B + 2)) := by
  intro Ω C n e S L label m E hnat hE i0 ps' hps' s hs B hB hn hq
  refine (tmGLPL1_spec E hfac h hjf hnat hE i0 hps' hs).mono fun w c ⟨y, hw, hy, hy0, hc⟩ =>
    ⟨y, hw, hy, hy0, hc.trans (tmGLN_L1C_mono _ ?_)⟩
  have h1 := tmGLN_lift_size e S E ps'
  have h2 : (Val.list [liftLabCtx n m ps', coordsVal e S E]).wt <
      (Val.list [.list [liftLabCtx n m ps', coordsVal e S E], encPerm s]).wt :=
    wt_le_wt_list (by simp)
  omega

theorem tmGLN_SupC_mono (K D : ℕ) {W W' : ℕ} (h : W ≤ W') : tmGLPSupC K D W ≤ tmGLPSupC K D W' := by
  have h6 := Nat.pow_le_pow_left (show W + 1 ≤ W' + 1 by omega) 6
  have h8 := Nat.pow_le_pow_left (show W + 1 ≤ W' + 1 by omega) 8
  have h1 : (10 ^ 4 * (W + 1) ^ 6) ^ D ≤ (10 ^ 4 * (W' + 1) ^ 6) ^ D :=
    Nat.pow_le_pow_left (Nat.mul_le_mul_left _ h6) D
  have := Nat.mul_le_mul_left K h1
  have := Nat.mul_le_mul_left (10 ^ 9) h8
  unfold tmGLPSupC
  omega

/-- **Step 4 meets its contract** (T4 at `sup`, cited through `TermSupSpec`). -/
theorem tmGLN_sup_ok {P : Program} {f inv cp cj mc sup Ks Ds : ℕ}
    (hf : P.funs[f]? = some (tmGLPSupF inv mc sup)) (hinv : P.HasAt inv (invFuns inv))
    (hcp : P.HasAt cp (composeFuns cp)) (hcj : P.funs[cj]? = some (supConjF cp))
    (hmc : P.HasAt mc (mapFuns mc cj)) (hsup : Iface.TermSupSpec P Ks Ds sup) :
    Iface.TmGLNSupOK P f (tmGLPSupC Ks Ds) := by
  intro n σN U hU τ hNR _ hsol B hB
  refine (tmGLPSup_spec hf hinv hcp hcj hmc hsup hU τ hNR hsol).mono
    fun u c ⟨S, h1, h2, h3, h4, hc⟩ => ⟨S, h1, h2, h3, h4, hc.trans (tmGLN_SupC_mono Ks Ds hB)⟩

end GI.Impl
