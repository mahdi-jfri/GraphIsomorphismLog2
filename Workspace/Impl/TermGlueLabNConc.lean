import Workspace.Impl.TermGlueLabNCost

/-!
# The label driver: the concrete code of the nonempty part

Proof of Theorem A.23 at a fixed layout. `tmGLNeConc g sup` is the code of the
nonempty part of the label program, placed at `g`: the driver `tmGLNeF` at `g`, then the
modules at fixed offsets. Offsets from `g`:

| offset | module | length |
|---|---|---|
| `0` | the driver `tmGLNeF` | 1 |
| `1` | front `tmGLNFrontFuns` (mkGroup, lifts, labels, `b_j`, step 4) | 177 |
| `178` | linear library `tmGLNLinFuns` | 135 |
| `313` | vectors `tmGLNVecMFuns` | 37 |
| `350` | step 5 `tmGLNS5Funs` | 84 |
| `434` | step 6 `tmGLNS6Funs` (with the affine transporter) | 1045 |
| `1479` | setup `tmGLNSetFuns` (abelian coordinates, quotient, inverse) | 107 |

The total is `1586`. Step 4 calls T4 at the outside index `sup`. The primitives are read at
fixed indices of the final table: PointwiseStab `0`, Membership `1`, NormalizedFactor `3`,
GroupOrder `5`, HermiteFullRank `15`, SmithNonsingular `16`, ConstructiveMembership `17`,
VectorStabilizer `18`.

`tmGLN_conc_spec`: if the code sits at `g`, the primitives are at these indices and T4 meets
`TermSupSpec P Ks Ds sup`, then `TmGLPNeSpec P (tmGLNeK … Ks Ds) (tmGLNeD … Ks Ds) g`. The
constants come from a polynomial bound `tmGLNF` of the ten callee costs (`TermGlueLabNCost`).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (PointwiseStab Membership NormalizedFactor ConstructiveMembership GroupOrder
  HermiteFullRank SmithNonsingular VectorStabilizer)

set_option maxRecDepth 100000

/-- The driver at `g`, with the modules at the offsets of the table above. -/
def tmGLNeDrv (g : ℕ) : Expr :=
  tmGLNeF (g + 1) (g + 1 + 7) (g + 1 + 117) (g + 1 + 121) (g + 1 + 156) (g + 1 + 150) (g + 350)
    (g + 313) (g + 434)

/-- **The code of the nonempty part** at `g`, calling T4 at `sup`. -/
def tmGLNeConc (g sup : ℕ) : List Expr :=
  [tmGLNeDrv g] ++ (tmGLNFrontFuns (g + 1) 0 1 3 sup ++ (tmGLNLinFuns (g + 178) 17 ++
    (tmGLNVecMFuns (g + 313) (g + 178) ++ (tmGLNS5Funs (g + 350) (g + 1) (g + 178) (g + 1479)
      (g + 1479 + 96) (g + 1479 + 105) ++ (tmGLNS6Funs (g + 434) 0 1 17 18 ++
    tmGLNSetFuns (g + 1479) 5 17 15 16)))))

theorem length_tmGLNeConc (g sup : ℕ) : (tmGLNeConc g sup).length = 1586 := by
  simp only [tmGLNeConc, List.length_append, length_tmGLNFrontFuns, length_tmGLNLinFuns,
    length_tmGLNS5Funs, length_tmGLNS6Funs, length_tmGLNSetFuns, tmGLNVecMFuns,
    List.length_singleton]
  rfl

private theorem tmGLN_cc_right {P : Program} {b b' : ℕ} {A B : List Expr}
    (h : P.HasAt b (A ++ B)) {n : ℕ} (hn : A.length = n) (hb : b + n = b') : P.HasAt b' B := by
  have := h.right; rwa [hn, hb] at this

/-- The modules of `tmGLNeConc g sup`. -/
theorem tmGLN_conc_parts {P : Program} {g sup : ℕ} (h : P.HasAt g (tmGLNeConc g sup)) :
    P.funs[g]? = some (tmGLNeDrv g) ∧ P.HasAt (g + 1) (tmGLNFrontFuns (g + 1) 0 1 3 sup) ∧
      P.HasAt (g + 178) (tmGLNLinFuns (g + 178) 17) ∧
      P.HasAt (g + 313) (tmGLNVecMFuns (g + 313) (g + 178)) ∧
      P.HasAt (g + 350) (tmGLNS5Funs (g + 350) (g + 1) (g + 178) (g + 1479) (g + 1479 + 96)
        (g + 1479 + 105)) ∧
      P.HasAt (g + 434) (tmGLNS6Funs (g + 434) 0 1 17 18) ∧
      P.HasAt (g + 1479) (tmGLNSetFuns (g + 1479) 5 17 15 16) := by
  have h1 := tmGLN_cc_right h (n := 1) rfl rfl
  have h2 := tmGLN_cc_right h1 (length_tmGLNFrontFuns _ _ _ _ _) (b' := g + 178) (by omega)
  have h3 := tmGLN_cc_right h2 (length_tmGLNLinFuns _ _) (b' := g + 313) (by omega)
  have h4 := tmGLN_cc_right h3 (n := 37) rfl (b' := g + 350) (by omega)
  have h5 := tmGLN_cc_right h4 (length_tmGLNS5Funs _ _ _ _ _ _) (b' := g + 434) (by omega)
  have h6 := tmGLN_cc_right h5 (length_tmGLNS6Funs _ _ _ _ _) (b' := g + 1479) (by omega)
  exact ⟨(h.left (B := _)).single, h1.left, h2.left, h3.left, h4.left, h5.left, h6⟩

/-! ### The cost -/

/-- The sum of the ten callee costs. -/
noncomputable def tmGLNSumC (hst : PointwiseStab) (hm : Membership) (hfac : NormalizedFactor)
    (ho : GroupOrder) (hH : HermiteFullRank) (hS : SmithNonsingular)
    (hcm : ConstructiveMembership) (hv : VectorStabilizer) (Ks Ds B : ℕ) : ℕ :=
  mkGroupK * ((B + 2) * (B + 1)) ^ 3 + tmGLPLcC hst (3 * B + 2) +
    tmGLPL1C (normalizedFactorPrim hfac) (4 * B + 2) + tmGLPXLabC B +
    tmGLPYLabC (membershipPrim hm) (normalizedFactorPrim hfac) B + tmGLPSupC Ks Ds B +
    tmGLPBsC B + tmGLNM5C hm hfac hcm (tmGLNFA ho hcm) (tmGLNFQ hH hS) (tmGLNFI hH) B +
    tmGLNVecC (tmGLNCs hcm) (tmGLNDs hcm) tmGLNCv tmGLNDv B +
    tmGLS6C (tmGLNAffK hm hcm hv) (tmGLNAffD hm hcm hv) (pointwiseStabPrim hst).c
      (pointwiseStabPrim hst).k (B + 1) B

theorem tmGLNSumC_poly (hst : PointwiseStab) (hm : Membership) (hfac : NormalizedFactor)
    (ho : GroupOrder) (hH : HermiteFullRank) (hS : SmithNonsingular)
    (hcm : ConstructiveMembership) (hv : VectorStabilizer) (Ks Ds : ℕ) :
    TmGLNPoly (tmGLNSumC hst hm hfac ho hH hS hcm hv Ks Ds) :=
  tmGLN_poly_add (tmGLN_poly_add (tmGLN_poly_add (tmGLN_poly_add (tmGLN_poly_add
    (tmGLN_poly_add (tmGLN_poly_add (tmGLN_poly_add (tmGLN_poly_add tmGLN_mkC_poly
    (tmGLN_lcC_poly hst)) (tmGLN_l1C_poly _)) tmGLN_xC_poly) (tmGLN_yC_poly _ _))
    (tmGLN_supC_poly Ks Ds)) tmGLN_bsC_poly) (tmGLN_m5C_poly hm hfac hcm ho hH hS))
    (tmGLN_vecC_poly _ _ _ _)) (tmGLN_s6C_poly _ _ _ _)

/-- The constants of the bound of the sum. -/
noncomputable def tmGLNSC (hst : PointwiseStab) (hm : Membership) (hfac : NormalizedFactor)
    (ho : GroupOrder) (hH : HermiteFullRank) (hS : SmithNonsingular)
    (hcm : ConstructiveMembership) (hv : VectorStabilizer) (Ks Ds : ℕ) : ℕ :=
  (tmGLNSumC_poly hst hm hfac ho hH hS hcm hv Ks Ds).choose
noncomputable def tmGLNSD (hst : PointwiseStab) (hm : Membership) (hfac : NormalizedFactor)
    (ho : GroupOrder) (hH : HermiteFullRank) (hS : SmithNonsingular)
    (hcm : ConstructiveMembership) (hv : VectorStabilizer) (Ks Ds : ℕ) : ℕ :=
  (tmGLNSumC_poly hst hm hfac ho hH hS hcm hv Ks Ds).choose_spec.choose

/-- **The common cost bound** of the ten callees: a polynomial above their sum. -/
noncomputable def tmGLNF (hst : PointwiseStab) (hm : Membership) (hfac : NormalizedFactor)
    (ho : GroupOrder) (hH : HermiteFullRank) (hS : SmithNonsingular)
    (hcm : ConstructiveMembership) (hv : VectorStabilizer) (Ks Ds W : ℕ) : ℕ :=
  tmGLNSC hst hm hfac ho hH hS hcm hv Ks Ds * (W + 1) ^ tmGLNSD hst hm hfac ho hH hS hcm hv Ks Ds

section Bound

variable (hst : PointwiseStab) (hm : Membership) (hfac : NormalizedFactor) (ho : GroupOrder)
  (hH : HermiteFullRank) (hS : SmithNonsingular) (hcm : ConstructiveMembership)
  (hv : VectorStabilizer) (Ks Ds : ℕ)

theorem tmGLNF_mono : Monotone (tmGLNF hst hm hfac ho hH hS hcm hv Ks Ds) := fun _ _ h =>
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) _)

theorem tmGLNF_poly : TmGLNPoly (tmGLNF hst hm hfac ho hH hS hcm hv Ks Ds) :=
  ⟨_, _, fun _ => le_refl _⟩

theorem tmGLN_sum_le_F (B : ℕ) :
    tmGLNSumC hst hm hfac ho hH hS hcm hv Ks Ds B ≤ tmGLNF hst hm hfac ho hH hS hcm hv Ks Ds B :=
  (tmGLNSumC_poly hst hm hfac ho hH hS hcm hv Ks Ds).choose_spec.choose_spec B

/-- The constant `K` of the driver (before the factor `6 ^ D` of `tmGLN_ne_spec`). -/
noncomputable def tmGLNeK0 : ℕ := (tmGLNTotC_poly (tmGLNF_poly hst hm hfac ho hH hS hcm hv Ks Ds)).choose

/-- **The constant `D` of the nonempty part.** -/
noncomputable def tmGLNeD : ℕ :=
  (tmGLNTotC_poly (tmGLNF_poly hst hm hfac ho hH hS hcm hv Ks Ds)).choose_spec.choose

/-- **The constant `K` of the nonempty part.** -/
noncomputable def tmGLNeK : ℕ :=
  tmGLNeK0 hst hm hfac ho hH hS hcm hv Ks Ds * 6 ^ tmGLNeD hst hm hfac ho hH hS hcm hv Ks Ds

theorem tmGLN_tot_le (W : ℕ) :
    tmGLNTotC (tmGLNF hst hm hfac ho hH hS hcm hv Ks Ds) W ≤
      tmGLNeK0 hst hm hfac ho hH hS hcm hv Ks Ds * (W + 1) ^ tmGLNeD hst hm hfac ho hH hS hcm hv Ks Ds :=
  (tmGLNTotC_poly (tmGLNF_poly hst hm hfac ho hH hS hcm hv Ks Ds)).choose_spec.choose_spec W

end Bound

/-! ### The contract -/

set_option maxHeartbeats 1000000 in
/-- **The nonempty part meets `TmGLPNeSpec`** at its layout. -/
theorem tmGLN_conc_spec (hst : PointwiseStab) (hm : Membership) (hfac : NormalizedFactor)
    (ho : GroupOrder) (hH : HermiteFullRank) (hS : SmithNonsingular)
    (hcm : ConstructiveMembership) (hv : VectorStabilizer) {P : Program} {g sup Ks Ds : ℕ}
    (h : P.HasAt g (tmGLNeConc g sup))
    (h0 : P.prims[0]? = some (pointwiseStabPrim hst))
    (h1 : P.prims[1]? = some (membershipPrim hm))
    (h3 : P.prims[3]? = some (normalizedFactorPrim hfac))
    (h5 : P.prims[5]? = some (groupOrderPrim ho))
    (h15 : P.prims[15]? = some (linHermitePrim hH))
    (h16 : P.prims[16]? = some (linSmithPrim hS))
    (h17 : P.prims[17]? = some (linMembershipPrim hcm))
    (h18 : P.prims[18]? = some (vectorStabilizerPrim hv))
    (hsup : Iface.TermSupSpec P Ks Ds sup) :
    Iface.TmGLPNeSpec P (tmGLNeK hst hm hfac ho hH hS hcm hv Ks Ds)
      (tmGLNeD hst hm hfac ho hH hS hcm hv Ks Ds) g := by
  obtain ⟨hd, hF, hL, hV, h5m, h6m, hU⟩ := tmGLN_conc_parts h
  obtain ⟨hmk, hlc, hl1, hx, hy, hsp, hbs⟩ := tmGLN_front_ok hst hm hfac hF h0 h1 h3 hsup
  have hLin := tmGLNLinAt_of hL h17
  have hvec : Iface.TmGLNVecOK P (g + 313)
      (tmGLNVecC (tmGLNCs hcm) (tmGLNDs hcm) tmGLNCv tmGLNDv) :=
    @tmGLN_vecm_ok hcm P (g + 313) (g + 178) 17 hV hLin
  obtain ⟨hab, hquo, hminv⟩ := tmGLN_set_ok ho hcm hH hS hU h5 h17 h15 h16
  have hs5 : Iface.TmGLNS5OK P (g + 350)
      (tmGLNM5C hm hfac hcm (tmGLNFA ho hcm) (tmGLNFQ hH hS) (tmGLNFI hH)) :=
    @tmGLN_m5_ok hst hm hfac hcm P (g + 350) (g + 1) (g + 178) (g + 1479) (g + 1479 + 96)
      (g + 1479 + 105) 0 1 3 17 sup h5m hF hLin h0 h1 h3 _ _ _ (tmGLNFA_mono ho hcm)
      (tmGLNFQ_mono hH hS) (tmGLNFI_mono hH) hab hquo hminv
  have hs6 : Iface.TmGLNS6OK P (g + 434) (fun B => tmGLS6C (tmGLNAffK hm hcm hv)
      (tmGLNAffD hm hcm hv) (pointwiseStabPrim hst).c (pointwiseStabPrim hst).k (B + 1) B) :=
    @tmGLN_m6_ok hst hm hcm hv P (g + 434) 0 1 17 18 h6m h0 h1 h17 h18
  have hle := tmGLN_sum_le_F hst hm hfac ho hH hS hcm hv Ks Ds
  unfold tmGLNSumC at hle
  exact @tmGLN_ne_spec P g (g + 1) (g + 1 + 7) (g + 1 + 117) (g + 1 + 121) (g + 1 + 156)
    (g + 1 + 150) (g + 350) (g + 313) (g + 434) hd (tmGLNF hst hm hfac ho hH hS hcm hv Ks Ds)
    (fun B => mkGroupK * ((B + 2) * (B + 1)) ^ 3) (fun B => tmGLPLcC hst (3 * B + 2))
    (fun B => tmGLPL1C (normalizedFactorPrim hfac) (4 * B + 2)) tmGLPXLabC
    (tmGLPYLabC (membershipPrim hm) (normalizedFactorPrim hfac)) (tmGLPSupC Ks Ds) tmGLPBsC
    (tmGLNM5C hm hfac hcm (tmGLNFA ho hcm) (tmGLNFQ hH hS) (tmGLNFI hH))
    (tmGLNVecC (tmGLNCs hcm) (tmGLNDs hcm) tmGLNCv tmGLNDv)
    (fun B => tmGLS6C (tmGLNAffK hm hcm hv) (tmGLNAffD hm hcm hv) (pointwiseStabPrim hst).c
      (pointwiseStabPrim hst).k (B + 1) B)
    (tmGLNF_mono hst hm hfac ho hH hS hcm hv Ks Ds)
    (fun B => by have := hle B; beta_reduce; omega) (fun B => by have := hle B; beta_reduce; omega)
    (fun B => by have := hle B; beta_reduce; omega) (fun B => by have := hle B; beta_reduce; omega)
    (fun B => by have := hle B; beta_reduce; omega) (fun B => by have := hle B; beta_reduce; omega)
    (fun B => by have := hle B; beta_reduce; omega) (fun B => by have := hle B; beta_reduce; omega)
    (fun B => by have := hle B; beta_reduce; omega) (fun B => by have := hle B; beta_reduce; omega)
    hmk hlc hl1 hx hy hsp hbs hs5 hvec hs6 _ _ (tmGLN_tot_le hst hm hfac ho hH hS hcm hv Ks Ds)

end GI.Impl
