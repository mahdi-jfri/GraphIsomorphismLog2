module

public import Workspace.Impl.TermGlueLabNDis
public import Workspace.Impl.TermGlueLabNDis2

@[expose] public section

/-!
# The label driver: the front module

Proof of Theorem A.23, the first stages of the label driver at a fixed layout.
`tmGLNFrontFuns b jp jm jf sup` holds `mkGroup`, the lift module (lift context at `b + 7`, one
lift at `b + 8`), the labels of `x` and of `y'` with the row transporter, the stabilizer
generators, and step 4 (`tmGLPSupF`, which calls T4 at the outside index `sup`).

`tmGLN_front_ok`: placed at `b`, with PointwiseStab at `jp`, Membership at `jm`,
NormalizedFactor at `jf` and T4 (`TermSupSpec`) at `sup`, the module meets the contracts
`TmGLNMkOK`, `TmGLNLcOK`, `TmGLNL1OK`, `TmGLNXOK`, `TmGLNYOK`, `TmGLNSupOK`, `TmGLNBsOK` of the
driver's first eight stages.

Layout (offsets from `b`): `0` mkGroup (7), `7` lift module (110), `117` labels of `x` (4),
`121` labels of `y'` (3), `124` find (4), `128` relation (22), `150` stabilizer generators (6),
`156` step 4, `157` conjugation, `158` inverse (12), `170` compose (4), `174` map (3).
-/

namespace GI.Impl

set_option maxRecDepth 100000

open GI.Algorithm GI.Lang
open GI.Cited (Val PointwiseStab Membership NormalizedFactor)

/-- The two single functions at offsets `156`, `157`. -/
def tmGLNFrontSup (b sup : ℕ) : List Expr := [tmGLPSupF (b + 158) (b + 174) sup, supConjF (b + 170)]

/-- **The front module** at `b`. -/
def tmGLNFrontFuns (b jp jm jf sup : ℕ) : List Expr :=
  mkGroupFuns b ++ (tmGLPLiftFuns (b + 7) jp jf ++ (tmGLPXLabFuns (b + 117) ++
    (tmGLPYLabFuns (b + 121) (b + 124) ++ (tmGLPFindFuns (b + 124) (b + 128) ++
    (tmGLPRelFuns (b + 128) jm jf ++ (tmGLPBsFuns (b + 150) ++ (tmGLNFrontSup b sup ++
    (invFuns (b + 158) ++ (composeFuns (b + 170) ++ mapFuns (b + 174) (b + 157))))))))))

theorem length_tmGLNFrontFuns (b jp jm jf sup : ℕ) :
    (tmGLNFrontFuns b jp jm jf sup).length = 177 := rfl

private theorem tmGLN_mf_right {P : Program} {b b' : ℕ} {A B : List Expr}
    (h : P.HasAt b (A ++ B)) (hb : b + A.length = b') : P.HasAt b' B := hb ▸ h.right

/-- The blocks of the front module. -/
theorem tmGLN_front_parts {P : Program} {b jp jm jf sup : ℕ}
    (h : P.HasAt b (tmGLNFrontFuns b jp jm jf sup)) :
    P.HasAt b (mkGroupFuns b) ∧ P.HasAt (b + 7) (tmGLPLiftFuns (b + 7) jp jf) ∧
      P.HasAt (b + 117) (tmGLPXLabFuns (b + 117)) ∧
      P.HasAt (b + 121) (tmGLPYLabFuns (b + 121) (b + 124)) ∧
      P.HasAt (b + 124) (tmGLPFindFuns (b + 124) (b + 128)) ∧
      P.HasAt (b + 128) (tmGLPRelFuns (b + 128) jm jf) ∧
      P.HasAt (b + 150) (tmGLPBsFuns (b + 150)) ∧
      P.funs[b + 156]? = some (tmGLPSupF (b + 158) (b + 174) sup) ∧
      P.funs[b + 157]? = some (supConjF (b + 170)) ∧ P.HasAt (b + 158) (invFuns (b + 158)) ∧
      P.HasAt (b + 170) (composeFuns (b + 170)) ∧
      P.HasAt (b + 174) (mapFuns (b + 174) (b + 157)) := by
  have h1 := tmGLN_mf_right h (b' := b + 7) rfl
  have h2 := tmGLN_mf_right h1 (b' := b + 117) rfl
  have h3 := tmGLN_mf_right h2 (b' := b + 121) rfl
  have h4 := tmGLN_mf_right h3 (b' := b + 124) rfl
  have h5 := tmGLN_mf_right h4 (b' := b + 128) rfl
  have h6 := tmGLN_mf_right h5 (b' := b + 150) rfl
  have h7 := tmGLN_mf_right h6 (b' := b + 156) rfl
  have h8 := tmGLN_mf_right h7 (b' := b + 158) rfl
  have h9 := tmGLN_mf_right h8 (b' := b + 170) rfl
  have h10 := tmGLN_mf_right h9 (b' := b + 174) rfl
  have hs := h7.left
  exact ⟨h.left, h1.left, h2.left, h3.left, h4.left, h5.left, h6.left,
    (hs.block (gs := [tmGLPSupF (b + 158) (b + 174) sup]) 0 rfl).single,
    by simpa using (hs.block (gs := [supConjF (b + 170)]) 1 rfl).single,
    h8.left, h9.left, h10⟩

/-- **The front module meets the contracts of the first stages.** -/
theorem tmGLN_front_ok (hst : PointwiseStab) (hm : Membership) (hfac : NormalizedFactor)
    {P : Program} {b jp jm jf sup : ℕ} (Ks Ds : ℕ) (h : P.HasAt b (tmGLNFrontFuns b jp jm jf sup))
    (hjp : P.prims[jp]? = some (pointwiseStabPrim hst))
    (hjm : P.prims[jm]? = some (membershipPrim hm))
    (hjf : P.prims[jf]? = some (normalizedFactorPrim hfac))
    (hsup : P.HasAt sup (tailFuns sup)) :
    Iface.TmGLNMkOK P b (fun B => mkGroupK * ((B + 2) * (B + 1)) ^ 3) ∧
      Iface.TmGLNLcOK P (b + 7) (fun B => tmGLPLcC hst (3 * B + 2)) ∧
      Iface.TmGLNL1OK P (b + 7 + 1) (fun B => tmGLPL1C (normalizedFactorPrim hfac) (4 * B + 2)) ∧
      Iface.TmGLNXOK P (b + 117) tmGLPXLabC ∧
      Iface.TmGLNYOK P (b + 121) (tmGLPYLabC (membershipPrim hm) (normalizedFactorPrim hfac)) ∧
      Iface.TmGLNSupOK P (b + 156) (tmGLPSupC Ks Ds) ∧ Iface.TmGLNBsOK P (b + 150) tmGLPBsC := by
  obtain ⟨hmg, hl, hx, hy, hfd, hr, hbs, hsf, hcj, hinv, hcp, hmc⟩ := tmGLN_front_parts h
  have hL := tmGLPLiftAt_of hl
  exact ⟨tmGLN_mk_ok hmg, tmGLN_lc_ok hst hL hjp, tmGLN_l1_ok hfac hL hjf, tmGLN_x_ok hx,
    tmGLN_y_ok hm hfac hy hfd (tmGLPRelAt_of hr) hjm hjf,
    tmGLN_sup_ok Ks Ds hsf hinv hcp hcj hmc hsup, tmGLN_bs_ok hbs⟩

end GI.Impl
