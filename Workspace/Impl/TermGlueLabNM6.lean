import Workspace.Impl.TermGlueLabN6
import Workspace.Impl.LinAffineIface

/-!
# The label driver: the step-6 module

Proof of Theorem A.23, step 6, at a fixed layout. `tmGLNS6Funs b jp jmem jm jv`
holds step 6 (`tmGLS6F`) with all its callees: the trampoline in place of step 5, `mkGroup`, the
output reduction and its library blocks, and the affine transporter
`linAffineTransportAllFuns`, which calls Membership at `jmem`,
ConstructiveMembership at `jm` and VectorStabilizer at `jv`.

`tmGLN_m6_ok`: placed at `b`, with these primitives and PointwiseStab at `jp`, the module meets
the step-6 contract `TmGLNS6OK`. The affine contract `TmGLAffineSpec` is no longer a hypothesis:
it is `linAffineTransportAll_iface_of`, with its constants `tmGLNAffK`, `tmGLNAffD`.

Layout (offsets from `b`): `0` step 6, `1` the trampoline, `2` `mkGroup` (7), `9` the output,
`10` the reduction, `11` the conjugation, `12` append (3), `15` inverse (12), `27` compose (4),
`31` map (3), `34` the affine transporter (1011).
-/

namespace GI.Impl

open GI.Algorithm GI.Lang
open GI.Cited (Val PointwiseStab Membership ConstructiveMembership VectorStabilizer)

/-- The single functions at offsets `9`–`11`. -/
def tmGLNS6Mid (b jp : ℕ) : List Expr :=
  [tmGLSOutF (b + 10) (b + 15) (b + 27) (b + 31), tmGLSRedF (b + 12) (b + 2) jp,
    supConjF (b + 27)]

/-- The first 34 functions of the module. -/
def tmGLNS6Head (b jp : ℕ) : List Expr :=
  [tmGLS6F (b + 2) (b + 1) (b + 34) (b + 9), tmGLNIdF] ++ (mkGroupFuns (b + 2) ++
    (tmGLNS6Mid b jp ++ (appendFuns (b + 12) ++ (invFuns (b + 15) ++ (composeFuns (b + 27) ++
    mapFuns (b + 31) (b + 11))))))

/-- **The step-6 module** at `b`. -/
def tmGLNS6Funs (b jp jmem jm jv : ℕ) : List Expr :=
  tmGLNS6Head b jp ++ linAffineTransportAllFuns (b + 34) jmem jm jv

theorem length_tmGLNS6Head (b jp : ℕ) : (tmGLNS6Head b jp).length = 34 := rfl

theorem length_tmGLNS6Funs (b jp jmem jm jv : ℕ) :
    (tmGLNS6Funs b jp jmem jm jv).length = 1045 := by
  rw [tmGLNS6Funs, List.length_append, length_tmGLNS6Head, linAffineTransportAllFuns_length]

/-- The constant `K` of the affine transporter. -/
noncomputable def tmGLNAffK (hmem : Membership) (hm : ConstructiveMembership)
    (hv : VectorStabilizer) : ℕ :=
  (linAffineTransportAll_iface_of hmem hm hv).choose

/-- The constant `D` of the affine transporter. -/
noncomputable def tmGLNAffD (hmem : Membership) (hm : ConstructiveMembership)
    (hv : VectorStabilizer) : ℕ :=
  (linAffineTransportAll_iface_of hmem hm hv).choose_spec.choose

/-- The cost of the step-6 module, for an input of weight `B`. -/
noncomputable def tmGLNM6C (hps : PointwiseStab) (hmem : Membership)
    (hm : ConstructiveMembership) (hv : VectorStabilizer) (B : ℕ) : ℕ :=
  tmGLS6C (tmGLNAffK hmem hm hv) (tmGLNAffD hmem hm hv) (pointwiseStabPrim hps).c
    (pointwiseStabPrim hps).k (B + 1) B

/-- **The step-6 module meets the step-6 contract.** -/
theorem tmGLN_m6_ok (hps : PointwiseStab) (hmem : Membership) (hm : ConstructiveMembership)
    (hv : VectorStabilizer) {P : Program} {b jp jmem jm jv : ℕ}
    (h : P.HasAt b (tmGLNS6Funs b jp jmem jm jv))
    (hjp : P.prims[jp]? = some (pointwiseStabPrim hps))
    (hjmem : P.prims[jmem]? = some (membershipPrim hmem))
    (hjm : P.prims[jm]? = some (linMembershipPrim hm))
    (hjv : P.prims[jv]? = some (vectorStabilizerPrim hv)) :
    Iface.TmGLNS6OK P b (fun B => tmGLS6C (tmGLNAffK hmem hm hv) (tmGLNAffD hmem hm hv)
      (pointwiseStabPrim hps).c (pointwiseStabPrim hps).k (B + 1) B) := by
  have hH : P.HasAt b (tmGLNS6Head b jp) := h.left
  have hA : P.HasAt (b + 34) (linAffineTransportAllFuns (b + 34) jmem jm jv) := by
    have := h.right; rwa [length_tmGLNS6Head] at this
  have hAff : Iface.TmGLAffineSpec P (tmGLNAffK hmem hm hv) (tmGLNAffD hmem hm hv) (b + 34) :=
    (linAffineTransportAll_iface_of hmem hm hv).choose_spec.choose_spec hA hjmem hjm hjv
  have hf : P.funs[b]? = some (tmGLS6F (b + 2) (b + 1) (b + 34) (b + 9)) := by
    simpa using (hH.block (gs := [tmGLS6F (b + 2) (b + 1) (b + 34) (b + 9)]) 0 rfl).single
  have hid : P.funs[b + 1]? = some tmGLNIdF := (hH.block (gs := [tmGLNIdF]) 1 rfl).single
  have hmg : P.HasAt (b + 2) (mkGroupFuns (b + 2)) := hH.block 2 rfl
  have hout : P.funs[b + 9]? = some (tmGLSOutF (b + 10) (b + 15) (b + 27) (b + 31)) :=
    (hH.block (gs := [tmGLSOutF (b + 10) (b + 15) (b + 27) (b + 31)]) 9 rfl).single
  have hred : P.funs[b + 10]? = some (tmGLSRedF (b + 12) (b + 2) jp) :=
    (hH.block (gs := [tmGLSRedF (b + 12) (b + 2) jp]) 10 rfl).single
  have hcj : P.funs[b + 11]? = some (supConjF (b + 27)) :=
    (hH.block (gs := [supConjF (b + 27)]) 11 rfl).single
  have happ : P.HasAt (b + 12) (appendFuns (b + 12)) := hH.block 12 rfl
  have hinv : P.HasAt (b + 15) (invFuns (b + 15)) := hH.block 15 rfl
  have hcp : P.HasAt (b + 27) (composeFuns (b + 27)) := hH.block 27 rfl
  have hmc : P.HasAt (b + 31) (mapFuns (b + 31) (b + 11)) := hH.block 31 rfl
  exact @tmGLN_s6_ok hps P b (b + 2) (b + 1) (b + 34) (b + 9) (b + 10) (b + 12) jp (b + 15)
    (b + 27) (b + 11) (b + 31) (tmGLNAffK hmem hm hv) (tmGLNAffD hmem hm hv) hf hid hmg hout hred
    happ hjp hinv hcp hcj hmc hAff

theorem tmGLNM6C_mono (hps : PointwiseStab) (hmem : Membership) (hm : ConstructiveMembership)
    (hv : VectorStabilizer) : Monotone (tmGLNM6C hps hmem hm hv) := fun _ _ h =>
  tmGLS6C_mono _ _ _ _ (Nat.add_le_add_right h 1) h

end GI.Impl
