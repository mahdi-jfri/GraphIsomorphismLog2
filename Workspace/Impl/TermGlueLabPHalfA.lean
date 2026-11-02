import Workspace.Impl.TermGlueLabPXs
import Workspace.Impl.TermGlueLabPOffM
import Workspace.Impl.TermGlueLabPLiftS

/-!
# The callees of the per-generator program (step 5)

Step 5 of the label program (proof of Theorem A.23). The per-generator program
chains five programs built earlier: the row transporters (`tmGLPOff_spec`), one lift
(`tmGLPL1_spec`), the offset list (`tmGLPXs_spec`), the offset vector (`tmGLPOVec_spec`) and
the matrix pair (`tmGLPMPair_spec`). This file bundles where each of them sits in the program
(`TmGLPOffAt`, `TmGLPL1At`, `TmGLPXsAt`, `TmGLPOVecAt`, `TmGLPMPairAt`), with their inner
indices hidden, and proves the monotonicity of their cost bounds and the shape of the
transporter list (`tmGLP_oout_form`).
-/

namespace GI.Impl

open GI.Lang Equiv
open GI.Cited (Val encPerm encGroup gens Membership NormalizedFactor ConstructiveMembership
  PointwiseStab)

/-- The row-transporter program `tmGLPOffFuns` sits at `off`. -/
def TmGLPOffAt (P : Program) (off : ℕ) (hm : Membership) (hfac : NormalizedFactor) : Prop :=
  ∃ find rel jm jf, P.HasAt off (tmGLPOffFuns off find rel) ∧
    P.HasAt find (tmGLPFindFuns find rel) ∧ TmGLPRelAt P rel jm jf ∧
    P.prims[jm]? = some (membershipPrim hm) ∧ P.prims[jf]? = some (normalizedFactorPrim hfac)

/-- The lift module sits at `b` (its one-lift entry is `b + 1`). -/
def TmGLPL1At (P : Program) (b : ℕ) (hst : PointwiseStab) (hfac : NormalizedFactor) : Prop :=
  ∃ jp jf, TmGLPLiftAt P b jp jf ∧ P.prims[jp]? = some (pointwiseStabPrim hst) ∧
    P.prims[jf]? = some (normalizedFactorPrim hfac)

/-- The offset-list program `tmGLPXsF` sits at `xs`. -/
def TmGLPXsAt (P : Program) (xs : ℕ) : Prop :=
  ∃ ap mg g1 mc lc cp, P.funs[xs]? = some (tmGLPXsF ap mg mc) ∧ P.HasAt ap (appendFuns ap) ∧
    P.HasAt mg (mapFuns mg g1) ∧ P.funs[g1]? = some tmGLPGet1F ∧
    P.HasAt mc (mapFuns mc lc) ∧ P.funs[lc]? = some (tmGLPLCmpF cp) ∧
    P.HasAt cp (composeFuns cp)

/-- The offset-vector program `tmGLPOVecF` sits at `ov`. -/
def TmGLPOVecAt (P : Program) (ov : ℕ) (hm : ConstructiveMembership) : Prop :=
  ∃ cs vec ec add ib jm mul tr red, P.funs[ov]? = some (tmGLPOVecF cs vec) ∧
    P.HasAt cs (tmGLPCSumFuns cs ec add) ∧ linElementCoordinatesAt P ec jm hm ∧
    linIntSpec P ib ∧ P.HasAt add (linVectorBinaryFuns add (ib + 11)) ∧
    P.funs[vec]? = some (tmGLPVecF mul tr red) ∧ linDenseMulAt P mul ∧
    P.HasAt tr (tmGLPTrFuns tr) ∧ P.HasAt red (linFiniteMatrixReduceFuns red)

/-- The matrix-pair program `tmGLPMPairF` sits at `mp`. -/
def TmGLPMPairAt (P : Program) (mp : ℕ) (hm : ConstructiveMembership) : Prop :=
  ∃ cm mat mcj cj cp tl mec ec jm mul tr red, P.funs[mp]? = some (tmGLPMPairF cm mat) ∧
    P.funs[cm]? = some (tmGLPCMatF mcj tl mec) ∧ P.HasAt cp (composeFuns cp) ∧
    P.funs[cj]? = some (supConjF cp) ∧ P.HasAt mcj (mapFuns mcj cj) ∧
    P.HasAt tl (linTailFuns tl) ∧ P.HasAt mec (mapFuns mec ec) ∧
    linElementCoordinatesAt P ec jm hm ∧ P.funs[mat]? = some (tmGLPMatF mul tr red) ∧
    linDenseMulAt P mul ∧ P.HasAt tr (tmGLPTrFuns tr) ∧
    P.HasAt red (linFiniteMatrixReduceFuns red)

/-! ### Monotone cost bounds -/

theorem tmGLPORowC_mono (pm pf : Prim) {W V : ℕ} (h : W ≤ V) :
    tmGLPORowC pm pf W ≤ tmGLPORowC pm pf V := by
  unfold tmGLPORowC
  have := tmGLPFindC_mono pm pf (show 100 * (W + 1) ^ 2 ≤ 100 * (V + 1) ^ 2 by gcongr)
  gcongr

theorem tmGLPOffC_mono (pm pf : Prim) {W V : ℕ} (h : W ≤ V) :
    tmGLPOffC pm pf W ≤ tmGLPOffC pm pf V := by
  unfold tmGLPOffC
  have := tmGLPORowC_mono pm pf h
  gcongr

theorem tmGLPXsC_mono {W V : ℕ} (h : W ≤ V) : tmGLPXsC W ≤ tmGLPXsC V := by
  unfold tmGLPXsC; gcongr

theorem tmGLPMPairC_mono (Cc Dc Cm Dm : ℕ) {W V : ℕ} (h : W ≤ V) :
    tmGLPMPairC Cc Dc Cm Dm W ≤ tmGLPMPairC Cc Dc Cm Dm V := by
  unfold tmGLPMPairC tmGLPMPZ tmGLPMPX; gcongr

/-! ### The shape of the transporter list -/

variable {n : ℕ} {Ω : Type} [GI.Multicoset.RAct (Perm (Fin n)) Ω]

/-- **The transporter list of `h ∈ Aut_H(T(x))`** is a list of pairs `[J_i, s_i]` with
`s_i ∈ N`, by `tmGLP_off_item` (applied with the row itself as `j0`). -/
theorem tmGLP_oout_form {H N : Subgroup (Perm (Fin n))} (hn : GI.Multicoset.Normalizes H N)
    {q : ℕ} {X : Fin q → Ω} {h : Perm (Fin n)} (hD : h ∈ GI.Multicoset.Aut H (GI.Multicoset.types N X))
    {u : Val} (hu : TmGLPOOut N X h u) :
    ∃ (J : Fin q → ℕ) (s : Fin q → Perm (Fin n)), (∀ i, s i ∈ N) ∧
      (∀ i, TmGLPOItem N X h i (.list [.nat (J i), encPerm (s i)])) ∧
      u = .list ((List.finRange q).map fun i => .list [.nat (J i), encPerm (s i)]) := by
  obtain ⟨l, rfl, hlen, hl⟩ := hu
  have hpair : ∀ i : Fin q, ∃ j : ℕ, ∃ s : Perm (Fin n), s ∈ N ∧
      l[i.1]? = some (.list [.nat j, encPerm s]) ∧
      TmGLPOItem N X h i (.list [.nat j, encPerm s]) := by
    intro i
    obtain ⟨v, hv, hit⟩ := hl i
    obtain ⟨j, s, hs, rfl, -, -⟩ := tmGLP_off_item hn i hD hit
    exact ⟨j, s, hs, hv, hit⟩
  choose J s hs hv hit using hpair
  refine ⟨J, s, hs, hit, ?_⟩
  congr 1
  refine List.ext_getElem (by simp [hlen]) fun i h1 h2 => ?_
  have := hv ⟨i, hlen ▸ h1⟩
  rw [List.getElem?_eq_getElem h1] at this
  simpa using this

end GI.Impl
