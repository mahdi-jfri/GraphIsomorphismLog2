import Workspace.Impl.LinObjectDataQuotient
import Workspace.Impl.LinObjectPresentedFrame
import Workspace.Impl.LinObjectReindexPresentation

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset
open scoped IsMulCommutative

variable {n : ℕ} (as ns : List (Equiv.Perm (Fin n)))
variable [((gens ns).subgroupOf (gens as)).Normal]
variable [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))]

noncomputable def linObjectCanonicalProjection : gens as →* ((gens as) ⧸ (gens ns).subgroupOf (gens as)) :=
  QuotientGroup.mk' ((gens ns).subgroupOf (gens as))

/-- The two stored normal forms are frames for the actual product of local
quotients and its common-translation quotient, in the paper's piece index. -/
def linObjectCanonicalFrames (Y : List (TmRiO n)) (out : Val) : Prop :=
  let π := linObjectCanonicalProjection as ns
  let d := as.length * (tmRiPcsO (gens as) Y).length
  ∃ (pv base block : Val) (VW DW : Matrix (Fin d) (Fin d) ℤ)
      (EW : linObjectOriginalProduct as π Y ≃+ tmGLVec (tmGLQMod DW))
      (VV DV : Matrix (Fin d) (Fin d) ℤ)
      (EV : linObjectOriginalQuotient as π Y ≃+ tmGLVec (tmGLQMod DV)),
    out = .list [pv,base,block,.list [linVecVal (fun i => DW i i),encIntMatrix VW],
      .list [linVecVal (fun i => DV i i),encIntMatrix VV]] ∧
    IsUnit VW.det ∧ (∀ i, 0 < DW i i) ∧
      (∀ z, EW (linObjectOriginalMap as π Y z) = tmGLQMap VW DW z) ∧
    IsUnit VV.det ∧ (∀ i, 0 < DV i i) ∧
      (∀ z, EV (linObjectOriginalQuotientMap as π Y z) = tmGLQMap VV DV z)

theorem linObjectData_frames (Y : List (TmRiO n)) {out : Val}
    (ho : linObjectDataOut as ns Y (linObjectCanonicalProjection as ns) out) :
    linObjectCanonicalFrames as ns Y out := by
  let π := linObjectCanonicalProjection as ns
  obtain ⟨M,groups,L,wn,vn,rfl,hM,hgroups,hLC,hfull,hwn,hvn⟩ := ho
  have hCert : linPresentationCertificate M (linObjectLiftCoord as π) :=
    linPermPresentation_certificate as ns M hM
  have hker := linObjectDataLocal_kernel as π M hCert (linObjectLocalImages as π Y) L hLC
  have hWsurj := linObjectOriginalMap_surjective as π Y hCert.2.1
  have hWker := linObjectOriginalMap_kernel as π Y L hker
  have hVsurj := linObjectOriginalQuotientMap_surjective as π Y hCert.2.1
  have hVker := linObjectOriginalQuotientMap_kernel as π Y hCert.2.1 L hker
  obtain ⟨VW,DW,EW,heW,hVW,hDW,hEW⟩ :=
    linObjectNormalFrame_exists (linObjectBlockMatrix L) (linObjectOriginalMap as π Y) hWsurj hWker hwn
  obtain ⟨VV,DV,EV,heV,hVV,hDV,hEV⟩ :=
    linObjectNormalFrame_exists (linObjectQuotientMatrix L) (linObjectOriginalQuotientMap as π Y) hVsurj hVker hvn
  refine ⟨.list [.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal),.list groups],
    encIntMatrix M,linObjectBlockInput L,VW,DW,EW,VV,DV,EV,?_,hVW,hDW,hEW,hVV,hDV,hEV⟩
  rw [heW,heV]

theorem linObjectCanonical_ker_local (Y : List (TmRiO n)) (hf : Fixes (gens ns) (tmGlMs Y)) :
    ∀ T ∈ pieces (gens as) (tmGlMs Y), (linObjectCanonicalProjection as ns).ker ≤
      (Aut (gens as) T).subgroupOf (gens as) := by
  intro T hT a ha
  have haN : a.val ∈ gens ns := by
    change a ∈ (QuotientGroup.mk' ((gens ns).subgroupOf (gens as))).ker at ha
    rw [QuotientGroup.ker_mk'] at ha
    exact ha
  exact ⟨a.property,(hf.of_le (piece_le hT)).act_eq haN⟩

end GI.Impl
