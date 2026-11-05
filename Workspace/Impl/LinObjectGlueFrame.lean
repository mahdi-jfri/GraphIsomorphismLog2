module

public import Workspace.Impl.LinObjectGlueCore

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset
open scoped IsMulCommutative

variable {n : ℕ} (as ns : List (Equiv.Perm (Fin n)))
variable [((gens ns).subgroupOf (gens as)).Normal]
variable [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))]

/-- The certificates extracted from the computed relation blocks and
Smith form. This record is used in the correctness proof only. -/
structure linObjectGlueFrame (Y : List (TmRiO n)) where
  base : Matrix (Fin as.length) (Fin as.length) ℤ
  groups : List Val
  blocks : Fin (tmRiPcsO (gens as) Y).length →
    Matrix (Fin (as.length+(n^2+1))) (Fin as.length) ℤ
  product : Val
  V : Matrix (Fin (as.length*(tmRiPcsO (gens as) Y).length))
    (Fin (as.length*(tmRiPcsO (gens as) Y).length)) ℤ
  D : Matrix (Fin (as.length*(tmRiPcsO (gens as) Y).length))
    (Fin (as.length*(tmRiPcsO (gens as) Y).length)) ℤ
  E : linObjectOriginalQuotient as (linObjectCanonicalProjection as ns) Y ≃+ tmGLVec (tmGLQMod D)
  presentation : linPresentationCertificate base (linObjectLiftCoord as (linObjectCanonicalProjection as ns))
  localGroups : List.Forall₂ (fun S v => GroupValC n v (Aut (gens as) (tmGlMs S)))
    (tmRiPcsO (gens as) Y) groups
  localKernel : ∀ i,LinearMap.ker ((linObjectLocalImages as (linObjectCanonicalProjection as ns) Y i).mkQ.comp
    (linObjectLiftCoord as (linObjectCanonicalProjection as ns))) = linRelations (blocks i)
  fullRank : ∀ i,Function.Injective (blocks i).mulVec
  invertible : IsUnit V.det
  positive : ∀ i,0 < D i i
  frame : ∀ z,E (linObjectOriginalQuotientMap as (linObjectCanonicalProjection as ns) Y z) = tmGLQMap V D z

variable {as ns}

noncomputable def linObjectGlueFrame.value {Y : List (TmRiO n)} (F : linObjectGlueFrame as ns Y) : Val :=
  .list [.list [.list ((tmRiPcsO (gens as) Y).map tmGlObjsVal),.list F.groups],encIntMatrix F.base,
    linObjectBlockInput F.blocks,F.product,.list [linVecVal (fun i => F.D i i),encIntMatrix F.V]]

theorem linObjectGlueFrame_exists (Y : List (TmRiO n)) {out : Val}
    (h : linObjectDataOut as ns Y (linObjectCanonicalProjection as ns) out) :
    ∃ F : linObjectGlueFrame as ns Y,F.value = out := by
  let π := linObjectCanonicalProjection as ns
  obtain ⟨M,groups,L,wn,vn,rfl,hM,hgroups,hLC,hfull,hwn,hvn⟩ := h
  have hCert := linPermPresentation_certificate as ns M hM
  have hker := linObjectDataLocal_kernel as π M hCert (linObjectLocalImages as π Y) L hLC
  have hsurj := linObjectOriginalQuotientMap_surjective as π Y hCert.2.1
  have hqker := linObjectOriginalQuotientMap_kernel as π Y hCert.2.1 L hker
  obtain ⟨V,D,E,he,hV,hD,hE⟩ := linObjectNormalFrame_exists (linObjectQuotientMatrix L)
    (linObjectOriginalQuotientMap as π Y) hsurj hqker hvn
  refine ⟨⟨M,groups,L,wn,V,D,E,hCert,hgroups,hker,hfull,hV,hD,hE⟩,?_⟩
  change Val.list [_,_,_,_,_] = _
  rw [he]

noncomputable def linObjectGlueFrame.q {Y : List (TmRiO n)} (_F : linObjectGlueFrame as ns Y) :
    linObjectIndexedProduct as (linObjectCanonicalProjection as ns) Y →+
      linObjectOriginalQuotient as (linObjectCanonicalProjection as ns) Y :=
  ((linObjectDiagonalModule (gens as) (linObjectCanonicalProjection as ns) (tmGlMs Y)).mkQ.toAddMonoidHom).comp
    (linObjectPieceReindex as (linObjectCanonicalProjection as ns) Y).toAddMonoidHom

noncomputable def linObjectGlueFrame.point {Y : List (TmRiO n)} (F : linObjectGlueFrame as ns Y)
    (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n)))) : tmGLVec (tmGLQMod F.D) :=
  F.E ((linObjectDiagonalModule (gens as) (linObjectCanonicalProjection as ns) (tmGlMs Y)).mkQ
    (linObjectConfigCoord (gens as) (linObjectCanonicalProjection as ns) (tmGlMs Y) Z))

theorem linObjectGlueFrame.point_indexed {Y : List (TmRiO n)} (F : linObjectGlueFrame as ns Y)
    (hπ : Function.Surjective (linObjectCanonicalProjection as ns))
    (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y),(linObjectCanonicalProjection as ns).ker ≤
      (Aut (gens as) T).subgroupOf (gens as))
    (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n)))) (hZ : Conf (gens as) (tmGlMs Y) Z) :
    F.E (F.q (linObjectIndexedConfigEquiv as (linObjectCanonicalProjection as ns) hπ Y hker ⟨Z,hZ⟩)) = F.point Z := by
  change F.E ((linObjectDiagonalModule (gens as) (linObjectCanonicalProjection as ns) (tmGlMs Y)).mkQ
    (linObjectPieceReindex as (linObjectCanonicalProjection as ns) Y _)) = _
  rw [linObjectPieceReindex_indexedConfig]
  rfl

end GI.Impl
