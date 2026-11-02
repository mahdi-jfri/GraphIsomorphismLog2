import Workspace.Impl.LinObjectGlueFrame
import Workspace.Impl.LinObjectAffineCorrection

namespace GI.Impl
open GI.Cited GI.Multicoset
open scoped IsMulCommutative

variable {n : ℕ} {as ns : List (Equiv.Perm (Fin n))}
variable [((gens ns).subgroupOf (gens as)).Normal]
variable [IsMulCommutative ((gens as) ⧸ (gens ns).subgroupOf (gens as))]
variable {Y : List (TmRiO n)} (F : linObjectGlueFrame as ns Y)
variable (H : Subgroup (Equiv.Perm (Fin n))) (hn : Normalizes H (gens as))
variable (hy : ∀ g ∈ H,Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ g))
variable (hπ : Function.Surjective (linObjectCanonicalProjection as ns))
variable (hker : ∀ T ∈ pieces (gens as) (tmGlMs Y),(linObjectCanonicalProjection as ns).ker ≤
  (Aut (gens as) T).subgroupOf (gens as))

noncomputable def linObjectGlueFrame.rep : H →* (tmGLVec (tmGLQMod F.D) ≃+ tmGLVec (tmGLQMod F.D)) :=
  linObjectFrameRep F.E (linObjectAffineQuotientLinear H (gens as) hn (tmGlMs Y) hy
    (linObjectCanonicalProjection as ns) hπ hker)
noncomputable def linObjectGlueFrame.cocycle (g : H) : tmGLVec (tmGLQMod F.D) :=
  F.E ((linObjectDiagonalModule (gens as) (linObjectCanonicalProjection as ns) (tmGlMs Y)).mkQ
    (linObjectFiniteConfigAction H (gens as) hn (tmGlMs Y) hy
      (linObjectCanonicalProjection as ns) hπ hker g 0))

theorem linObjectGlueFrame.rep_point (g : H) (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n))))
    (hZ : Conf (gens as) (tmGlMs Y) Z) :
    F.rep H hn hy hπ hker g (F.point Z)+F.cocycle H hn hy hπ hker g = F.point (Z ↼ g.val⁻¹) :=
  linObjectFrameQuotient_eval as (linObjectCanonicalProjection as ns) hπ Y hker H hn hy
    (tmGLQMod F.D) F.E g Z hZ

theorem linObjectGlueFrame.cocycle_law (g k : H) :
    F.cocycle H hn hy hπ hker (g*k) = F.rep H hn hy hπ hker g (F.cocycle H hn hy hπ hker k)+
      F.cocycle H hn hy hπ hker g :=
  linObjectFrameRep_cocycle F.E (linObjectAffineQuotientLinear H (gens as) hn (tmGlMs Y) hy
    (linObjectCanonicalProjection as ns) hπ hker)
    (fun g => (linObjectDiagonalModule (gens as) (linObjectCanonicalProjection as ns) (tmGlMs Y)).mkQ
      (linObjectFiniteConfigAction H (gens as) hn (tmGlMs Y) hy (linObjectCanonicalProjection as ns) hπ hker g 0))
    (linObjectAffineQuotient_cocycle H (gens as) hn (tmGlMs Y) hy
      (linObjectCanonicalProjection as ns) hπ hker) g k

theorem linObjectGlueFrame.correct_iff (g : H) (Z : Multiset (CObj ℕ (Equiv.Perm (Fin n))))
    (hZ : Conf (gens as) (tmGlMs Y) Z) :
    F.point Z = F.cocycle H hn hy hπ hker g ↔ ∃ a ∈ gens as,(Z ↼ g.val) ↼ a = tmGlMs Y := by
  have hh := linObjectAffineCorrection_iff H (gens as) hn (tmGlMs Y) hy
    (linObjectCanonicalProjection as ns) hπ hker g Z hZ
  constructor
  · intro he
    exact hh.mp (F.E.injective he)
  · intro he
    exact congrArg F.E (hh.mpr he)

include hker in
theorem linObjectGlueFrame.self_point : F.point (tmGlMs Y) = 0 := by
  unfold linObjectGlueFrame.point
  rw [linObjectConfigCoord_self _ _ _ hker,map_zero,map_zero]

theorem linObjectGlueFrame.frame_indexed (z : Fin (as.length*(tmRiPcsO (gens as) Y).length) → ℤ) :
    F.E (F.q (linObjectProductMap
      (fun i => linObjectGroupImage (gens as) (linObjectCanonicalProjection as ns)
        (Aut (gens as) (tmGlMs ((tmRiPcsO (gens as) Y).get i))))
      (linObjectLiftCoord as (linObjectCanonicalProjection as ns)) (linObjectUnflatten _ _ z))) =
        tmGLQMap F.V F.D z := F.frame z

end GI.Impl
