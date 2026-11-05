module

public import Workspace.Impl.LinObjectGlueFrame
public import Workspace.Impl.LinObjectAffineCorrection

@[expose] public section

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

theorem conf_act_eq_of_mem {A N : Subgroup (Equiv.Perm (Fin n))} (hAN : Normalizes A N)
    {Y Z : Multiset (CObj ℕ (Equiv.Perm (Fin n)))} (hfY : Fixes N Y) (hZ : Conf A Y Z)
    {k : Equiv.Perm (Fin n)} (hk : k ∈ N) : Z ↼ k = Z := by
  obtain ⟨w, hw, rfl⟩ := hZ
  rw [sum_act]
  exact Finset.sum_congr rfl fun T hT => ((hfY.of_le (piece_le hT)).act hAN (hw T hT)).act_eq hk

theorem linObjectGlueFrame.rep_eq_one_of_mem
    (hAN : Normalizes (gens as) (gens ns)) (hfY : Fixes (gens ns) (tmGlMs Y))
    {g : H} (hg : g.val ∈ gens ns) :
    F.rep H hn hy hπ hker g = 1 := by
  have hc0 : F.cocycle H hn hy hπ hker g = 0 := by
    have hr := F.rep_point H hn hy hπ hker g (tmGlMs Y) (conf_self _ _)
    rw [F.self_point hker, map_zero, zero_add,
      conf_act_eq_of_mem hAN hfY (conf_self _ _) ((gens ns).inv_mem hg),
      F.self_point hker] at hr
    exact hr
  ext x : 1
  obtain ⟨w, hw⟩ := Submodule.mkQ_surjective
    (linObjectDiagonalModule (gens as) (linObjectCanonicalProjection as ns) (tmGlMs Y)) (F.E.symm x)
  obtain ⟨Z, hZ, hZcoord⟩ := linObjectConfigCoord_surjective (gens as)
    (linObjectCanonicalProjection as ns) hπ (tmGlMs Y) hker w
  have hx : F.point Z = x := by
    unfold linObjectGlueFrame.point
    rw [hZcoord, hw, F.E.apply_symm_apply]
  rw [← hx]
  have hr := F.rep_point H hn hy hπ hker g Z hZ
  rw [hc0, add_zero, conf_act_eq_of_mem hAN hfY hZ ((gens ns).inv_mem hg)] at hr
  exact hr

theorem linObjectGlueFrame.solvable_rep {K : Subgroup (Equiv.Perm (Fin n))}
    (hHK : H ≤ K) (hKN : Normalizes K (gens ns))
    (hsol : ∀ [((gens ns).subgroupOf K).Normal], IsSolvable (K ⧸ (gens ns).subgroupOf K))
    (hAN : Normalizes (gens as) (gens ns)) (hfY : Fixes (gens ns) (tmGlMs Y)) :
    IsSolvable (F.rep H hn hy hπ hker).range := by
  have : ((gens ns).subgroupOf K).Normal :=
    ⟨fun n hn k => hKN k.1 k.2 n.1 hn⟩
  have : Group.IsSolvable (K ⧸ (gens ns).subgroupOf K) := hsol
  let φ : H →* K ⧸ (gens ns).subgroupOf K :=
    (QuotientGroup.mk' ((gens ns).subgroupOf K)).comp (Subgroup.inclusion hHK)
  have hker_φ : φ.ker = (gens ns).subgroupOf H := by
    ext h
    simp [φ, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have : Group.IsSolvable (H ⧸ φ.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.quotientKerEquivRange φ).injective
  have hle : φ.ker ≤ (F.rep H hn hy hπ hker).rangeRestrict.ker := by
    rw [hker_φ]
    intro g hg
    exact Subtype.ext (F.rep_eq_one_of_mem H hn hy hπ hker hAN hfY hg)
  let ψ := QuotientGroup.lift φ.ker (F.rep H hn hy hπ hker).rangeRestrict hle
  have hsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨g, hg⟩ := (F.rep H hn hy hπ hker).rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk g, hg⟩
  exact Group.isSolvable_of_surjective hsurj

end GI.Impl
