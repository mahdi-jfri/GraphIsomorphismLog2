import Workspace.Impl.LinObjectGluePrefix

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset
open scoped IsMulCommutative

variable {n : ℕ} (I : linObjectGlueProblem n)
variable [((gens I.ns).subgroupOf (gens I.as)).Normal]
variable [IsMulCommutative ((gens I.as) ⧸ (gens I.ns).subgroupOf (gens I.as))]

noncomputable def linObjectGlueProblem.affineC (F : linObjectGlueFrame I.as I.ns I.Y) :
    gens I.coverGenerators → tmGLVec (tmGLQMod F.D) :=
  F.cocycle (gens I.coverGenerators) (I.normalA.mono I.cover_H) I.cover_conf
    (QuotientGroup.mk'_surjective _) (linObjectCanonical_ker_local I.as I.ns I.Y I.fixY)

theorem linObjectGlueProblem.affine_correct (F : linObjectGlueFrame I.as I.ns I.Y) (g : gens I.coverGenerators) :
    I.affineC F g = F.point (tmGlMs I.X ↼ I.τ) ↔
      ∃ a ∈ gens I.as,(tmGlMs I.X ↼ (I.τ*g.val)) ↼ a = tmGlMs I.Y := by
  have hh := F.correct_iff (gens I.coverGenerators) (I.normalA.mono I.cover_H) I.cover_conf
    (QuotientGroup.mk'_surjective _) (linObjectCanonical_ker_local I.as I.ns I.Y I.fixY) g
    (tmGlMs I.X ↼ I.τ) I.source_conf
  simpa only [eq_comm,act_act] using hh

theorem linObjectGlueProblem.zero_correct (F : linObjectGlueFrame I.as I.ns I.Y) (g : gens I.coverGenerators) :
    I.affineC F g = 0 ↔ ∃ a ∈ gens I.as,(tmGlMs I.Y ↼ g.val) ↼ a = tmGlMs I.Y := by
  have hk := linObjectCanonical_ker_local I.as I.ns I.Y I.fixY
  have hh := F.correct_iff (gens I.coverGenerators) (I.normalA.mono I.cover_H) I.cover_conf
    (QuotientGroup.mk'_surjective _) hk g (tmGlMs I.Y) (conf_self _ _)
  rw [F.self_point hk] at hh
  exact (eq_comm).trans hh

theorem linObjectGlueProblem.affine_nonempty (F : linObjectGlueFrame I.as I.ns I.Y) :
    (I.affineSet F).Nonempty ↔ (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y)).Nonempty := by
  constructor
  · rintro ⟨r,hr⟩
    obtain ⟨g,hg,rfl⟩ := hr
    have he : I.affineC F g = F.point (tmGlMs I.X ↼ I.τ) := by simpa only [map_zero,zero_add] using hg
    obtain ⟨a,ha,he⟩ := (I.affine_correct F g).mp he
    refine ⟨I.τ*g.val*a,(gens I.hs).mul_mem ((gens I.hs).mul_mem I.τH (I.cover_H g.property)) (I.AH ha),?_⟩
    rwa [← act_act]
  · rintro ⟨t,ht⟩
    have hg : I.τ⁻¹*t ∈ gens I.coverGenerators := by
      rw [I.cover_eq]
      change I.τ*(I.τ⁻¹*t)*I.τ⁻¹ ∈ gens I.bs
      simpa only [mul_inv_cancel_left] using I.P4 t ht
    let g : gens I.coverGenerators := ⟨I.τ⁻¹*t,hg⟩
    have he : I.affineC F g = F.point (tmGlMs I.X ↼ I.τ) := (I.affine_correct F g).mpr ⟨1,(gens I.as).one_mem,by
      simpa only [g,mul_inv_cancel_left,act_one] using ht.2⟩
    refine ⟨g.val,g,?_,rfl⟩
    simpa only [map_zero,zero_add] using he

def linObjectGlueSuccessData (F : linObjectGlueFrame I.as I.ns I.Y) (r : Equiv.Perm (Fin n))
    (ls : List (Equiv.Perm (Fin n))) : Prop :=
  r ∈ gens I.coverGenerators ∧
    (∃ a ∈ gens I.as,(tmGlMs I.X ↼ (I.τ*r)) ↼ a = tmGlMs I.Y) ∧
    (∀ g ∈ 1::ls,g ∈ gens I.hs ∧ Conf (gens I.as) (tmGlMs I.Y) (tmGlMs I.Y ↼ g) ∧
      ∃ a ∈ gens I.as,(tmGlMs I.Y ↼ g) ↼ a = tmGlMs I.Y) ∧
    Aut (gens I.hs) (tmGlMs I.Y) ≤ gens (1::ls)

theorem linObjectGens_cons_one (ls : List (Equiv.Perm (Fin n))) : gens (1::ls) = gens ls := by
  simpa only [List.nil_append] using gens_append_cons_of_mem (a:=[]) (l:=ls) (gens []).one_mem

set_option maxHeartbeats 400000 in
theorem linObjectGlueProblem.affine_success (F : linObjectGlueFrame I.as I.ns I.Y)
    (r : Equiv.Perm (Fin n)) (ls : List (Equiv.Perm (Fin n)))
    (hT : I.affineSet F = (fun l => r*l) '' (gens ls : Set (Equiv.Perm (Fin n)))) :
    linObjectGlueSuccessData I F r ls := by
  let H := gens I.coverGenerators
  let hk := linObjectCanonical_ker_local I.as I.ns I.Y I.fixY
  let ρ := F.rep H (I.normalA.mono I.cover_H) I.cover_conf (QuotientGroup.mk'_surjective _) hk
  let c := I.affineC F
  have hc : ∀ g k,c (g*k) = ρ g (c k)+c g :=
    F.cocycle_law H (I.normalA.mono I.cover_H) I.cover_conf (QuotientGroup.mk'_surjective _) hk
  obtain ⟨u,hu,hur,hL,hzero⟩ := linObjectAffineCoset_group I.coverGenerators (tmGLQMod F.D) ρ c hc
    (F.point (tmGlMs I.X ↼ I.τ)) r ls hT
  have hr : r ∈ H := hu ▸ u.property
  have hcorr : ∃ a ∈ gens I.as,(tmGlMs I.X ↼ (I.τ*r)) ↼ a = tmGlMs I.Y := by
    have hh := (I.affine_correct F u).mp hur
    rwa [hu] at hh
  have ht : (Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y)).Nonempty := by
    obtain ⟨a,ha,he⟩ := hcorr
    exact ⟨I.τ*r*a,(gens I.hs).mul_mem ((gens I.hs).mul_mem I.τH (I.cover_H hr)) (I.AH ha),by rwa [← act_act]⟩
  obtain ⟨t,ht⟩ := ht
  have hAutCover : Aut (gens I.hs) (tmGlMs I.Y) ≤ H := by
    rw [show H = conjR (gens I.bs) I.τ from I.cover_eq]
    exact linObjectAut_target_cover _ _ _ _ _ _ ht (I.P4 t ht) I.P5
  have hcov : Aut (gens I.hs) (tmGlMs I.Y) ≤ gens ls := by
    intro g hg
    let k : H := ⟨g,hAutCover hg⟩
    apply (hzero k).mpr
    exact (I.zero_correct F k).mpr ⟨1,(gens I.as).one_mem,by simpa only [act_one] using hg.2⟩
  refine ⟨hr,hcorr,?_,by rwa [linObjectGens_cons_one]⟩
  intro g hg
  have hgl : g ∈ gens ls := by
    rcases List.mem_cons.mp hg with rfl | hg
    · exact (gens ls).one_mem
    · exact Subgroup.subset_closure hg
  let k : H := ⟨g,hL hgl⟩
  exact ⟨I.cover_H k.property,I.cover_conf g k.property,(I.zero_correct F k).mp ((hzero k).mp hgl)⟩

end GI.Impl
