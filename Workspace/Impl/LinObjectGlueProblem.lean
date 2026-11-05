module

public import Workspace.Impl.LinObjectGlueGrowth
public import Workspace.Impl.LinObjectGlueAction

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

/-- The hypotheses of one normalized A.20 object-glue call. All fields
are mathematical input conditions, not additional algorithmic tasks. -/
structure linObjectGlueProblem (n : ℕ) where
  hs : List (Equiv.Perm (Fin n))
  ns : List (Equiv.Perm (Fin n))
  as : List (Equiv.Perm (Fin n))
  X : List (TmRiO n)
  Y : List (TmRiO n)
  bs : List (Equiv.Perm (Fin n))
  τ : Equiv.Perm (Fin n)
  solvable : ∀ [((gens ns).subgroupOf (gens hs)).Normal], IsSolvable ((gens hs) ⧸ (gens ns).subgroupOf (gens hs))
  objsIn : TmRiListIn (gens hs) (X ++ Y)
  NA : gens ns ≤ gens as
  AH : gens as ≤ gens hs
  normalN : GI.Multicoset.Normalizes (gens hs) (gens ns)
  normalA : GI.Multicoset.Normalizes (gens hs) (gens as)
  abelian : ∀ a ∈ gens as,∀ b ∈ gens as,a*b*a⁻¹*b⁻¹ ∈ gens ns
  fixX : Fixes (gens ns) (tmGlMs X)
  fixY : Fixes (gens ns) (tmGlMs Y)
  AB : gens as ≤ gens bs
  BH : gens bs ≤ gens hs
  τH : τ ∈ gens hs
  P1 : ∀ g ∈ gens bs,Conf (gens as) (tmGlMs X) (tmGlMs X ↼ g)
  P2 : ∀ g ∈ gens bs,Conf (gens as) (tmGlMs Y) (tmGlMs X ↼ (g*τ))
  P3 : ∀ g ∈ gens bs,Conf (gens as) (tmGlMs Y) (tmGlMs Y ↼ (τ⁻¹*g*τ))
  P4 : ∀ h ∈ Iso (gens hs) (tmGlMs X) (tmGlMs Y),h*τ⁻¹ ∈ gens bs
  P5 : Aut (gens hs) (tmGlMs X) ≤ gens bs
  compact : as.length ≤ n^2
  targetOK : TmRecObjOK Y.length Y
  jointOK : TmRecObjOK (Y.length+X.length) (Y++X)

variable {n : ℕ} (I : linObjectGlueProblem n)

noncomputable def linObjectGlueProblem.value : Val := tmGlIn I.hs I.ns I.as I.X I.Y I.bs I.τ

def linObjectGlueProblem.coverGenerators : List (Equiv.Perm (Fin n)) := linConjugateGenerators I.bs I.τ

theorem linObjectGlueProblem.cover_eq : gens I.coverGenerators = conjR (gens I.bs) I.τ := by
  rw [linObjectGlueProblem.coverGenerators,linConjugateGenerators_gens,linObjectTargetCover]

theorem linObjectGlueProblem.A_cover : gens I.as ≤ gens I.coverGenerators := by
  rw [I.cover_eq]
  exact (linObjectTargetCover_props (gens I.hs) (gens I.as) (gens I.bs) I.AH I.normalA I.AB I.BH I.τ I.τH).1

theorem linObjectGlueProblem.cover_H : gens I.coverGenerators ≤ gens I.hs := by
  rw [I.cover_eq]
  exact (linObjectTargetCover_props (gens I.hs) (gens I.as) (gens I.bs) I.AH I.normalA I.AB I.BH I.τ I.τH).2

theorem linObjectGlueProblem.norm_X : TmRiListNorm (gens I.as) I.X :=
  TmRiListIn.norm_of (fun o ho => I.objsIn o (List.mem_append_left _ ho)) I.normalA

theorem linObjectGlueProblem.norm_Y : TmRiListNorm (gens I.as) I.Y :=
  TmRiListIn.norm_of (fun o ho => I.objsIn o (List.mem_append_right _ ho)) I.normalA

theorem linObjectGlueProblem.norm_YX : TmRiListNorm (gens I.as) (I.Y ++ I.X) :=
  I.norm_Y.append I.norm_X

theorem linObjectGlueProblem.cover_conf : ∀ g ∈ gens I.coverGenerators,
    Conf (gens I.as) (tmGlMs I.Y) (tmGlMs I.Y ↼ g) := by
  intro g hg
  rw [I.cover_eq] at hg
  have hh := I.P3 (I.τ*g*I.τ⁻¹) hg
  have he : I.τ⁻¹*(I.τ*g*I.τ⁻¹)*I.τ = g := by group
  rwa [he] at hh

open scoped IsMulCommutative in
theorem linObjectGlueProblem.solvable_rep
    [((gens I.ns).subgroupOf (gens I.as)).Normal]
    [IsMulCommutative ((gens I.as) ⧸ (gens I.ns).subgroupOf (gens I.as))]
    (F : linObjectGlueFrame I.as I.ns I.Y) :
    IsSolvable (F.rep (gens I.coverGenerators) (I.normalA.mono I.cover_H) I.cover_conf
      (QuotientGroup.mk'_surjective _) (linObjectCanonical_ker_local I.as I.ns I.Y I.fixY)).range :=
  F.solvable_rep (gens I.coverGenerators) (I.normalA.mono I.cover_H) I.cover_conf
    (QuotientGroup.mk'_surjective _) (linObjectCanonical_ker_local I.as I.ns I.Y I.fixY)
    I.cover_H I.normalN I.solvable (I.normalN.mono I.AH) I.fixY

theorem linObjectGlueProblem.source_conf : Conf (gens I.as) (tmGlMs I.Y) (tmGlMs I.X ↼ I.τ) := by
  simpa only [one_mul] using I.P2 1 (gens I.bs).one_mem

theorem linObjectGlueProblem.source_cover_conf (g : Equiv.Perm (Fin n)) (hg : g ∈ gens I.coverGenerators) :
    Conf (gens I.as) (tmGlMs I.Y) (tmGlMs I.X ↼ (I.τ*g)) := by
  rw [I.cover_eq] at hg
  have hh := I.P2 (I.τ*g*I.τ⁻¹) hg
  have he : I.τ*g*I.τ⁻¹*I.τ = I.τ*g := by group
  rwa [he] at hh

end GI.Impl
