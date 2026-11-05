module

public import Workspace.Impl.LinObjectGlue
public import Workspace.Impl.LinObjectGlueCoreSpec

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Lang GI.Multicoset

/-- The unmodified hypotheses of TermGlueObjSpec. -/
structure linObjectGlueRaw (n : ℕ) where
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

variable {n : ℕ} (I : linObjectGlueRaw n)

noncomputable def linObjectGlueRaw.value : Val := tmGlIn I.hs I.ns I.as I.X I.Y I.bs I.τ

noncomputable def linObjectGlueRaw.normalize : linObjectGlueProblem n :=
  let Z := I.Y++I.X
  let f := linObjectNorm (linObjectColor Z)
  let hX : ∀ x ∈ I.X,x ∈ Z := fun x hx => List.mem_append_right _ hx
  let hY : ∀ y ∈ I.Y,y ∈ Z := fun y hy => List.mem_append_left _ hy
  { hs := I.hs
    ns := I.ns
    as := keepList I.as
    X := I.X.map f
    Y := I.Y.map f
    bs := I.bs
    τ := I.τ
    solvable := I.solvable
    objsIn := by
      intro o ho
      rw [← List.map_append] at ho
      obtain ⟨o₀, ho₀, rfl⟩ := List.mem_map.mp ho
      rw [tmRiStab_linObjectNorm]
      exact I.objsIn o₀ ho₀
    NA := by simpa only [gens_keepList] using I.NA
    AH := by simpa only [gens_keepList] using I.AH
    normalN := I.normalN
    normalA := by simpa only [gens_keepList] using I.normalA
    abelian := by simpa only [gens_keepList] using I.abelian
    fixX := (linObjectNorm_fixes Z I.X hX (gens I.ns)).mpr I.fixX
    fixY := (linObjectNorm_fixes Z I.Y hY (gens I.ns)).mpr I.fixY
    AB := by simpa only [gens_keepList] using I.AB
    BH := I.BH
    τH := I.τH
    P1 := by
      intro g hg
      rw [gens_keepList]
      exact (linObjectNorm_conf_act Z I.X I.X hX hX (gens I.as) g).mpr (I.P1 g hg)
    P2 := by
      intro g hg
      rw [gens_keepList]
      exact (linObjectNorm_conf_act Z I.X I.Y hX hY (gens I.as) (g*I.τ)).mpr (I.P2 g hg)
    P3 := by
      intro g hg
      rw [gens_keepList]
      exact (linObjectNorm_conf_act Z I.Y I.Y hY hY (gens I.as) (I.τ⁻¹*g*I.τ)).mpr (I.P3 g hg)
    P4 := by
      intro h hh
      have he := linObjectNorm_iso_in Z I.X I.Y hX hY (gens I.hs)
      rw [he] at hh
      exact I.P4 h hh
    P5 := by
      intro g hg
      have he := linObjectNorm_iso_in Z I.X I.X hX hX (gens I.hs)
      change g ∈ Iso (gens I.hs) (tmGlMs (I.X.map f)) (tmGlMs (I.X.map f)) at hg
      rw [he] at hg
      exact I.P5 hg
    compact := length_keepList_le _
    targetOK := by
      simpa only [List.length_map] using linObjectNorm_prefix_ok I.Y I.X
    jointOK := by
      simpa only [Z,f,List.map_append,List.length_map,List.length_append] using linObjectNorm_rec_ok Z }

theorem linObjectGlueRaw.normalize_iso :
    Iso (gens I.normalize.hs) (tmGlMs I.normalize.X) (tmGlMs I.normalize.Y) =
      Iso (gens I.hs) (tmGlMs I.X) (tmGlMs I.Y) :=
  linObjectNorm_iso_in (I.Y++I.X) I.X I.Y (fun x hx => List.mem_append_right _ hx)
    (fun y hy => List.mem_append_left _ hy) (gens I.hs)

end GI.Impl
