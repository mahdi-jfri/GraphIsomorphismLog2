import Workspace.Impl.LinObjectCorrectedAut
import Workspace.Impl.LinObjectCorrectMapObject

namespace GI.Impl
open GI.Cited GI.Multicoset

theorem linObjectGens_get {n : ℕ} (gs : List (Equiv.Perm (Fin n))) :
    Subgroup.closure (Set.range (fun i : Fin gs.length => gs.get i)) = gens gs := by
  congr 1
  ext g
  exact List.mem_iff_get.symm

theorem linObjectCorrectedList_eq {n : ℕ} (H A : Subgroup (Equiv.Perm (Fin n)))
    (hAH : A ≤ H) (hA : Normalizes H A) (Y : Multiset (CObj ℕ (Equiv.Perm (Fin n))))
    (gs ks : List (Equiv.Perm (Fin n))) (hgs : ∀ g ∈ gs, g ∈ H)
    (hcover : Aut H Y ≤ gens gs) (hk : List.Forall₂ (linObjectCorrectPair A Y) gs ks) :
    gens ks ⊔ Aut A Y = Aut H Y := by
  let orig : Fin gs.length → Equiv.Perm (Fin n) := fun i => gs.get i
  let corr : Fin gs.length → Equiv.Perm (Fin n) := fun i => ks.get (i.cast hk.length_eq)
  have hlen := hk.length_eq
  have hpair (i : Fin gs.length) : linObjectCorrectPair A Y (orig i) (corr i) :=
    hk.get i.isLt (by omega)
  have hoH (i : Fin gs.length) : orig i ∈ H := hgs _ (List.get_mem _ _)
  have hcH (i : Fin gs.length) : corr i ∈ H := by
    obtain ⟨a,ha,he,_⟩ := hpair i
    rw [he]
    exact H.mul_mem (hoH i) (hAH ha)
  have hcov : Aut H Y ≤ Subgroup.closure (Set.range orig) := by
    simpa only [orig,linObjectGens_get] using hcover
  have hcS (i : Fin gs.length) : corr i ∈ Aut H Y := by
    refine ⟨hcH i,?_⟩
    obtain ⟨a,ha,he,hy⟩ := hpair i
    rw [he,← act_act]
    exact hy
  have hdiff (i : Fin gs.length) : (orig i)⁻¹*corr i ∈ A := by
    obtain ⟨a,ha,he,_⟩ := hpair i
    simpa only [he,inv_mul_cancel_left] using ha
  have hr := linObjectCorrectedAut_eq H A hAH hA Y orig corr hoH hcH hcov hcS hdiff
  have he : Set.range corr = {k | k ∈ ks} := by
    ext k
    constructor
    · rintro ⟨i,rfl⟩
      exact List.get_mem _ _
    · intro hk'
      obtain ⟨i,hi⟩ := List.mem_iff_get.mp hk'
      exact ⟨i.cast hk.length_eq.symm,by simpa only [corr,Fin.cast_cast,Fin.cast_refl] using hi⟩
  rwa [he] at hr

end GI.Impl
