module

public import Workspace.Impl.LinObjectKernel
public import Workspace.Impl.LinObjectPieceIndex

@[expose] public section

namespace GI.Impl
open GI.Cited GI.Multicoset

theorem linObjectKernel_aut_eq {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n)) :
    linObjectKernelPrefix (gens as) ((tmRiPcsO (gens as) Y).map fun S => Aut (gens as) (tmGlMs S))
      (tmRiPcsO (gens as) Y).length = Aut (gens as) (tmGlMs Y) := by
  classical
  let refs := tmRiPcsO (gens as) Y
  have hRef (S : List (TmRiO n)) (hS : S ∈ refs) : tmGlMs S ∈ pieces (gens as) (tmGlMs Y) := by
    have hh : tmGlMs S ∈ ((refs.map tmGlMs : List _) : Multiset _) := by
      simp only [Multiset.mem_coe,List.mem_map]
      exact ⟨S,hS,rfl⟩
    rw [tmRiPcsO_ms] at hh
    exact hh
  ext g
  have hi := linObjectKernelPrefix_mem (gens as) (refs.map fun S => Aut (gens as) (tmGlMs S)) g
  simp only [List.length_map] at hi
  rw [hi]
  constructor
  · rintro ⟨hg,hB⟩
    refine ⟨hg,fix_of_pieces (A := gens as) ?_⟩
    intro T hT
    obtain ⟨i,he⟩ := (linObjectPieceIndex as Y).surjective ⟨T,hT⟩
    have he' : tmGlMs (refs.get i) = T := congrArg Subtype.val he
    have hm := hB (Aut (gens as) (tmGlMs (refs.get i))) (List.mem_map.mpr ⟨refs.get i,List.get_mem refs i,rfl⟩)
    rw [he'] at hm
    exact hm.2
  · intro hg
    refine ⟨hg.1,?_⟩
    intro B hB
    obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hB
    exact ⟨hg.1,piece_act_of_fix (hRef S hS) hg.1 hg.2⟩

end GI.Impl
