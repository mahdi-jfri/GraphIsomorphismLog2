import Workspace.Impl.AggStab
import Workspace.Impl.AggMT
import Workspace.LocalPermFamilies

/-!
# The group `P_T` as a preimage of labels

The certificate phase starts each test set `T` from `P_T` (`GI.LocalGroups.Pgrp`), a subgroup
of the faithful image `G|_dom`. The program works with its lift to `G`. `liftGroup_Pgrp`: this
lift is the part of `G` whose label permutation lies in `M_T = Alt(T) × Alt(Tᶜ)`. So the program
gets `P_T` in graph form from one **Preimage** call with the generators `cycGen T u v w` of
`M_T` (`closure_cycGens`).
-/

namespace GI.Impl

open Equiv Equiv.Perm GI.Algorithm GI.LocalGroups

variable {Ω C : Type} {S : State Ω C} {L : GiantLabels S}

/-- **The lift of `P_T` is the preimage of `M_T`.** The hypothesis `hπ` says that the label map
`πd` of `G|_dom` agrees with the label map `π` of `G` (`Aggregation.πd_spec`). -/
theorem liftGroup_Pgrp (πd : S.domGroup →* alternatingGroup (Fin L.q))
    (hπ : ∀ g : S.G, πd ⟨S.domHom g, g, rfl⟩ = L.π g) (T : Finset (Fin L.q)) :
    S.liftGroup (Pgrp S.domGroup πd T) = labPre (L := L) (MT T) := by
  rw [MT_eq_KT]
  ext g
  rw [State.mem_liftGroup]
  have hlab : ∀ hg : g ∈ S.G, ∀ hm : S.domHom ⟨g, hg⟩ ∈ S.domGroup,
      lab S.domGroup πd (S.domHom ⟨g, hg⟩) = (L.π ⟨g, hg⟩ : Perm (Fin L.q)) := by
    intro hg hm
    rw [lab_of_mem hm, ← hπ ⟨g, hg⟩]
  constructor
  · rintro ⟨hg, hP⟩
    obtain ⟨hQ, hs⟩ := mem_Pgrp.1 hP
    have h : ∀ c, (L.π ⟨g, hg⟩ : Perm (Fin L.q)) c ∈ T ↔ c ∈ T := fun c => by
      rw [← hlab hg hQ.1]; exact hQ.2 c
    refine ⟨hg, h, ?_, (L.π ⟨g, hg⟩).2⟩
    have e : (L.π ⟨g, hg⟩ : Perm (Fin L.q)).subtypePerm h = restrictQ S.domGroup πd T ⟨_, hQ⟩ := by
      refine Equiv.ext fun c => Subtype.ext ?_
      rw [restrictQ_apply, hlab hg hQ.1]
      rfl
    rw [e]; exact hs
  · rintro ⟨hg, h, s1, -⟩
    have hm : S.domHom ⟨g, hg⟩ ∈ S.domGroup := ⟨⟨g, hg⟩, rfl⟩
    have hQ : S.domHom ⟨g, hg⟩ ∈ Qgrp S.domGroup πd T :=
      ⟨hm, fun c => by rw [hlab hg hm]; exact h c⟩
    refine ⟨hg, mem_Pgrp.2 ⟨hQ, ?_⟩⟩
    have e : (L.π ⟨g, hg⟩ : Perm (Fin L.q)).subtypePerm h = restrictQ S.domGroup πd T ⟨_, hQ⟩ := by
      refine Equiv.ext fun c => Subtype.ext ?_
      rw [restrictQ_apply, hlab hg hm]
      rfl
    rw [← e]; exact s1

end GI.Impl
