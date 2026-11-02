import Workspace.Impl.LinObjectOffsetsSpec

namespace GI.Impl
open GI.Cited GI.Multicoset

/-- The runtime list of reference pieces enumerates the mathematical index set once. -/
theorem linObjectPieceIndex_bijective {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n)) :
    Function.Bijective (fun i : Fin (tmRiPcsO (gens as) Y).length =>
      (⟨tmGlMs ((tmRiPcsO (gens as) Y).get i), by
        have hm := List.get_mem (tmRiPcsO (gens as) Y) i
        have hh : tmGlMs ((tmRiPcsO (gens as) Y).get i) ∈
            (((tmRiPcsO (gens as) Y).map tmGlMs : List _) : Multiset _) := by simp; exact ⟨_, hm, rfl⟩
        rw [tmRiPcsO_ms] at hh
        exact hh⟩ : ↥(pieces (gens as) (tmGlMs Y)))) := by
  let refs := tmRiPcsO (gens as) Y
  have hnd : (refs.map tmGlMs).Nodup := by
    have hh := (pieces (gens as) (tmGlMs Y)).nodup
    rw [← tmRiPcsO_ms] at hh
    exact hh
  constructor
  · intro i j he
    apply Fin.ext
    apply (hnd.getElem_inj_iff
      (hi := by simpa only [List.length_map, refs] using i.isLt)
      (hj := by simpa only [List.length_map, refs] using j.isLt)).mp
    simpa [refs] using congrArg Subtype.val he
  · intro T
    have hh := T.property
    change T.val ∈ (pieces (gens as) (tmGlMs Y)).val at hh
    rw [← tmRiPcsO_ms] at hh
    obtain ⟨S, hS, he⟩ := List.mem_map.mp (Multiset.mem_coe.mp hh)
    obtain ⟨i, hi⟩ := List.get_of_mem hS
    refine ⟨i, Subtype.ext ?_⟩
    simpa only [hi] using he

noncomputable def linObjectPieceIndex {n : ℕ} (as : List (Equiv.Perm (Fin n))) (Y : List (TmRiO n)) :
    Fin (tmRiPcsO (gens as) Y).length ≃ ↥(pieces (gens as) (tmGlMs Y)) :=
  Equiv.ofBijective _ (linObjectPieceIndex_bijective as Y)

end GI.Impl
