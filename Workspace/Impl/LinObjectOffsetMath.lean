import Workspace.Impl.LinObjectConfigAction

/-! In a configuration, a row of local transporters has a nonempty
entry, and every such entry points to the same part of the configuration. -/
namespace GI.Impl
open GI.Multicoset
variable {G Ω : Type*} [Group G] [RAct G Ω]

theorem linObjectConfig_part_mem_pieces {A : Subgroup G} {Y Z T : Multiset Ω}
    (hZ : Conf A Y Z) (hT : T ∈ pieces A Y) : partAt A Z T ∈ pieces A Z := by
  obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero (piece_ne_zero hT)
  let a := coord A Z T
  have ha : a ∈ A := (coord_spec hZ hT).1
  have hz : t ↼ a ∈ partAt A Z T := by
    rw [(coord_spec hZ hT).2]
    exact act_mem_act a ht
  have hzZ : t ↼ a ∈ Z := (mem_partAt.mp hz).1
  have he : partAt A Z T = partAt A Z {t ↼ a} := by
    apply partAt_congr (t₀ := t ↼ a)
    · intro s hs
      exact (sameOrb_act_self t ha).symm.trans (piece_sameOrb hT ht hs)
    · intro s hs
      rw [Multiset.mem_singleton] at hs
      rw [hs]
      exact sameOrb_refl A _
    · exact piece_ne_zero hT
    · simp
  exact mem_pieces.mpr ⟨t ↼ a, hzZ, he⟩

theorem linObjectConfig_piece_transport {A : Subgroup G} {Y Z T : Multiset Ω}
    (hZ : Conf A Y Z) (hT : T ∈ pieces A Y) :
    ∃ T' ∈ pieces A Z, (Iso A T T').Nonempty := by
  refine ⟨partAt A Z T, linObjectConfig_part_mem_pieces hZ hT,
    coord A Z T, (coord_spec hZ hT).1, ?_⟩
  exact (coord_spec hZ hT).2.symm

theorem linObjectConfig_piece_transport_unique {A : Subgroup G} {Y Z T T' : Multiset Ω}
    (hT : T ∈ pieces A Y) (hT' : T' ∈ pieces A Z)
    {a : G} (ha : a ∈ Iso A T T') : T' = partAt A Z T := by
  obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero (piece_ne_zero hT)
  have hta : t ↼ a ∈ T' := by rw [← ha.2]; exact act_mem_act a ht
  have he : partAt A Z T = partAt A Z T' := by
    apply partAt_congr (t₀ := t)
    · intro s hs
      exact piece_sameOrb hT ht hs
    · intro s hs
      exact (sameOrb_act_self t ha.1).trans (piece_sameOrb hT' hta hs)
    · exact piece_ne_zero hT
    · exact piece_ne_zero hT'
  rw [partAt_piece hT'] at he
  exact he.symm

end GI.Impl
