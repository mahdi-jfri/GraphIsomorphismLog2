import Workspace.Impl.LinObjectConfigMath

/-! An arbitrary valid choice of local transporters obeys the same
affine law. This is the form used when constructing matrix columns. -/
namespace GI.Impl
open GI.Cited GI.Multicoset

variable {G Ω : Type*} [Group G] [RAct G Ω]

theorem linObject_partAt_act_repr {H A : Subgroup G} (hn : Normalizes H A)
    {Y Z : Multiset Ω} {g : G} (hg : g ∈ H) (hYg : Conf A Y (Y ↼ g))
    (w : Multiset Ω → G)
    (hw : ∀ S ∈ pieces A Y, partAt A Z S = S ↼ w S)
    {T : Multiset Ω} (hT : T ∈ pieces A Y) :
    partAt A (Z ↼ g) T =
      T ↼ (coord A (Y ↼ g) T * (g⁻¹ * w (src A Y g T) * g)) := by
  obtain ⟨hsrc, hsrcY⟩ := src_spec hn hg hYg hT
  obtain ⟨hu, hu'⟩ := coord_spec hYg hT
  have hcong : partAt A (Z ↼ g) T = partAt A (Z ↼ g) (src A Y g T ↼ g) := by
    obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero (piece_ne_zero hT)
    apply partAt_congr (t₀ := t)
    · intro s hs
      exact piece_sameOrb hT ht hs
    · intro s hs
      have hm : s ∈ partAt A (Y ↼ g) T := by rw [hsrcY]; exact hs
      obtain ⟨_, t', ht', ht's⟩ := mem_partAt.mp hm
      exact (piece_sameOrb hT ht ht').trans ht's
    · exact piece_ne_zero hT
    · exact act_ne_zero (piece_ne_zero hsrc) g
  rw [hcong, partAt_act hn hg, hw _ hsrc, act_act]
  have he : src A Y g T ↼ (w (src A Y g T) * g) =
      src A Y g T ↼ g ↼ (g⁻¹ * w (src A Y g T) * g) := by
    rw [act_act]
    congr 1
    group
  rw [he, ← hsrcY, hu', act_act]

end GI.Impl

namespace GI.Impl
open GI.Cited GI.Multicoset
variable {n : ℕ} {Q Ω : Type*} [CommGroup Q] [RAct (Equiv.Perm (Fin n)) Ω]

theorem linObjectConfigCoord_of_repr (A : Subgroup (Equiv.Perm (Fin n)))
    (π : A →* Q) (Y Z : Multiset Ω) (hZ : Conf A Y Z)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A)
    (w : Multiset Ω → Equiv.Perm (Fin n)) (hw : ∀ T ∈ pieces A Y, w T ∈ A)
    (he : ∀ T ∈ pieces A Y, partAt A Z T = T ↼ w T)
    (T : {T // T ∈ pieces A Y}) :
    linObjectConfigCoord A π Y Z T =
      (linObjectGroupImage A π (Aut A T.val)).mkQ
        (Additive.ofMul (π ⟨w T.val, hw T.val T.property⟩)) := by
  apply (linObject_mkQ_eq_iff _ _ _).mpr
  apply (linObject_act_eq_iff_image A π T.val (hker T.val T.property)
    (linIntoSubgroup A (coord A Z T.val)) ⟨w T.val, hw T.val T.property⟩).mp
  have hh := linIntoSubgroup_val A _ (coord_spec hZ T.property).1
  change (linIntoSubgroup A (coord A Z T.val)).val = coord A Z T.val at hh
  rw [hh, ← (coord_spec hZ T.property).2, he T.val T.property]

noncomputable def linObjectConfigAction (B A : Subgroup (Equiv.Perm (Fin n)))
    (hn : Normalizes B A) (Y : Multiset Ω)
    (hy : ∀ g ∈ B, Conf A Y (Y ↼ g)) :
    B →* Equiv.Perm {Z // Conf A Y Z} where
  toFun g :=
    { toFun := fun Z => ⟨Z.val ↼ g.val⁻¹,
        (affine_law hn (B.inv_mem g.property) (hy _ (B.inv_mem g.property)) Z.property).2.2⟩
      invFun := fun Z => ⟨Z.val ↼ g.val,
        (affine_law hn g.property (hy _ g.property) Z.property).2.2⟩
      left_inv := fun Z => Subtype.ext (by simp)
      right_inv := fun Z => Subtype.ext (by simp) }
  map_one' := by ext Z; simp
  map_mul' g h := by
    ext Z
    change Z.val ↼ (g.val * h.val)⁻¹ = (Z.val ↼ h.val⁻¹) ↼ g.val⁻¹
    rw [mul_inv_rev, act_act]

noncomputable def linObjectFiniteConfigAction (B A : Subgroup (Equiv.Perm (Fin n)))
    (hn : Normalizes B A) (Y : Multiset Ω) (hy : ∀ g ∈ B, Conf A Y (Y ↼ g))
    (π : A →* Q) (hπ : Function.Surjective π)
    (hker : ∀ T ∈ pieces A Y, π.ker ≤ (Aut A T).subgroupOf A) :
    B →* Equiv.Perm (∀ T : {T // T ∈ pieces A Y},
      Additive Q ⧸ linObjectGroupImage A π (Aut A T.val)) :=
  (linObjectConfigEquiv A π hπ Y hker).permCongrHom.toMonoidHom.comp (linObjectConfigAction B A hn Y hy)

end GI.Impl
