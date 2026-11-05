module

public import Workspace.Impl.GMPCosetIndex
public import Workspace.Proved.GMPLuksAction

@[expose] public section

/-! # The permutation action on an enumerated list of right cosets -/

namespace GI.Proved

open GI.Impl

variable {G K : Type*} [Group G] [Group K] {U V : Subgroup G}
  {rs : List G}

/-- Right cosets are represented by inverse left cosets, as in the closure loop. -/
noncomputable def gmpRepsQuotientEquiv (hrs : GmpCosetReps U V rs) :
    Fin rs.length ≃ U ⧸ V.subgroupOf U := by
  let f : Fin rs.length → U ⧸ V.subgroupOf U := fun i => tmRpQ U V (rs.get i)
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    have hd := tmRpQuot_nodup hrs.sub hrs.distinct
    have hi : i.val < (rs.map (tmRpQ U V)).length := by simpa using i.isLt
    have hj : j.val < (rs.map (tmRpQ U V)).length := by simpa using j.isLt
    apply Fin.ext
    apply (hd.getElem_inj (hi := hi) (hj := hj)).mp
    simpa only [f, List.getElem_map, List.get_eq_getElem] using hij
  · intro q
    induction q using QuotientGroup.induction_on with
    | H z =>
      obtain ⟨r, hr, v, hv, he⟩ := hrs.cover (z⁻¹).val (z⁻¹).property
      obtain ⟨i, hi, hri⟩ := List.mem_iff_getElem.mp hr
      refine ⟨⟨i, hi⟩, ?_⟩
      have hmem : r * z.val ∈ V := by
        have hv' := V.inv_mem hv
        have hz : z.val = r⁻¹ * v⁻¹ := by
          have h := congrArg Inv.inv he
          simpa only [Subgroup.coe_inv, inv_inv, mul_inv_rev] using h
        rw [hz, ← mul_assoc, mul_inv_cancel, one_mul]
        exact hv'
      change tmRpQ U V rs[i] = (z : U ⧸ V.subgroupOf U)
      rw [hri]
      unfold tmRpQ
      rw [dif_pos (hrs.sub r hr)]
      change (QuotientGroup.mk (⟨r, hrs.sub r hr⟩ : U)⁻¹ : U ⧸ V.subgroupOf U) = _
      simpa only [inv_inv] using
        (tmRp_mk_eq_iff ⟨r, hrs.sub r hr⟩ z⁻¹).mpr (by simpa using hmem)

theorem gmpRepsQuotientEquiv_apply (hrs : GmpCosetReps U V rs) (i : Fin rs.length) :
    gmpRepsQuotientEquiv hrs i =
      (QuotientGroup.mk (⟨(rs.get i), hrs.sub _ (List.get_mem rs i)⟩ : U)⁻¹ : U ⧸ V.subgroupOf U) := by
  change tmRpQ U V (rs.get i) = _
  unfold tmRpQ
  rw [dif_pos (hrs.sub _ (List.get_mem rs i))]
  rfl

/-- Any automorphism action preserving the coset subgroup becomes an
actual permutation action on the enumerated labels. -/
noncomputable def gmpRepsAutAction (hrs : GmpCosetReps U V rs) (φ : K →* MulAut U)
    (hφ : ∀ k, V.subgroupOf U ≤ (V.subgroupOf U).comap (φ k).toMonoidHom) :
    K →* Equiv.Perm (Fin rs.length) :=
  (gmpRepsQuotientEquiv hrs).symm.permCongrHom.toMonoidHom.comp
    (gmpAutCosetAction (V.subgroupOf U) φ hφ)

/-- The label action agrees with precisely the coset-membership tests
performed by the action-table program. -/
theorem gmpRepsAutAction_apply_iff (hrs : GmpCosetReps U V rs) (φ : K →* MulAut U)
    (hφ : ∀ k, V.subgroupOf U ≤ (V.subgroupOf U).comap (φ k).toMonoidHom)
    (k : K) (i j : Fin rs.length) :
    gmpRepsAutAction hrs φ hφ k i = j ↔
      ((φ k) ⟨(rs.get i), hrs.sub _ (List.get_mem rs i)⟩ : G) * (rs.get j)⁻¹ ∈ V := by
  let e := gmpRepsQuotientEquiv hrs
  have he : e (gmpRepsAutAction hrs φ hφ k i) =
      gmpAutCosetAction (V.subgroupOf U) φ hφ k (e i) := by
    change e (e.symm (gmpAutCosetAction (V.subgroupOf U) φ hφ k (e i))) = _
    exact e.apply_symm_apply _
  have hright := tmRp_mk_eq_iff (R := V)
    ((φ k) ⟨(rs.get i), hrs.sub _ (List.get_mem rs i)⟩)
    (⟨(rs.get j), hrs.sub _ (List.get_mem rs j)⟩ : U)
  constructor
  · intro hij
    rw [hij] at he
    dsimp only [e] at he
    rw [gmpRepsQuotientEquiv_apply, gmpRepsQuotientEquiv_apply] at he
    apply hright.mp
    symm at he
    change (QuotientGroup.mk ((φ k) _) : U ⧸ V.subgroupOf U) = _ at he
    rw [map_inv] at he
    exact he
  · intro hmem
    apply e.injective
    rw [he]
    dsimp only [e]
    rw [gmpRepsQuotientEquiv_apply, gmpRepsQuotientEquiv_apply]
    change (QuotientGroup.mk ((φ k) _) : U ⧸ V.subgroupOf U) = _
    rw [map_inv]
    exact hright.mpr hmem

end GI.Proved
