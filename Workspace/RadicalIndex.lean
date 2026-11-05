module

public import Workspace.RadicalFreeOrder
public import Workspace.MulticosetRadical

@[expose] public section

/-!
# The radical index bound of Corollary A.22

For `N ◁ H ≤ Sym(B)` with `N` transitive, `Q = H/N` and `R` the full preimage of `Rad(Q)`:
`[H : R] = |Q/Rad(Q)| ≤ b(Q)² ≤ b^{2 log₂ b}`, by Lemma A.21 and [GMP, Theorem 1.4].
This is the hypothesis `hidx` of `GI.Paper.cor_transitive_kernel_multicoset` and
`GI.Paper.thm_transitive_gat_terminal`.
-/

namespace GI.RadicalIndex

open GI.Cited GI.Composition GI.Multicoset

universe u

variable {B : Type u} [Fintype B]

/-- `[H : R] = |Q/Rad(Q)|`. -/
theorem index_radicalPreimage {H N : Subgroup (Equiv.Perm B)} [(N.subgroupOf H).Normal] :
    ((radicalPreimage H N).subgroupOf H).index =
      Nat.card ((H ⧸ N.subgroupOf H) ⧸
        GI.RadicalSocle.solvableRadical (H ⧸ N.subgroupOf H)) := by
  rw [radicalPreimage, dif_pos (inferInstance : (N.subgroupOf H).Normal)]
  have h : (((GI.RadicalSocle.solvableRadical (H ⧸ N.subgroupOf H)).comap
      (QuotientGroup.mk' (N.subgroupOf H))).map H.subtype).subgroupOf H =
      (GI.RadicalSocle.solvableRadical (H ⧸ N.subgroupOf H)).comap
        (QuotientGroup.mk' (N.subgroupOf H)) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [h, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rfl

/-- [GMP, Theorem 1.4] for subgroups of `Sym(B)`, `B` in any universe. -/
theorem transitiveNonabelian_univ (hTr : GMPTransitiveNonabelian)
    {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H) [(N.subgroupOf H).Normal]
    (htr : MulAction.IsPretransitive N B) (hB : 1 ≤ Fintype.card B) :
    (bFac (H ⧸ N.subgroupOf H) : ℝ) ≤
      (Fintype.card B : ℝ) ^ Real.logb 2 (Fintype.card B) := by
  let e : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  let φ : Equiv.Perm B ≃* Equiv.Perm (Fin (Fintype.card B)) := e.permCongrHom
  let H' := H.map φ.toMonoidHom
  let N' := N.map φ.toMonoidHom
  have hN'H' : N' ≤ H' := Subgroup.map_mono hNH
  have hn := normalizes_of_normal hNH
  have hn' : Normalizes H' N' := by
    rintro _ ⟨h, hh, rfl⟩ _ ⟨n, hnN, rfl⟩
    refine ⟨h * n * h⁻¹, hn h hh n hnN, ?_⟩
    simp
  haveI := normal_of_normalizes hn'
  have htr' : MulAction.IsPretransitive N' (Fin (Fintype.card B)) := by
    refine ⟨fun i j => ?_⟩
    obtain ⟨g, hg⟩ := htr.exists_smul_eq (e.symm i) (e.symm j)
    refine ⟨⟨φ g, g, g.2, rfl⟩, ?_⟩
    have hg' : g.1 (e.symm i) = e.symm j := hg
    show (φ g.1) i = j
    simp [φ, Equiv.permCongrHom_coe, Equiv.permCongr_apply, hg']
  let q : (H ⧸ N.subgroupOf H) ≃* (H' ⧸ N'.subgroupOf H') :=
    QuotientGroup.congr (N.subgroupOf H) (N'.subgroupOf H') (φ.subgroupMap H) (by
      ext ⟨x, hx⟩
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨y, hy, hyx⟩
        refine ⟨y, hy, ?_⟩
        have := congrArg Subtype.val hyx
        exact this
      · rintro ⟨n, hnN, hnx⟩
        obtain ⟨h, hh, rfl⟩ := hx
        have hnh : n = h := φ.injective hnx
        subst hnh
        exact ⟨⟨n, hh⟩, hnN, rfl⟩)
  have hc : CompositionProducts (H' ⧸ N'.subgroupOf H') (aFac (H ⧸ N.subgroupOf H))
      (bFac (H ⧸ N.subgroupOf H)) := congr (spec _) q
  have h := hTr (Fintype.card B) hB H' N' hN'H' htr' _ _ hc
  exact_mod_cast h

/-- **The first displayed step of the proof of Corollary A.22 for any subgroup `R'` with
`[H : R'] ≤ b(H/N)²`:** `[H : R'] ≤ b(Q)² ≤ b^{2 log₂ b}` for `N ◁ H ≤ Sym(B)` with `N`
transitive. -/
theorem sub_index_chain (hTr : GMPTransitiveNonabelian)
    {H N R' : Subgroup (Equiv.Perm B)} (hNH : N ≤ H) [(N.subgroupOf H).Normal]
    (htr : MulAction.IsPretransitive N B)
    (hR' : (R'.subgroupOf H).index ≤ bFac (H ⧸ N.subgroupOf H) ^ 2) :
    (R'.subgroupOf H).index ≤ bFac (H ⧸ N.subgroupOf H) ^ 2 ∧
    ((bFac (H ⧸ N.subgroupOf H) ^ 2 : ℕ) : ℝ) ≤
      (Fintype.card B : ℝ) ^ (2 * Real.logb 2 (Fintype.card B)) := by
  refine ⟨hR', ?_⟩
  rcases Nat.eq_zero_or_pos (Fintype.card B) with h0 | hB
  · -- `B` is empty: everything is trivial and both sides are `1`
    haveI : IsEmpty B := Fintype.card_eq_zero_iff.mp h0
    haveI : Subsingleton (H ⧸ N.subgroupOf H) := by
      refine ⟨fun x y => ?_⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ y
      congr 1
      exact Subsingleton.elim x y
    have hb : bFac (H ⧸ N.subgroupOf H) = 1 := by
      have h := aFac_mul_bFac (X := H ⧸ N.subgroupOf H)
      rw [Nat.card_unique] at h
      exact Nat.eq_one_of_mul_eq_one_left h
    rw [hb, h0]
    simp
  · have h := transitiveNonabelian_univ hTr hNH htr hB
    have hb0 : (0 : ℝ) ≤ Fintype.card B := Nat.cast_nonneg _
    calc ((bFac (H ⧸ N.subgroupOf H) ^ 2 : ℕ) : ℝ)
        = (bFac (H ⧸ N.subgroupOf H) : ℝ) ^ 2 := by push_cast; rfl
      _ ≤ ((Fintype.card B : ℝ) ^ Real.logb 2 (Fintype.card B)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
      _ = (Fintype.card B : ℝ) ^ (2 * Real.logb 2 (Fintype.card B)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hb0]
        congr 1
        push_cast
        ring

/-- For any subgroup `R'` with `[H : R'] ≤ b(H/N)²`, we have `[H : R'] ≤ b^{2 log₂ b}`. -/
theorem sub_index_le (hTr : GMPTransitiveNonabelian)
    {H N R' : Subgroup (Equiv.Perm B)} (hNH : N ≤ H) [(N.subgroupOf H).Normal]
    (htr : MulAction.IsPretransitive N B)
    (hR' : (R'.subgroupOf H).index ≤ bFac (H ⧸ N.subgroupOf H) ^ 2) :
    ((R'.subgroupOf H).index : ℝ) ≤
      (Fintype.card B : ℝ) ^ (2 * Real.logb 2 (Fintype.card B)) := by
  obtain ⟨h1, h2⟩ := sub_index_chain hTr hNH htr hR'
  exact (Nat.cast_le.mpr h1).trans h2

/-- **The first displayed step of the proof of Corollary A.22:**
`[H : R'] ≤ b(Q)² ≤ b^{2 log₂ b}` for `N ◁ H ≤ Sym(B)` with `N` transitive and
`R' = radicalSubgroup H N`. -/
theorem radical_index_chain (hTr : GMPTransitiveNonabelian)
    {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H) [(N.subgroupOf H).Normal]
    (htr : MulAction.IsPretransitive N B) :
    ((radicalSubgroup H N).subgroupOf H).index ≤ bFac (H ⧸ N.subgroupOf H) ^ 2 ∧
    ((bFac (H ⧸ N.subgroupOf H) ^ 2 : ℕ) : ℝ) ≤
      (Fintype.card B : ℝ) ^ (2 * Real.logb 2 (Fintype.card B)) :=
  sub_index_chain hTr hNH htr (GI.RadicalFreeOrder.radicalSubgroup_index_le hNH)

/-- The index bound in the form of the hypothesis `hidx` of
`GI.Paper.cor_transitive_kernel_multicoset` and `GI.Paper.thm_transitive_gat_terminal`. -/
theorem radical_index_le (hTr : GMPTransitiveNonabelian)
    {H N : Subgroup (Equiv.Perm B)} (hNH : N ≤ H) [(N.subgroupOf H).Normal]
    (htr : MulAction.IsPretransitive N B) :
    (((radicalSubgroup H N).subgroupOf H).index : ℝ) ≤
      (Fintype.card B : ℝ) ^ (2 * Real.logb 2 (Fintype.card B)) :=
  sub_index_le hTr hNH htr (GI.RadicalFreeOrder.radicalSubgroup_index_le hNH)

end GI.RadicalIndex
