module

public import Workspace.CompositionFactors
public import Workspace.SmallSimple
public import Workspace.SocleOuter
public import Workspace.RadicalSocleDecomposition
public import Workspace.Schreier
public import Workspace.Proved.SolvGMP
public import Workspace.MulticosetRadical

@[expose] public section

/-!
# Lemma A.21 (`lem:radical-free-order`): solvable-quotient subgroup of index at most `b(Q)²`

For `N ◁ H` in a finite group `G`, let `R = radicalPreimage H N`, `E_H = soclePreimage H R`,
and `K*_H = radicalPreimage H E_H`. For the radical-free quotient `Q₀ = H/R` with socle
`E = E_H/R = T₁ × ⋯ × T_t`:

* `Q₀` acts faithfully on `E` by conjugation (`C_{Q₀}(E) = 1`);
* the action on the simple factors has image `P ≤ Sym(t)`, with kernel `K`;
* `K` maps to `∏ Out(T_i)` with kernel `E`, so `K/E` is solvable by Schreier's conjecture
  (`GI.schreier`) and `K/E ≤ Rad(Q₀/E)`;
* [GMP, Proposition 6.1] (`GI.Proved.gmpAbelianFactors`) and `|T_i| ≥ 34`
  (`GI.SmallSimple.thirtyfour_le_card`) give `a(P) ≤ |E|`, so `[H : K*_H] ≤ |P| ≤ b(H/N)` and
  `[E_H : R] = |E| ≤ b(H/N)`;
* for any solvable supplement `S₁ ≤ K*_H` of `E_H` in `K*_H` (or any `R ≤ R' ≤ K*_H` with
  `R'/R` solvable and `R' E_H = K*_H`), `R'/N` is solvable and `[H : R'] ≤ b(H/N)²`.
-/

namespace GI.RadicalFreeOrder

open GI.Cited GI.Composition GI.RadicalSocle GI.SocleOuter

universe u

/-! ### Moving [GMP, Proposition 6.1] to any universe -/

/-- [GMP, Proposition 6.1] for a permutation group on any finite type with `t ≥ 1` points. -/
theorem abelianFactors_univ (hAb : GMPAbelianFactors) {α : Type u} [Finite α]
    (ht : 1 ≤ Nat.card α) (P : Subgroup (Equiv.Perm α)) :
    (aFac P : ℝ) ≤ (24 : ℝ) ^ (((Nat.card α : ℝ) - 1) / 3) := by
  let e : α ≃ Fin (Nat.card α) := Finite.equivFin α
  let φ := e.permCongrHom
  let P' := P.map φ.toMonoidHom
  have h : CompositionProducts P' (aFac P) (bFac P) := congr (spec P) (φ.subgroupMap P)
  exact hAb _ ht P' _ _ h

/-! ### The structure of a radical-free group -/

section Structure

variable {G : Type u} [Group G] [Finite G]
  (rf : ∀ N : Subgroup G, N.Normal → IsSolvable N → N = ⊥)

/-- The socle `E` as a group. -/
local notation "E" => socle G

omit [Finite G] in
/-- Conjugation by an element of `E` is the inner automorphism of `E`. -/
theorem socleConjugation_of_mem (ε : E) :
    socleConjugation (G := G) (ε : G) = MulAut.conj ε :=
  MulAut.conjNormal_val

omit [Finite G] in
/-- An inner automorphism of `E` fixes every minimal normal subgroup of `E`. -/
theorem minimalNormalAction_conj (ε : E) : minimalNormalAction (MulAut.conj ε) = 1 := by
  ext N : 1
  apply Subtype.ext
  change N.val.map (MulAut.conj ε).toMonoidHom = N.val
  haveI : N.val.Normal := N.property.1
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (inferInstance : N.val.Normal).conj_mem x hx ε
  · intro x hx
    refine ⟨ε⁻¹ * x * ε, ?_, ?_⟩
    · simpa using (inferInstance : N.val.Normal).conj_mem x hx ε⁻¹
    · simp [MulAut.conj_apply, mul_assoc]

/-- The action of `G` on the simple factors of its socle. -/
noncomputable def factorAction : G →* Equiv.Perm (MinimalNormals E) :=
  minimalNormalAction.comp socleConjugation

omit [Finite G] in
theorem socle_le_factorAction_ker : E ≤ (factorAction (G := G)).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  change minimalNormalAction (socleConjugation x) = 1
  rw [socleConjugation_of_mem ⟨x, hx⟩]
  exact minimalNormalAction_conj _

/-- The kernel of the factor action acts on `E` fixing every factor. -/
noncomputable def kernelToFactorKernel :
    (factorAction (G := G)).ker →* FactorKernel E :=
  ((socleConjugation (G := G)).comp (factorAction (G := G)).ker.subtype).codRestrict _
    (fun k => k.2)

/-- The map from the kernel `K` of the factor action to `∏ Out(T_i)`. -/
noncomputable def kernelToOuter :
    (factorAction (G := G)).ker →* ∀ N : MinimalNormals E, OuterAut N.val :=
  (factorOuterHom (G := E)).comp kernelToFactorKernel

/-- The inclusion of `E` into the kernel `K`. -/
noncomputable def socleToKernel : E →* (factorAction (G := G)).ker :=
  Subgroup.inclusion socle_le_factorAction_ker

include rf in
/-- The kernel of `K → ∏ Out(T_i)` is exactly `E`. -/
theorem kernelToOuter_ker : (kernelToOuter (G := G)).ker = (socleToKernel (G := G)).range := by
  have rfE := normal_subgroup_radicalFree rf (socle G)
  have hsoc : socle (socle G) = ⊤ := socle_idempotent
  ext k
  rw [MonoidHom.mem_ker]
  change (factorOuterHom (G := E)) (kernelToFactorKernel k) = 1 ↔ _
  rw [← MonoidHom.mem_ker, factorOuterHom_ker_eq_inner_comap rfE hsoc, Subgroup.mem_comap]
  change socleConjugation (k : G) ∈ innerAut E ↔ _
  constructor
  · rintro ⟨ε, hε⟩
    refine ⟨ε, Subtype.ext ?_⟩
    change (ε : G) = k
    apply socleConjugation_injective rf
    rw [socleConjugation_of_mem, hε]
  · rintro ⟨ε, rfl⟩
    exact ⟨ε, (socleConjugation_of_mem ε).symm⟩

include rf in
theorem nonabelian_factor (N : MinimalNormals E) : ¬ ∀ x y : N.val, x * y = y * x := by
  obtain ⟨x, y, h⟩ := socle_intrinsic_factor_nonabelian rf N
  exact fun hc => h (hc x y)

include rf in
/-- `E` has no abelian composition factor and `b(E) = |E|`. -/
theorem socle_compositionProducts : CompositionProducts E 1 (Nat.card E) := by
  letI := Fintype.ofFinite (MinimalNormals E)
  haveI := fun N : MinimalNormals E => socle_intrinsic_factor_simple N
  have h := pi_compositionProducts (MinimalNormals E) (fun N => N.val)
  have ha : ∏ N : MinimalNormals E, aFac N.val = 1 :=
    Finset.prod_eq_one (fun N _ => aFac_of_simple (nonabelian_factor rf N))
  have hb : ∏ N : MinimalNormals E, bFac N.val = Nat.card E := by
    rw [← Nat.card_congr (socleIntrinsicProductEquiv rf).toEquiv, Nat.card_pi]
    exact Finset.prod_congr rfl (fun N _ => bFac_of_simple (nonabelian_factor rf N))
  rw [ha, hb] at h
  exact congr h (socleIntrinsicProductEquiv rf)

include rf in
theorem aFac_socle : aFac E = 1 := aFac_eq (socle_compositionProducts rf)

include rf in
theorem bFac_socle : bFac E = Nat.card E := bFac_eq (socle_compositionProducts rf)

include rf in
/-- `|E| ≤ b(G)`. -/
theorem card_socle_le_bFac : Nat.card E ≤ bFac G := by
  rw [bFac_mul E, bFac_socle rf]
  exact Nat.le_mul_of_pos_right _ bFac_pos

theorem nontrivial_factors [Nontrivial G] : 1 ≤ Nat.card (MinimalNormals E) := by
  obtain ⟨M, hM, -⟩ := exists_minimal_normal_le (⊤ : Subgroup G) top_ne_bot
  have hE : socle G ≠ ⊥ := fun h => hM.2.1 (le_bot_iff.mp (h ▸ minimalNormal_le_socle hM))
  haveI : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot _).mpr hE
  obtain ⟨N, hN, -⟩ := exists_minimal_normal_le (⊤ : Subgroup E) top_ne_bot
  haveI : Nonempty (MinimalNormals E) := ⟨⟨N, hN⟩⟩
  exact Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'

/-- A finite direct product of solvable groups is solvable. -/
theorem pi_isSolvable {I : Type*} [Finite I] {D : I → Type*} [∀ i, Group (D i)]
    (hs : ∀ i, Group.IsSolvable (D i)) : Group.IsSolvable (∀ i, D i) := by
  classical
  letI := Fintype.ofFinite I
  choose n hn using fun i => (hs i).solvable
  refine ⟨⟨∑ i : I, n i, eq_bot_iff.mpr ?_⟩⟩
  intro x hx
  ext i
  have hle : n i ≤ ∑ j : I, n j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have h1 : Pi.evalMonoidHom D i x ∈
      (derivedSeries (∀ j, D j) (∑ j : I, n j)).map (Pi.evalMonoidHom D i) := ⟨x, hx, rfl⟩
  have h2 := (map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom D i) (∑ j : I, n j)).trans
    (derivedSeries_antitone (D i) hle)
  rw [hn i] at h2
  exact h2 h1

include rf in
/-- By Schreier's conjecture (`GI.schreier`), `∏ Out(T_i)` is solvable. -/
theorem outer_product_solvable :
    Group.IsSolvable (∀ N : MinimalNormals E, OuterAut N.val) := by
  have := fun N : MinimalNormals E => socle_intrinsic_factor_simple N
  exact pi_isSolvable fun N => GI.schreier N.val (socle_intrinsic_factor_nonabelian rf N)

include rf in
/-- The image `K/E` of the factor-action kernel `K` in `G/E` embeds into `∏ Out(T_i)`,
so it is solvable by Schreier's conjecture. -/
theorem factorAction_ker_quotient_solvable :
    Group.IsSolvable (((factorAction (G := G)).ker).map (QuotientGroup.mk' E)) := by
  set q := QuotientGroup.mk' E
  set K := (factorAction (G := G)).ker
  obtain ⟨n, hn⟩ := (outer_product_solvable rf).solvable
  refine ⟨⟨n, eq_bot_iff.mpr ?_⟩⟩
  rw [← map_derivedSeries_eq (q.subgroupMap_surjective K) n]
  rintro _ ⟨x, hx, rfl⟩
  apply Subtype.ext
  exact (QuotientGroup.eq_one_iff (x : G)).mpr (by
    have h1 : kernelToOuter (G := G) x ∈
        (derivedSeries K n).map (kernelToOuter (G := G)) := ⟨x, hx, rfl⟩
    have h2 := map_derivedSeries_le_derivedSeries (kernelToOuter (G := G)) n
    rw [hn, le_bot_iff] at h2
    have hker : x ∈ (kernelToOuter (G := G)).ker := by
      rw [MonoidHom.mem_ker, ← Subgroup.mem_bot, ← h2]
      exact h1
    rw [kernelToOuter_ker rf] at hker
    obtain ⟨ε, rfl⟩ := hker
    exact ε.2)

include rf in
/-- Because `K ◁ G` and `K/E` is solvable, `K/E ≤ Rad(G/E)`. -/
theorem factorAction_ker_le_radical :
    ((factorAction (G := G)).ker).map (QuotientGroup.mk' E) ≤ solvableRadical (G ⧸ E) := by
  have : (((factorAction (G := G)).ker).map (QuotientGroup.mk' E)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective E)
  have : Group.IsSolvable (((factorAction (G := G)).ker).map (QuotientGroup.mk' E)) :=
    factorAction_ker_quotient_solvable rf
  exact le_solvableRadical _

include rf in
/-- Since `K/E ≤ Rad(G/E)`, we have `[G/E : Rad(G/E)] ≤ [G : K] = |P|`. -/
theorem index_radical_quotient_socle_le_factorAction :
    (solvableRadical (G ⧸ E)).index ≤ Nat.card (factorAction (G := G)).range := by
  set q := QuotientGroup.mk' E
  set K := (factorAction (G := G)).ker
  have hle := factorAction_ker_le_radical rf
  have hmul := Subgroup.relIndex_mul_index hle
  have hpos : 0 < (K.map q).relIndex (solvableRadical (G ⧸ E)) := Nat.card_pos
  have h1 : (solvableRadical (G ⧸ E)).index ≤ (K.map q).index := by
    rw [← hmul]
    exact Nat.le_mul_of_pos_left _ hpos
  have h2 : (K.map q).index = K.index := by
    rw [← Subgroup.index_comap_of_surjective (K.map q) (QuotientGroup.mk'_surjective E),
      Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr socle_le_factorAction_ker]
  have h3 : K.index = Nat.card (factorAction (G := G)).range := by
    rw [Subgroup.index]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (factorAction (G := G))).toEquiv
  omega

include rf in
/-- **`a(P) ≤ |E|`**: by [GMP, Proposition 6.1] (`GI.Proved.gmpAbelianFactors`),
`a(P) ≤ 24^{(t-1)/3} ≤ 34^t ≤ ∏ |T_i| = |E|`. -/
theorem aFac_factorAction_le_card_socle :
    aFac (factorAction (G := G)).range ≤ Nat.card E := by
  by_cases hG : Subsingleton G
  · have := hG
    have h1 : aFac (factorAction (G := G)).range ≤ Nat.card (factorAction (G := G)).range :=
      aFac_le_card
    rw [Nat.card_unique] at h1
    exact h1.trans (Nat.one_le_iff_ne_zero.mpr (Nat.card_pos (α := E)).ne')
  rw [not_subsingleton_iff_nontrivial] at hG
  letI := Fintype.ofFinite (MinimalNormals E)
  have := fun N : MinimalNormals E => socle_intrinsic_factor_simple N
  have ht := nontrivial_factors (G := G)
  set t := Nat.card (MinimalNormals E)
  have hP := abelianFactors_univ GI.Proved.gmpAbelianFactors ht (factorAction (G := G)).range
  have h34 : ∀ N : MinimalNormals E, (34 : ℝ) ≤ Nat.card N.val := by
    intro N
    exact_mod_cast GI.SmallSimple.thirtyfour_le_card (nonabelian_factor rf N)
  have hpow : (24 : ℝ) ^ (((t : ℝ) - 1) / 3) ≤ (34 : ℝ) ^ t := by
    calc (24 : ℝ) ^ (((t : ℝ) - 1) / 3)
        ≤ (24 : ℝ) ^ (t : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          have : (1 : ℝ) ≤ t := by exact_mod_cast ht
          linarith
      _ = (24 : ℝ) ^ t := Real.rpow_natCast 24 t
      _ ≤ (34 : ℝ) ^ t := pow_le_pow_left₀ (by norm_num) (by norm_num) t
  have hE : (Nat.card E : ℝ) = ∏ N : MinimalNormals E, (Nat.card N.val : ℝ) := by
    rw [← Nat.card_congr (socleIntrinsicProductEquiv rf).toEquiv, Nat.card_pi]
    push_cast
    rfl
  have hmain : (aFac (factorAction (G := G)).range : ℝ) ≤ Nat.card E := by
    calc (aFac (factorAction (G := G)).range : ℝ)
        ≤ (34 : ℝ) ^ t := hP.trans hpow
      _ = ∏ _ : MinimalNormals E, (34 : ℝ) := by
          rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
      _ ≤ ∏ N : MinimalNormals E, (Nat.card N.val : ℝ) :=
          Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun N _ => h34 N)
      _ = Nat.card E := hE.symm
  exact_mod_cast hmain

include rf in
/-- **`|P| ≤ b(G)`**: `|P| = a(P) b(P) ≤ |E| b(P) ≤ b(K) b(P) = b(G)`. -/
theorem card_factorAction_le_bFac :
    Nat.card (factorAction (G := G)).range ≤ bFac G := by
  set P := (factorAction (G := G)).range
  set K := (factorAction (G := G)).ker
  have h1 : Nat.card P = aFac P * bFac P := (aFac_mul_bFac (X := P)).symm
  have h2 : aFac P ≤ Nat.card E := aFac_factorAction_le_card_socle rf
  have h3 : Nat.card E ≤ bFac K := by
    rw [bFac_ker_range (kernelToOuter (G := G)),
      bFac_congr (MulEquiv.subgroupCongr (kernelToOuter_ker rf)),
      ← bFac_congr (MonoidHom.ofInjective (f := socleToKernel (G := G))
        (Subgroup.inclusion_injective _)), bFac_socle rf]
    exact Nat.le_mul_of_pos_right _ bFac_pos
  rw [h1, bFac_ker_range (factorAction (G := G))]
  exact Nat.mul_le_mul_right _ (h2.trans h3)

include rf in
/-- **`[G/E : Rad(G/E)] ≤ b(G)`** for a radical-free finite group `G`. -/
theorem index_radical_quotient_socle_le :
    (solvableRadical (G ⧸ E)).index ≤ bFac G :=
  (index_radical_quotient_socle_le_factorAction rf).trans (card_factorAction_le_bFac rf)

end Structure

/-! ### Lemma A.21′: solvable-quotient subgroup of index at most `b(Q)²` -/

export GI.Multicoset (
  soclePreimage
  radicalPreimage_le
  le_radicalPreimage
  radicalPreimage_subgroupOf
  normal_radicalPreimage
  normalizes_radicalPreimage
  soclePreimage_le
  le_soclePreimage
  soclePreimage_subgroupOf
  normal_soclePreimage
  normalizes_soclePreimage
  relDerived_mono_kernel
  relDerived_add_le
  relDerived_trans
  sup_quotient_solvable
  exists_solvable_supplement_radicalOuter
  radicalSubgroup
  radicalSubgroup_spec
)

section SolvablePreimage

open Classical GI.Multicoset

variable {G : Type u} [Group G]

/-- In a finite group, `H.relIndex N * (H ⊔ N).index = H.index` when `N` is normal. -/
theorem relIndex_mul_index_sup [Finite G] (H N : Subgroup G) [N.Normal] :
    H.relIndex N * (H ⊔ N).index = H.index := by
  have hpos : 0 < N.relIndex H := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc
    (H.relIndex N * (H ⊔ N).index) * N.relIndex H =
        H.relIndex N * (N.relIndex (H ⊔ N) * (H ⊔ N).index) := by
      rw [Subgroup.relIndex_sup_right]
      ac_rfl
    _ = H.relIndex N * N.index := by rw [Subgroup.relIndex_mul_index le_sup_right]
    _ = (H ⊓ N).index := by
      rw [← Subgroup.inf_relIndex_right H N]
      exact Subgroup.relIndex_mul_index inf_le_right
    _ = N.relIndex H * H.index := by
      rw [← Subgroup.inf_relIndex_left H N]
      exact (Subgroup.relIndex_mul_index inf_le_left).symm
    _ = H.index * N.relIndex H := Nat.mul_comm _ _

/-- For any subgroup `S`, `(⊥ : Subgroup G).relIndex S = Nat.card S`. -/
theorem bot_relIndex_eq_card (S : Subgroup G) : (⊥ : Subgroup G).relIndex S = Nat.card S := by
  rw [Subgroup.relIndex, Subgroup.index]
  have hbot : (⊥ : Subgroup G).subgroupOf S = ⊥ := by
    ext x
    simp
  rw [hbot]
  exact Nat.card_congr (QuotientGroup.quotientBot (G := S)).toEquiv

/-- The index of the solvable radical is preserved under group isomorphism. -/
theorem solvableRadical_index_congr {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) : (solvableRadical A).index = (solvableRadical B).index := by
  have h : solvableRadical A = (solvableRadical B).comap e.toMonoidHom := by
    apply le_antisymm
    · rw [← Subgroup.map_le_iff_le_comap]
      have : ((solvableRadical A).map e.toMonoidHom).Normal :=
        Subgroup.Normal.map inferInstance _ e.surjective
      have : Group.IsSolvable ((solvableRadical A).map e.toMonoidHom) :=
        Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _)
      exact le_solvableRadical _
    · have : ((solvableRadical B).comap e.toMonoidHom).Normal :=
        Subgroup.Normal.comap inferInstance e.toMonoidHom
      have heq : (solvableRadical B).comap e.toMonoidHom =
          (solvableRadical B).map e.symm.toMonoidHom := by
        ext x
        simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
        exact ⟨fun hx => ⟨e x, hx, e.symm_apply_apply x⟩,
          fun ⟨y, hy, hyx⟩ => by rw [← hyx, e.apply_symm_apply]; exact hy⟩
      have : Group.IsSolvable ((solvableRadical B).comap e.toMonoidHom) := by
        rw [heq]
        exact Group.isSolvable_of_surjective (e.symm.toMonoidHom.subgroupMap_surjective _)
      exact le_solvableRadical _
  rw [h, Subgroup.index_comap_of_surjective _ e.surjective]

/-- Third isomorphism theorem for a preimage `K` in `H` of `P ≤ H/M`. -/
noncomputable def quotientPreimageEquiv {H M K : Subgroup G} [(M.subgroupOf H).Normal]
    [(K.subgroupOf H).Normal] (P : Subgroup (H ⧸ M.subgroupOf H)) [P.Normal]
    (hK : K.subgroupOf H = P.comap (QuotientGroup.mk' (M.subgroupOf H))) :
    (H ⧸ K.subgroupOf H) ≃* ((H ⧸ M.subgroupOf H) ⧸ P) := by
  let f : H →* (H ⧸ M.subgroupOf H) ⧸ P :=
    (QuotientGroup.mk' P).comp (QuotientGroup.mk' (M.subgroupOf H))
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective P).comp (QuotientGroup.mk'_surjective (M.subgroupOf H))
  have hker : K.subgroupOf H = f.ker := by
    ext x
    rw [hK, Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact (QuotientGroup.eq_one_iff _).symm
  exact (QuotientGroup.congr (K.subgroupOf H) f.ker (MulEquiv.refl H)
    (by ext x; simp [hker])).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)

/-- `H/R ≅ (H/N) / Rad(H/N)` is radical-free. -/
theorem radicalPreimage_quotient_radicalFree [Finite G] {H N : Subgroup G}
    [(N.subgroupOf H).Normal] :
    ∀ M : Subgroup (H ⧸ (radicalPreimage H N).subgroupOf H),
      M.Normal → Group.IsSolvable M → M = ⊥ := by
  intro M hM hsolv
  let e := quotientPreimageEquiv (solvableRadical (H ⧸ N.subgroupOf H))
    (radicalPreimage_subgroupOf (H := H) (N := N))
  have hM' : (M.map e.toMonoidHom).Normal := Subgroup.Normal.map hM _ e.surjective
  have hs' : Group.IsSolvable (M.map e.toMonoidHom) :=
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective M)
  have hbot := radical_quotient_radicalFree (M.map e.toMonoidHom) hM' hs'
  rw [eq_bot_iff] at hbot ⊢
  intro x hx
  have hx' : e x ∈ M.map e.toMonoidHom := ⟨x, hx, rfl⟩
  rw [Subgroup.mem_bot] at *
  exact (MulEquiv.map_eq_one_iff e).mp (hbot hx')

/-- `b(H/R) = b(H/N)`. -/
theorem bFac_quotient_radicalPreimage [Finite G] {H N : Subgroup G} [(N.subgroupOf H).Normal] :
    bFac (H ⧸ (radicalPreimage H N).subgroupOf H) = bFac (H ⧸ N.subgroupOf H) := by
  let e := quotientPreimageEquiv (solvableRadical (H ⧸ N.subgroupOf H))
    (radicalPreimage_subgroupOf (H := H) (N := N))
  rw [bFac_congr e]
  symm
  rw [bFac_mul (solvableRadical (H ⧸ N.subgroupOf H)) (X := H ⧸ N.subgroupOf H),
    bFac_of_solvable, one_mul]

/-- `[E_H : R] = |soc(H/R)|`. -/
theorem relIndex_soclePreimage_eq [Finite G] {H R : Subgroup G} [(R.subgroupOf H).Normal] :
    ((R.subgroupOf H).relIndex ((soclePreimage H R).subgroupOf H)) =
      Nat.card (socle (H ⧸ R.subgroupOf H)) := by
  have hR : R.subgroupOf H =
      (⊥ : Subgroup (H ⧸ R.subgroupOf H)).comap (QuotientGroup.mk' (R.subgroupOf H)) := by
    rw [MonoidHom.comap_bot, QuotientGroup.ker_mk']
  rw [soclePreimage_subgroupOf]
  nth_rw 1 [hR]
  rw [Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
    bot_relIndex_eq_card]

/-- `[E_H : R] ≤ b(H/N)`. -/
theorem relIndex_soclePreimage_le [Finite G] {H N : Subgroup G} [(N.subgroupOf H).Normal] :
    ((radicalPreimage H N).subgroupOf H).relIndex
      ((soclePreimage H (radicalPreimage H N)).subgroupOf H) ≤
      bFac (H ⧸ N.subgroupOf H) := by
  rw [relIndex_soclePreimage_eq, ← bFac_quotient_radicalPreimage]
  exact card_socle_le_bFac radicalPreimage_quotient_radicalFree

/-- `[H : K*_H] ≤ b(H/N)`. -/
theorem index_radicalOuter_le
    [Finite G] {H N : Subgroup G} [(N.subgroupOf H).Normal] :
    ((radicalPreimage H (soclePreimage H (radicalPreimage H N))).subgroupOf H).index ≤
      bFac (H ⧸ N.subgroupOf H) := by
  set R := radicalPreimage H N
  set E_H := soclePreimage H R
  rw [radicalPreimage_subgroupOf,
    Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let e := quotientPreimageEquiv (socle (H ⧸ R.subgroupOf H))
    (soclePreimage_subgroupOf (H := H) (R := R))
  rw [solvableRadical_index_congr e, ← bFac_quotient_radicalPreimage]
  exact index_radical_quotient_socle_le radicalPreimage_quotient_radicalFree

/-- **Lemma A.21′ (quotient-supplement form)**: for any subgroup `R'` with `R ≤ R' ≤ K*_H`,
`R'/R` solvable, and `R' ⊔ E_H = K*_H`, we have `N ≤ R' ≤ H`, `R'/N` is solvable, and
`[H : R'] ≤ b(H/N)²`. -/
theorem radical_free_order_of_quotient [Finite G] {H N : Subgroup G} (hNH : N ≤ H)
    [(N.subgroupOf H).Normal] {R' : Subgroup G}
    (hRR' : radicalPreimage H N ≤ R')
    (hR'K : R' ≤ radicalPreimage H (soclePreimage H (radicalPreimage H N)))
    (hsolvR : ∀ [((radicalPreimage H N).subgroupOf R').Normal],
      Group.IsSolvable (R' ⧸ (radicalPreimage H N).subgroupOf R'))
    (hsup : R' ⊔ soclePreimage H (radicalPreimage H N) =
      radicalPreimage H (soclePreimage H (radicalPreimage H N))) :
    N ≤ R' ∧ R' ≤ H ∧ (N.subgroupOf R').Normal ∧
      (∃ ℓ, relDerived R' N ℓ ≤ N) ∧
      (∀ [(N.subgroupOf R').Normal], Group.IsSolvable (R' ⧸ N.subgroupOf R')) ∧
      (R'.subgroupOf H).index ≤ bFac (H ⧸ N.subgroupOf H) ^ 2 := by
  set R := radicalPreimage H N
  set E_H := soclePreimage H R
  set K_H := radicalPreimage H E_H
  have hn : Normalizes H N := normalizes_of_normal hNH
  obtain ⟨hRH, hNR, ℓ₂, hℓ₂⟩ := radicalPreimage_spec hNH hn
  have hKH : K_H ≤ H := radicalPreimage_le H E_H
  have hR'H : R' ≤ H := hR'K.trans hKH
  have hNR' : N ≤ R' := hNR.trans hRR'
  have : (N.subgroupOf R').Normal := normal_of_normalizes (hn.mono hR'H)
  have hnR : Normalizes H R := normalizes_of_normal hRH
  have : (R.subgroupOf R').Normal := normal_of_normalizes (hnR.mono hR'H)
  have := hsolvR
  obtain ⟨ℓ₁, hℓ₁⟩ := exists_relDerived_of_isSolvable hRR'
  have hrel : ∃ ℓ, relDerived R' N ℓ ≤ N := ⟨ℓ₁ + ℓ₂, relDerived_trans hNR hℓ₁ hℓ₂⟩
  have hsolvN : ∀ [(N.subgroupOf R').Normal], Group.IsSolvable (R' ⧸ N.subgroupOf R') :=
    fun [_] => isSolvable_quot_of_relDerived (relDerived_trans hNR hℓ₁ hℓ₂)
  -- Index bound `[H : R'] ≤ b(H/N)²`
  have hsup_sub : R'.subgroupOf H ⊔ E_H.subgroupOf H = K_H.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hR'H,
      inf_of_le_left (soclePreimage_le H R), inf_of_le_left hKH, hsup]
  have hidx_eq : (R'.subgroupOf H).index =
      (R'.subgroupOf H).relIndex (E_H.subgroupOf H) * (K_H.subgroupOf H).index := by
    rw [← relIndex_mul_index_sup (R'.subgroupOf H) (E_H.subgroupOf H), hsup_sub]
  have hRR'_sub : R.subgroupOf H ≤ R'.subgroupOf H := Subgroup.subgroupOf_mono H hRR'
  have hrel_le : (R'.subgroupOf H).relIndex (E_H.subgroupOf H) ≤ bFac (H ⧸ N.subgroupOf H) :=
    (Subgroup.relIndex_le_of_le_left hRR'_sub Nat.card_pos.ne').trans relIndex_soclePreimage_le
  have hK_le : (K_H.subgroupOf H).index ≤ bFac (H ⧸ N.subgroupOf H) := index_radicalOuter_le
  have hidx : (R'.subgroupOf H).index ≤ bFac (H ⧸ N.subgroupOf H) ^ 2 := by
    rw [hidx_eq, sq]
    exact Nat.mul_le_mul hrel_le hK_le
  exact ⟨hNR', hR'H, inferInstance, hrel, hsolvN, hidx⟩

/-- **Lemma A.21′** (`lem:radical-free-order`): for `N ◁ H`, let `R = radicalPreimage H N`,
`E_H = soclePreimage H R`, and `K*_H = radicalPreimage H E_H`. For any solvable subgroup
`S₁ ≤ K*_H` with `S₁ ⊔ E_H = K*_H`, the subgroup `R' = S₁ ⊔ R` satisfies `N ≤ R' ≤ H`,
`N ◁ R'`, `R'/N` is solvable, and `[H : R'] ≤ b(H/N)²`. -/
theorem radical_free_order_of_supplement [Finite G] {H N : Subgroup G} (hNH : N ≤ H)
    [(N.subgroupOf H).Normal] {S₁ : Subgroup G}
    (hS₁ : S₁ ≤ radicalPreimage H (soclePreimage H (radicalPreimage H N)))
    [Group.IsSolvable S₁]
    (hsup : S₁ ⊔ soclePreimage H (radicalPreimage H N) =
      radicalPreimage H (soclePreimage H (radicalPreimage H N))) :
    let R := radicalPreimage H N
    let R' := S₁ ⊔ R
    N ≤ R' ∧ R' ≤ H ∧ (N.subgroupOf R').Normal ∧
      (∃ ℓ, relDerived R' N ℓ ≤ N) ∧
      (∀ [(N.subgroupOf R').Normal], Group.IsSolvable (R' ⧸ N.subgroupOf R')) ∧
      (R'.subgroupOf H).index ≤ bFac (H ⧸ N.subgroupOf H) ^ 2 := by
  set R := radicalPreimage H N
  set E_H := soclePreimage H R
  set K_H := radicalPreimage H E_H
  set R' := S₁ ⊔ R
  have hRE : R ≤ E_H := le_soclePreimage (radicalPreimage_le H N)
  have hEK : E_H ≤ K_H := le_radicalPreimage (soclePreimage_le H R)
  have hRR' : R ≤ R' := le_sup_right
  have hR'K : R' ≤ K_H := sup_le hS₁ (hRE.trans hEK)
  have hsup' : R' ⊔ E_H = K_H := by
    rw [show R' ⊔ E_H = S₁ ⊔ (R ⊔ E_H) from sup_assoc _ _ _, sup_eq_right.mpr hRE, hsup]
  exact radical_free_order_of_quotient hNH hRR' hR'K (fun [_] => sup_quotient_solvable) hsup'

/-- The canonical subgroup `R' = radicalSubgroup H N` of Lemma A.21 has index at most
`b(H/N)²` in `H`. -/
theorem radicalSubgroup_index_le [Finite G] {H N : Subgroup G} (hNH : N ≤ H)
    [hN : (N.subgroupOf H).Normal] :
    ((radicalSubgroup H N).subgroupOf H).index ≤ bFac (H ⧸ N.subgroupOf H) ^ 2 := by
  rw [radicalSubgroup, dif_pos hN]
  obtain ⟨hS₁, hsolv, hsup⟩ :=
    Classical.choose_spec (exists_solvable_supplement_radicalOuter (H := H) (N := N))
  exact (radical_free_order_of_supplement hNH hS₁ hsup).2.2.2.2.2

end SolvablePreimage

end GI.RadicalFreeOrder
