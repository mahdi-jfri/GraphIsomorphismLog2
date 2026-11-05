module

public import Workspace.Schreier
public import Workspace.TransitiveKernelReduction
public import Workspace.AffineAlternatingExclusion
public import Workspace.BudgetInductionRadicalFree
public import Workspace.SocleOuterBudget
public import Workspace.SocleFactorDegree
public import Workspace.PrimitiveSubdirectDegree
public import Mathlib.Analysis.SpecialFunctions.Log.Base

@[expose] public section

namespace GI.AffectThreshold

open GI.RadicalSocle GI.PrimitiveStructure GI.PrimitiveCartesian GI.SocleOuter GI.SectionCaps

/-- For `k ≥ 5`, `2 ^ k ≤ k! / 2 = |Alt(k)|`. -/
theorem two_pow_le_card_alternatingGroup {k : ℕ} (hk : 5 ≤ k) :
    2 ^ k ≤ Nat.card (alternatingGroup (Fin k)) := by
  have h2 : 2 ^ (k + 1) ≤ k.factorial := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    clear hk
    induction d with
    | zero => decide
    | succ d ih =>
      have hpos : 2 ≤ 5 + d + 1 := by omega
      have hadd : 5 + (d + 1) = (5 + d) + 1 := by omega
      calc
        2 ^ (5 + (d + 1) + 1) = 2 * 2 ^ (5 + d + 1) := by ring
        _ ≤ (5 + d + 1) * (5 + d).factorial := Nat.mul_le_mul hpos ih
        _ = (5 + (d + 1)).factorial := by rw [hadd, Nat.factorial_succ]
  have half : 2 * Fintype.card (alternatingGroup (Fin k)) = k.factorial := by
    have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
    simpa only [Fintype.card_perm, Fintype.card_fin] using two_mul_card_alternatingGroup (α := Fin k)
  rw [Nat.card_eq_fintype_card]
  have hpow : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
  omega

/-- If `2 ^ k ≤ m ^ 2`, then `k ≤ 12 * log₂ m`. -/
theorem le_twelve_logb_of_two_pow_le_sq {k m : ℕ} (hm : 1 ≤ m) (h : 2 ^ k ≤ m ^ 2) :
    (k : ℝ) ≤ 12 * Real.logb 2 m := by
  have hr : (2 : ℝ) ^ k ≤ (m : ℝ) ^ 2 := by exact_mod_cast h
  have hlog := Real.log_le_log (pow_pos (by norm_num : (0 : ℝ) < 2) k) hr
  rw [Real.log_pow, Real.log_pow] at hlog
  push_cast at hlog
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  have hk2 : (k : ℝ) ≤ 2 * Real.logb 2 m := by
    rw [Real.logb, mul_div_assoc', le_div_iff₀ hlog2]
    linarith
  have hlogb_nonneg : 0 ≤ Real.logb 2 m := by
    rw [Real.logb]
    exact div_nonneg hlogm hlog2.le
  linarith

/-- In a radical-free primitive group `G` on `V`, the number `t` of minimal normal
subgroups of `socle G` satisfies `2 ^ t ≤ |V| ^ 2`. -/
theorem radicalFree_socle_factors_pow_le_degree_sq
    {G V : Type*} [Group G] [Finite G] [MulAction G V] [FaithfulSMul G V]
    [Nontrivial V] [MulAction.IsPreprimitive G V]
    (radicalFree : ∀ K : Subgroup G, K.Normal → Group.IsSolvable K → K = ⊥) (a : V) :
    2 ^ Nat.card (MinimalNormals (socle G)) ≤ (Nat.card V) ^ 2 := by
  classical
  have : Nontrivial G := by
    obtain ⟨b, hb⟩ := exists_ne a
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a b
    refine ⟨⟨g, 1, fun he => ?_⟩⟩
    rw [he, one_smul] at hg
    exact hb hg.symm
  obtain ⟨N, hN, _⟩ := exists_minimal_normal_le (⊤ : Subgroup G) top_ne_bot
  let _ : N.Normal := hN.1
  by_cases hpair : ∃ M : Subgroup G, MinimalNormal M ∧ M ≠ N
  · obtain ⟨M, hM, hne⟩ := hpair
    exact two_minimal_intrinsic_count_pow_le_degree_sq hM hN hne a
  · have hsoc : socle G = N := by
      apply le_antisymm
      · apply socle_le_normal
        intro M hM
        exact le_of_eq (not_ne_iff.mp (fun hne => hpair ⟨M, hM, hne⟩))
      · exact minimalNormal_le_socle hN
    let _ : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN.2.1
    obtain ⟨K, hK, _⟩ := exists_minimal_normal_le (⊤ : Subgroup N) top_ne_bot
    by_cases honto : ∀ j : MinimalNormals N,
        ((MulAction.stabilizer G a).comap (minimalCoordinateEmbedding radicalFree N hN)).map
          (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) j) = ⊤
    · calc
        2 ^ Nat.card (MinimalNormals (socle G)) ≤ Nat.card (socle G) :=
          socle_intrinsic_count_pow_le_card radicalFree
        _ = Nat.card N := by rw [hsoc]
        _ ≤ (Nat.card V) ^ 2 :=
          minimalNormal_card_le_degree_sq_of_subdirect radicalFree N hN a ⟨K, hK⟩ honto
    · push Not at honto
      obtain ⟨j, hproper⟩ := honto
      have hdeg := primitive_uniform_degree radicalFree N hN a j hproper
      have hind : 2 ≤
          (((MulAction.stabilizer G a).comap (minimalCoordinateEmbedding radicalFree N hN)).map
            (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) j)).index :=
        Nat.succ_le_iff.mpr (Subgroup.one_lt_index_of_ne_top hproper)
      have hcount : Nat.card (MinimalNormals (socle G)) = Nat.card (MinimalNormals N) := by
        rw [hsoc]
      calc
        2 ^ Nat.card (MinimalNormals (socle G)) = 2 ^ Nat.card (MinimalNormals N) := by
          rw [hcount]
        _ ≤ (((MulAction.stabilizer G a).comap (minimalCoordinateEmbedding radicalFree N hN)).map
              (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) j)).index ^
                Nat.card (MinimalNormals N) := Nat.pow_le_pow_left hind _
        _ = Nat.card V := hdeg.symm
        _ ≤ (Nat.card V) ^ 2 := Nat.le_self_pow two_ne_zero (Nat.card V)

/-- In a radical-free group `G`, if `ψ : G ↠ Alt(k)` (`k ≥ 5`) contains `socle G` in its
kernel, then `k` is at most the number of minimal normal subgroups of `socle G`. -/
theorem quotient_degree_le_socle_factors_of_socle_le_ker
    {G : Type*} [Group G] [Finite G]
    (radicalFree : ∀ K : Subgroup G, K.Normal → Group.IsSolvable K → K = ⊥)
    {k : ℕ} (hk5 : 5 ≤ k) (ψ : G →* alternatingGroup (Fin k))
    (hψ : Function.Surjective ψ) (hsoc_ker : socle G ≤ ψ.ker) :
    k ≤ Nat.card (MinimalNormals (socle G)) := by
  classical
  let S := socle G
  let I := MinimalNormals S
  let _ := Fintype.ofFinite I
  let act : G →* Equiv.Perm I :=
    (minimalNormalAction (G := S)).comp (socleConjugation (G := G))
  have hact_ker : act.ker ≤ ψ.ker := by
    let pre := preimage (socleConjugation (G := G)) (FactorKernel S)
    let toOut : act.ker →* (∀ N : I, OuterAut N.val) :=
      (factorOuterHom (G := S)).comp pre
    have hradS := normal_subgroup_radicalFree radicalFree S
    have htoOut_ker : toOut.ker ≤ (ψ.comp act.ker.subtype).ker := by
      intro x hx
      have hx' : pre x ∈ (factorOuterHom (G := S)).ker := hx
      rw [factorOuterHom_ker_eq_inner_comap hradS socle_idempotent] at hx'
      obtain ⟨s, hs⟩ := hx'
      have hconj : socleConjugation (G := G) x.val = socleConjugation (G := G) s.val := by
        calc
          socleConjugation (G := G) x.val = (pre x).val := rfl
          _ = MulAut.conj s := hs.symm
          _ = socleConjugation (G := G) s.val := MulAut.conjNormal_val.symm
      have hxs : x.val = s.val := socleConjugation_injective radicalFree hconj
      change ψ x.val = 1
      rw [hxs]
      exact hsoc_ker s.property
    have outerSolvable : ∀ N : I, Group.IsSolvable (OuterAut N.val) := by
      intro N
      let _ : IsSimpleGroup N.val := socle_intrinsic_factor_simple N
      exact GI.schreier N.val (socle_intrinsic_factor_nonabelian radicalFree N)
    have hcapOut : Cap (∀ N : I, OuterAut N.val) 4 :=
      product_cap_four_of_solvable outerSolvable
    let _ : IsSimpleGroup (alternatingGroup (Fin k)) := GI.AlternatingSimple.isSimple_fin hk5
    have hn : (act.ker.map ψ).Normal := (inferInstance : act.ker.Normal).map ψ hψ
    rcases hn.eq_bot_or_eq_top with hbot | htop
    · intro g hg
      have hm : ψ g ∈ act.ker.map ψ := ⟨g, hg, rfl⟩
      simpa only [hbot, Subgroup.mem_bot, MonoidHom.mem_ker] using hm
    · exfalso
      have honto : Function.Surjective (ψ.comp act.ker.subtype) := by
        intro y
        have hy : y ∈ act.ker.map ψ := by rw [htop]; exact Subgroup.mem_top y
        obtain ⟨g, hg, rfl⟩ := hy
        exact ⟨⟨g, hg⟩, rfl⟩
      have hk4 := quotient_degree_le hcapOut hk5 toOut (ψ.comp act.ker.subtype) honto htoOut_ker
      omega
  have hk_card := quotient_degree_le permutations hk5 act ψ hψ hact_ker
  rwa [← Nat.card_eq_fintype_card] at hk_card

/-- If `ψ : G ↠ Alt(k)` has transitive kernel on `V` (`|V| ≥ 5`, `k ≥ 5`) for a primitive
group `G ≤ Perm(V)`, then `k ≤ max 63 (12 * log₂ |V|)`. -/
theorem primitive_obstruction_bound {k n : ℕ} (hk5 : 5 ≤ k)
    (w : GI.A15Work.PrimitiveObstruction k n) :
    (k : ℝ) ≤ max 63 (12 * @Real.logb 2 (@Fintype.card w.Domain w.finite)) := by
  classical
  let _ : Fintype w.Domain := w.finite
  let _ : MulAction.IsPreprimitive w.group w.Domain := w.primitive
  let ψ := w.step.quotient
  have hψ := w.step.onto
  have htV := w.kernel_transitive
  have hk_le_V : k ≤ Fintype.card w.Domain := GI.A15Work.alternating_quotient_degree_le hk5 ψ hψ
  have hV1 : 1 ≤ Fintype.card w.Domain := by omega
  have : Nontrivial w.Domain := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  by_cases hrad : solvableRadical w.group = ⊥
  · refine (?_ : (k : ℝ) ≤ 12 * Real.logb 2 (Fintype.card w.Domain)).trans (le_max_right _ _)
    have radicalFree : ∀ K : Subgroup w.group, K.Normal → Group.IsSolvable K → K = ⊥ := by
      intro K hK hs
      have := hK
      have : Group.IsSolvable K := hs
      exact le_bot_iff.mp (hrad ▸ le_solvableRadical K)
    by_cases hM_all : ∀ M : Subgroup w.group, MinimalNormal M → M ≤ ψ.ker
    · have hsoc_ker : socle w.group ≤ ψ.ker := socle_le_normal ψ.ker hM_all
      have hk_le_t := quotient_degree_le_socle_factors_of_socle_le_ker
        radicalFree hk5 ψ hψ hsoc_ker
      have ht_pow := radicalFree_socle_factors_pow_le_degree_sq radicalFree w.base
      rw [Nat.card_eq_fintype_card (α := w.Domain)] at ht_pow
      have hk_pow : 2 ^ k ≤ (Fintype.card w.Domain) ^ 2 :=
        (Nat.pow_le_pow_right (by decide) hk_le_t).trans ht_pow
      exact le_twelve_logb_of_two_pow_le_sq hV1 hk_pow
    · push Not at hM_all
      obtain ⟨M, hM, hM_not⟩ := hM_all
      let _ : M.Normal := hM.1
      have hMK_bot : M ⊓ ψ.ker = ⊥ := by
        rcases hM.2.2 (M ⊓ ψ.ker) inferInstance inf_le_left with hb | he
        · exact hb
        · exfalso
          exact hM_not (he ▸ inf_le_right)
      have comm : ∀ m : M, ∀ n : ψ.ker, (m : w.group) * (n : w.group) = (n : w.group) * (m : w.group) := by
        intro m n
        have hc := Subgroup.commutator_le_inf M ψ.ker
          (Subgroup.commutator_mem_commutator m.property n.property)
        rw [hMK_bot, Subgroup.mem_bot] at hc
        exact commutatorElement_eq_one_iff_mul_comm.mp hc
      have : MulAction.IsPretransitive ψ.ker w.Domain :=
        ⟨fun x y => by
          obtain ⟨g, hg1, hgx⟩ := htV x y
          exact ⟨⟨g, hg1⟩, hgx⟩⟩
      have hM_card : Nat.card M ≤ Fintype.card w.Domain := by
        rw [← Nat.card_eq_fintype_card]
        exact Nat.card_le_card_of_injective _ (commuting_transitive_free M ψ.ker comm w.base)
      let _ : IsSimpleGroup (alternatingGroup (Fin k)) := GI.AlternatingSimple.isSimple_fin hk5
      have hn : (M.map ψ).Normal := hM.1.map ψ hψ
      rcases hn.eq_bot_or_eq_top with hbot | htop
      · exfalso
        apply hM_not
        intro m hm
        have hm' : ψ m ∈ M.map ψ := ⟨m, hm, rfl⟩
        simpa only [hbot, Subgroup.mem_bot, MonoidHom.mem_ker] using hm'
      · have honto : Function.Surjective (ψ.comp M.subtype) := by
          intro y
          have hy : y ∈ M.map ψ := by rw [htop]; exact Subgroup.mem_top y
          obtain ⟨m, hm, rfl⟩ := hy
          exact ⟨⟨m, hm⟩, rfl⟩
        have hcard_alt : Nat.card (alternatingGroup (Fin k)) ≤ Nat.card M :=
          Nat.card_le_card_of_surjective _ honto
        have hk_pow : 2 ^ k ≤ (Fintype.card w.Domain) ^ 2 :=
          calc
            2 ^ k ≤ Nat.card (alternatingGroup (Fin k)) := two_pow_le_card_alternatingGroup hk5
            _ ≤ Nat.card M := hcard_alt
            _ ≤ Fintype.card w.Domain := hM_card
            _ ≤ (Fintype.card w.Domain) ^ 2 := Nat.le_self_pow two_ne_zero (Fintype.card w.Domain)
        exact le_twelve_logb_of_two_pow_le_sq hV1 hk_pow
  · obtain ⟨N, hN, comm⟩ := exists_abelian_normal_of_radical_ne_bot hrad
    let _ : N.Normal := hN.1
    obtain ⟨p, hp, d, ⟨basis⟩⟩ := abelian_normal_coordinates N hN.2.1 comm w.base
    let _ : Fact p.Prime := ⟨hp⟩
    have regular := abelian_normal_regular N hN.2.1 comm w.base
    have hG := GI.AffineRecognition.permutation_group_le_affine_range w.group N w.base regular basis
    have hdeg := GI.AffineRecognition.degree_eq N w.base regular basis
    have hb := GI.A15Work.affine_image_alternating_quotient_bound
      (GI.AffineRecognition.physicalAffineAction N w.base regular basis) w.group hG ψ hψ
    have hcard : ((Fintype.card (ZMod p) : ℝ) ^ d) = (Fintype.card w.Domain : ℝ) := by
      exact_mod_cast hdeg.symm
    have hlog_eq : (12 / Real.log 2) * Real.log ((Fintype.card (ZMod p) : ℝ) ^ d) =
        12 * Real.logb 2 (Fintype.card w.Domain) := by
      rw [hcard, Real.logb]
      ring
    rwa [hlog_eq] at hb

/-- If `q : H ↠ Alt(k)` has transitive kernel on `B`, then
`k ≤ max 63 (12 * log₂ |B|)`. -/
theorem transitive_kernel_alternating_quotient_bound
    {B : Type} [Fintype B] {H : Subgroup (Equiv.Perm B)} {k : ℕ}
    (q : H →* alternatingGroup (Fin k)) (hq : Function.Surjective q)
    (ht : ∀ x y : B, ∃ g : H, q g = 1 ∧ g.val x = y) :
    (k : ℝ) ≤ max 63 (12 * Real.logb 2 (Fintype.card B)) := by
  by_cases hk : k ≤ 63
  · exact (by exact_mod_cast hk : (k : ℝ) ≤ 63).trans (le_max_left _ _)
  · push Not at hk
    have hk5 : 5 ≤ k := by omega
    obtain ⟨w⟩ := GI.A15Work.primitive_obstruction_of_transitive_kernel hk5 q hq ht
    let _ : Fintype w.Domain := w.finite
    have hb := primitive_obstruction_bound hk5 w
    have hV_pos : 0 < Fintype.card w.Domain := by
      have := GI.A15Work.alternating_quotient_degree_le hk5 w.step.quotient w.step.onto
      omega
    have hlog_le : Real.logb 2 (Fintype.card w.Domain) ≤ Real.logb 2 (Fintype.card B) := by
      rw [Real.logb, Real.logb]
      apply div_le_div_of_nonneg_right _ (Real.log_pos (by norm_num)).le
      exact Real.log_le_log (by exact_mod_cast hV_pos) (by exact_mod_cast w.degree)
    exact hb.trans (max_le_max_left 63 (by linarith))

end GI.AffectThreshold
