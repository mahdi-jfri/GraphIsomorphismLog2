module

public import Workspace.PrimitiveProductStabilizer
public import Workspace.PrimitiveMinimalNormals
public import Workspace.SocleSimpleAlternative
public import Workspace.PrimitiveCoordinateFibers
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Nilpotent

@[expose] public section

set_option linter.style.haveILetI false

namespace GI.Proved

open scoped Pointwise
open GI.RadicalSocle GI.PrimitiveStructure GI.PrimitiveCartesian

variable {G V : Type*} [Group G] [MulAction G V]

/-- A group action of `G` on `V` is 2-transitive if any ordered pair of distinct elements
can be mapped to any other ordered pair of distinct elements. -/
def WielTwoTrans (G : Type*) (V : Type*) [Group G] [MulAction G V] : Prop :=
  ∀ x₁ x₂ y₁ y₂ : V, x₁ ≠ x₂ → y₁ ≠ y₂ → ∃ g : G, g • x₁ = y₁ ∧ g • x₂ = y₂

theorem WielTwoTrans.isPretransitive [Nontrivial V] (h2 : WielTwoTrans G V) :
    MulAction.IsPretransitive G V := by
  constructor
  intro x y
  by_cases hxy : x = y
  · exact ⟨1, by rw [one_smul, hxy]⟩
  · obtain ⟨g, hg, _⟩ := h2 x y y x hxy (Ne.symm hxy)
    exact ⟨g, hg⟩

theorem WielTwoTrans.exists_stabilizer_smul_eq (h2 : WielTwoTrans G V)
    {a b c : V} (hb : b ≠ a) (hc : c ≠ a) :
    ∃ g : MulAction.stabilizer G a, (g : G) • b = c := by
  obtain ⟨g, hga, hgb⟩ := h2 a b a c (Ne.symm hb) (Ne.symm hc)
  exact ⟨⟨g, hga⟩, hgb⟩

theorem WielTwoTrans.isPreprimitive [Nontrivial V] (h2 : WielTwoTrans G V) :
    MulAction.IsPreprimitive G V := by
  have htr : MulAction.IsPretransitive G V := h2.isPretransitive
  refine { htr with isTrivialBlock_of_isBlock := ?_ }
  intro B hB
  rcases Set.subsingleton_or_nontrivial B with hsub | hnontriv
  · exact Or.inl hsub
  · right
    obtain ⟨x, hx, y, hy, hxy⟩ := hnontriv
    ext z
    simp only [Set.mem_univ, iff_true]
    by_cases hzx : z = x
    · exact hzx ▸ hx
    · obtain ⟨g, hgx, hgy⟩ := h2 x y x z hxy (Ne.symm hzx)
      have heq : g • B = (1 : G) • B :=
        hB.smul_eq_smul_of_nonempty ⟨x, ⟨x, hx, hgx⟩, by simpa only [one_smul] using hx⟩
      have hz : z ∈ g • B := ⟨y, hy, hgy⟩
      simpa only [heq, one_smul] using hz

/-- If all nonidentity elements of a finite nontrivial group have the same order,
then the group has a prime order element `x₀` such that every nonidentity element has
that same prime order. -/
theorem exists_prime_orderOf_all_ne_one {H : Type*} [Group H] [Finite H] [Nontrivial H]
    (hord : ∀ x y : H, x ≠ 1 → y ≠ 1 → orderOf x = orderOf y) :
    ∃ p : ℕ, p.Prime ∧ ∀ y : H, y ≠ 1 → orderOf y = p := by
  have hcard : Nat.card H ≠ 1 := by
    intro hc
    letI : Subsingleton H := (Nat.card_eq_one_iff_unique.mp hc).1
    obtain ⟨x, hx⟩ := exists_ne (1 : H)
    exact hx (Subsingleton.elim _ _)
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hcard
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := H) p hdvd
  have hx₀_ne : x₀ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx₀
    exact hp.ne_one hx₀.symm
  exact ⟨p, hp, fun y hy => (hord y x₀ hy hx₀_ne).trans hx₀⟩

/-- If all nonidentity elements of a finite nontrivial group have the same order,
then the group is a `p`-group for some prime `p` and therefore is solvable. -/
theorem isSolvable_of_orderOf_eq {H : Type*} [Group H] [Finite H] [Nontrivial H]
    (hord : ∀ x y : H, x ≠ 1 → y ≠ 1 → orderOf x = orderOf y) :
    Group.IsSolvable H := by
  obtain ⟨p, hp, hall⟩ := exists_prime_orderOf_all_ne_one hord
  letI : Fact p.Prime := ⟨hp⟩
  have hpG : IsPGroup p H := by
    rw [IsPGroup.iff_orderOf]
    intro y
    by_cases hy : y = 1
    · exact ⟨0, by rw [hy, orderOf_one, pow_zero]⟩
    · exact ⟨1, by rw [pow_one, hall y hy]⟩
  haveI := hpG.isNilpotent
  infer_instance

/-- In any nontrivial solvable group, the commutator subgroup `derivedSeries H 1` is
strictly smaller than `⊤`. -/
theorem derivedSeries_one_ne_top_of_solvable {H : Type*} [Group H] [Nontrivial H]
    [Group.IsSolvable H] : derivedSeries H 1 ≠ ⊤ := by
  intro ht
  have h1 : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤ := by
    simpa only [derivedSeries_succ, derivedSeries_zero] using ht
  have hall : ∀ k : ℕ, derivedSeries H k = ⊤ := by
    intro k
    induction k with
    | zero => exact derivedSeries_zero H
    | succ k ih => rw [derivedSeries_succ, ih, h1]
  obtain ⟨k, hk⟩ := ‹Group.IsSolvable H›.solvable
  have hbot : (⊤ : Subgroup H) = ⊥ := by rw [← hall k, hk]
  exact top_ne_bot hbot

/-- If `derivedSeries H 1 = ⊥`, then `H` is abelian. -/
theorem comm_of_derivedSeries_one_eq_bot {H : Type*} [Group H]
    (hb : derivedSeries H 1 = ⊥) (x y : H) : x * y = y * x := by
  letI : Bracket H H := commutatorElement
  rw [derivedSeries_succ, derivedSeries_zero] at hb
  have hm : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup H), ⊤⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  rw [hb, Subgroup.mem_bot] at hm
  exact commutatorElement_eq_one_iff_mul_comm.mp hm

/-- In a 2-transitive action, if a normal subgroup `N` acts regularly, then the point
stabilizer `stabilizer G a` acts transitively on `N \ {1}` by conjugation. -/
theorem regular_normal_conj_transitive (h2 : WielTwoTrans G V)
    (N : Subgroup G) [N.Normal] (a : V)
    (hreg : Function.Bijective (fun n : N => n • a))
    {x y : N} (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ g : MulAction.stabilizer G a, MulAut.conjNormal (H := N) (g : G) x = y := by
  have hxa : x • a ≠ a := by
    intro h
    exact hx (hreg.injective (by simpa only [one_smul] using h))
  have hya : y • a ≠ a := by
    intro h
    exact hy (hreg.injective (by simpa only [one_smul] using h))
  obtain ⟨g, hg⟩ := h2.exists_stabilizer_smul_eq hxa hya
  refine ⟨g, hreg.injective ?_⟩
  change ((g : G) * (x : G) * (g : G)⁻¹) • a = (y : G) • a
  have hginv : (g : G)⁻¹ • a = a := by
    have hga : (g : G) • a = a := g.property
    calc (g : G)⁻¹ • a = (g : G)⁻¹ • ((g : G) • a) := by rw [hga]
      _ = a := inv_smul_smul (g : G) a
  rw [mul_smul, mul_smul, hginv]
  exact hg

/-- Fact 1: Every regular normal subgroup of a finite 2-transitive group is abelian. -/
theorem regular_normal_abelian_of_two_transitive [Finite G] [Nontrivial V]
    (h2 : WielTwoTrans G V) (N : Subgroup G) [N.Normal] (a : V)
    (hreg : Function.Bijective (fun n : N => n • a)) :
    ∀ x y : N, x * y = y * x := by
  letI : Nontrivial N := (Equiv.ofBijective _ hreg).nontrivial
  have hord : ∀ x y : N, x ≠ 1 → y ≠ 1 → orderOf x = orderOf y := by
    intro x y hx hy
    obtain ⟨g, rfl⟩ := regular_normal_conj_transitive h2 N a hreg hx hy
    exact (MulEquiv.orderOf_eq (MulAut.conjNormal (H := N) (g : G)) x).symm
  haveI : Group.IsSolvable N := isSolvable_of_orderOf_eq hord
  have hne_top : derivedSeries N 1 ≠ ⊤ := derivedSeries_one_ne_top_of_solvable
  have hbot : derivedSeries N 1 = ⊥ := by
    by_contra hne_bot
    letI : Nontrivial (derivedSeries N 1) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne_bot
    obtain ⟨⟨z, hz_mem⟩, hz_ne'⟩ := exists_ne (1 : derivedSeries N 1)
    have hz_ne : z ≠ 1 := fun h => hz_ne' (Subtype.ext h)
    apply hne_top
    rw [eq_top_iff]
    intro y _
    by_cases hy : y = 1
    · exact hy ▸ (derivedSeries N 1).one_mem
    · obtain ⟨g, rfl⟩ := regular_normal_conj_transitive h2 N a hreg hz_ne hy
      have hchar : (derivedSeries N 1).Characteristic := by
        rw [derivedSeries_succ, derivedSeries_zero]
        infer_instance
      rw [Subgroup.characteristic_iff_map_le] at hchar
      exact hchar (MulAut.conjNormal (H := N) (g : G)) ⟨z, hz_mem, rfl⟩
  exact comm_of_derivedSeries_one_eq_bot hbot

/-- If a regular normal subgroup of a finite 2-transitive group is cyclic, then the degree
`Nat.card V` is prime. -/
theorem regular_normal_prime_card_of_cyclic [Finite G] [Nontrivial V]
    (h2 : WielTwoTrans G V) (N : Subgroup G) [N.Normal] (a : V)
    (hreg : Function.Bijective (fun n : N => n • a)) (hcyc : IsCyclic N) :
    (Nat.card V).Prime := by
  let e : N ≃ V := Equiv.ofBijective _ hreg
  letI : Nontrivial N := e.nontrivial
  have hord : ∀ x y : N, x ≠ 1 → y ≠ 1 → orderOf x = orderOf y := by
    intro x y hx hy
    obtain ⟨g, rfl⟩ := regular_normal_conj_transitive h2 N a hreg hx hy
    exact (MulEquiv.orderOf_eq (MulAut.conjNormal (H := N) (g : G)) x).symm
  obtain ⟨p, hp, hall⟩ := exists_prime_orderOf_all_ne_one hord
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hg_ne : g ≠ 1 := by
    intro h1
    obtain ⟨x, hx⟩ := exists_ne (1 : N)
    obtain ⟨k, hk⟩ := hg x
    change g ^ k = x at hk
    rw [← hk, h1, one_zpow] at hx
    exact hx rfl
  haveI : Fintype N := Fintype.ofFinite N
  have hcardN : Nat.card N = p :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).symm.trans (hall g hg_ne)
  rw [← Nat.card_congr e, hcardN]
  exact hp

/-- Every solvable minimal normal subgroup is abelian. -/
theorem minimalNormal_abelian_of_solvable {N : Subgroup G}
    (hN : MinimalNormal N) [Group.IsSolvable N] :
    ∀ x y : N, x * y = y * x := by
  haveI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN.2.1
  have hchar : (derivedSeries N 1).Characteristic := by
    rw [derivedSeries_succ, derivedSeries_zero]
    infer_instance
  rcases minimalNormal_characteristic_subgroup hN (derivedSeries N 1) with hb | ht
  · exact comm_of_derivedSeries_one_eq_bot hb
  · exact (derivedSeries_one_ne_top_of_solvable ht).elim

/-- If a faithful 2-transitive group has a nonabelian minimal normal subgroup `N`,
then `G` has no nontrivial solvable normal subgroup. -/
theorem radicalFree_of_two_transitive_nonabelian_minimalNormal
    [Finite G] [FaithfulSMul G V] [Nontrivial V]
    (h2 : WielTwoTrans G V) {N : Subgroup G} (hN : MinimalNormal N)
    (hnonab : ∃ x y : N, x * y ≠ y * x) (a : V) :
    ∀ K : Subgroup G, K.Normal → Group.IsSolvable K → K = ⊥ := by
  haveI : MulAction.IsPreprimitive G V := h2.isPreprimitive
  intro K hK hsolv
  letI := hK
  letI := hsolv
  by_contra hKne
  obtain ⟨M, hM, hMK⟩ := exists_minimal_normal_le K hKne
  letI : M.Normal := hM.1
  haveI : Group.IsSolvable M := Group.isSolvable_of_ker_le_range
    (⊥ : Subgroup M).subtype (Subgroup.inclusion hMK) (by
      intro x hx
      have hx1 : x = 1 := Subgroup.inclusion_injective hMK hx
      exact ⟨1, hx1.symm⟩)
  have hMN : M ≠ N := by
    intro heq
    subst heq
    obtain ⟨x, y, hxy⟩ := hnonab
    exact hxy (minimalNormal_abelian_of_solvable hM x y)
  have hregN : Function.Bijective (fun n : N => n • a) :=
    (distinct_minimal_normals_regular hM hN hMN a).2
  letI : N.Normal := hN.1
  obtain ⟨x, y, hxy⟩ := hnonab
  exact hxy (regular_normal_abelian_of_two_transitive h2 N a hregN x y)

section ProductElimination

variable {I : Type*} {S : I → Type*} [∀ i, Group (S i)] [DecidableEq I]

/-- In a faithful transitive product embedding, no nontrivial factor is contained in the
point stabilizer. -/
theorem product_factor_not_le_stabilizer [FaithfulSMul G V]
    (a : V) (F : (∀ i, S i) →* G) (hinj : Function.Injective F)
    (hreps : ∀ v : V, ∃ z : ∀ i, S i, F z • a = v)
    (m : I) [Nontrivial (S m)] :
    ∃ x : S m, Pi.mulSingle m x ∉ (MulAction.stabilizer G a).comap F := by
  by_contra hall
  push Not at hall
  obtain ⟨x, hx⟩ := exists_ne (1 : S m)
  apply hx
  have hF1 : F (Pi.mulSingle m x) = 1 := by
    apply eq_of_smul_eq_smul (α := V)
    intro v
    rw [one_smul]
    obtain ⟨z, rfl⟩ := hreps v
    have hcomm_z : Pi.mulSingle m x * z = z * Pi.mulSingle m ((z m)⁻¹ * x * z m) := by
      funext j
      by_cases hj : j = m
      · subst hj
        simp only [Pi.mul_apply, Pi.mulSingle_eq_same, mul_assoc, mul_inv_cancel_left]
      · simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, one_mul, mul_one]
    have hmem : F (Pi.mulSingle m ((z m)⁻¹ * x * z m)) • a = a := hall ((z m)⁻¹ * x * z m)
    rw [← mul_smul, ← map_mul, hcomm_z, map_mul, mul_smul, hmem]
  have hsingle1 : Pi.mulSingle m x = (1 : ∀ i, S i) := hinj (hF1.trans (map_one F).symm)
  simpa only [Pi.mulSingle_eq_same, Pi.one_apply] using congrFun hsingle1 m

/-- Elimination of multiple factors in the proper-projection branch (`projectionEnvelope = K`). -/
theorem subsingleton_of_two_transitive_proper_envelope
    (h2 : WielTwoTrans G V) (a : V) (F : (∀ i, S i) →* G)
    (hnot_all : ∀ m : I, ∃ x : S m, Pi.mulSingle m x ∉ (MulAction.stabilizer G a).comap F)
    (hconj : ∀ (g : MulAction.stabilizer G a) (m : I) (x : S m),
      ∃ (j : I) (y : S j), (g : G) • (F (Pi.mulSingle m x) • a) = F (Pi.mulSingle j y) • a)
    (hprod : projectionEnvelope ((MulAction.stabilizer G a).comap F) =
      (MulAction.stabilizer G a).comap F) :
    Subsingleton I := by
  constructor
  intro i₁ i₂
  by_contra hi₁₂
  let K := (MulAction.stabilizer G a).comap F
  have hmem_iff : ∀ z : ∀ i, S i,
      z ∈ K ↔ ∀ m : I, z m ∈ K.map (Pi.evalMonoidHom S m) := by
    intro z
    constructor
    · intro hz m
      exact ⟨z, hz, rfl⟩
    · intro hz
      have hpi : z ∈ projectionEnvelope K := fun m _ => hz m
      rwa [hprod] at hpi
  have hnot_proj : ∀ m : I,
      ∃ t : S m, t ∉ K.map (Pi.evalMonoidHom S m) := by
    intro m
    obtain ⟨x, hx⟩ := hnot_all m
    by_contra hall
    push Not at hall
    apply hx
    rw [hmem_iff]
    intro j
    by_cases hj : j = m
    · subst hj
      rw [Pi.mulSingle_eq_same]
      exact hall x
    · rw [Pi.mulSingle_eq_of_ne hj]
      exact Subgroup.one_mem _
  obtain ⟨t₁, ht₁⟩ := hnot_proj i₁
  obtain ⟨t₂, ht₂⟩ := hnot_proj i₂
  let z₁ : ∀ i, S i := Pi.mulSingle i₁ t₁
  let z₁₂ : ∀ i, S i := Pi.mulSingle i₁ t₁ * Pi.mulSingle i₂ t₂
  have hz₁ : F z₁ • a ≠ a := by
    intro h
    have hk := (hmem_iff z₁).mp h i₁
    change Pi.mulSingle i₁ t₁ i₁ ∈ _ at hk
    rw [Pi.mulSingle_eq_same] at hk
    exact ht₁ hk
  have hz₁₂ : F z₁₂ • a ≠ a := by
    intro h
    have hk := (hmem_iff z₁₂).mp h i₁
    have heval : z₁₂ i₁ = t₁ := by
      simp only [z₁₂, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hi₁₂, mul_one]
    rw [heval] at hk
    exact ht₁ hk
  obtain ⟨g, hg⟩ := h2.exists_stabilizer_smul_eq hz₁ hz₁₂
  obtain ⟨j, y, hjy⟩ := hconj g i₁ t₁
  rw [hjy] at hg
  have hw : (Pi.mulSingle j y)⁻¹ * z₁₂ ∈ K := by
    change F ((Pi.mulSingle j y)⁻¹ * z₁₂) • a = a
    rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff]
    exact hg.symm
  by_cases hj₁ : j = i₁
  · have hj₂ : j ≠ i₂ := hj₁ ▸ hi₁₂
    have hw₂ := (hmem_iff _).mp hw i₂
    have heval₂ : ((Pi.mulSingle j y)⁻¹ * z₁₂) i₂ = t₂ := by
      simp only [z₁₂, Pi.mul_apply, Pi.inv_apply]
      rw [Pi.mulSingle_eq_of_ne (Ne.symm hj₂), Pi.mulSingle_eq_of_ne (Ne.symm hi₁₂),
        Pi.mulSingle_eq_same, inv_one, one_mul, one_mul]
    rw [heval₂] at hw₂
    exact ht₂ hw₂
  · have hw₁ := (hmem_iff _).mp hw i₁
    have heval₁ : ((Pi.mulSingle j y)⁻¹ * z₁₂) i₁ = t₁ := by
      simp only [z₁₂, Pi.mul_apply, Pi.inv_apply]
      rw [Pi.mulSingle_eq_of_ne (Ne.symm hj₁), Pi.mulSingle_eq_same,
        Pi.mulSingle_eq_of_ne hi₁₂, inv_one, one_mul, mul_one]
    rw [heval₁] at hw₁
    exact ht₁ hw₁

/-- Elimination of the subdirect branch (`∀ m, R m = ⊤`) for nonabelian simple factors. -/
theorem false_of_two_transitive_subdirect
    [∀ m, Finite (S m)] [∀ m, IsSimpleGroup (S m)]
    (h2 : WielTwoTrans G V) (a : V) (F : (∀ i, S i) →* G) (i₁ : I)
    (hnonab : ∃ x y : S i₁, x * y ≠ y * x)
    (hnot_all : ∀ m : I, ∃ x : S m, Pi.mulSingle m x ∉ (MulAction.stabilizer G a).comap F)
    (hconj : ∀ (g : MulAction.stabilizer G a) (m : I) (x : S m),
      ∃ (j : I) (φ : S m ≃* S j),
        (g : G) • (F (Pi.mulSingle m x) • a) = F (Pi.mulSingle j (φ x)) • a)
    (hsub : ∀ m : I,
      ((MulAction.stabilizer G a).comap F).map (Pi.evalMonoidHom S m) = ⊤) :
    False := by
  let K := (MulAction.stabilizer G a).comap F
  have hKsingle : ∀ (m : I) (x : S m), Pi.mulSingle m x ∈ K → x = 1 := by
    intro m
    let f_m := MonoidHom.mulSingle S m
    let Km : Subgroup (S m) := K.comap f_m
    have hKm_norm : Km.Normal := by
      constructor
      intro x hx s
      have hs : s ∈ K.map (Pi.evalMonoidHom S m) := by rw [hsub m]; exact Subgroup.mem_top s
      obtain ⟨k, hk, hkm⟩ := hs
      change k m = s at hkm
      have hconj_k : k * Pi.mulSingle m x * k⁻¹ = Pi.mulSingle m (s * x * s⁻¹) := by
        funext j
        by_cases hj : j = m
        · subst hj
          simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same, hkm]
        · simp only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_of_ne hj,
            mul_one, mul_inv_cancel]
      change Pi.mulSingle m (s * x * s⁻¹) ∈ K
      rw [← hconj_k]
      exact K.mul_mem (K.mul_mem hk hx) (K.inv_mem hk)
    rcases hKm_norm.eq_bot_or_eq_top with hb | ht
    · intro x hx
      have hmem : x ∈ Km := hx
      rw [hb, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      obtain ⟨x, hx⟩ := hnot_all m
      have hmem : x ∈ Km := by rw [ht]; exact Subgroup.mem_top x
      exact hx hmem
  have hord : ∀ t₁ t₂ : S i₁, t₁ ≠ 1 → t₂ ≠ 1 → orderOf t₁ = orderOf t₂ := by
    intro t₁ t₂ ht₁ ht₂
    have hp₁ : F (Pi.mulSingle i₁ t₁) • a ≠ a := fun h => ht₁ (hKsingle i₁ t₁ h)
    have hp₂ : F (Pi.mulSingle i₁ t₂) • a ≠ a := fun h => ht₂ (hKsingle i₁ t₂ h)
    obtain ⟨g, hg⟩ := h2.exists_stabilizer_smul_eq hp₁ hp₂
    obtain ⟨j, φ, hjφ⟩ := hconj g i₁ t₁
    rw [hjφ] at hg
    have hz : (Pi.mulSingle i₁ t₂)⁻¹ * Pi.mulSingle j (φ t₁) ∈ K := by
      change F ((Pi.mulSingle i₁ t₂)⁻¹ * Pi.mulSingle j (φ t₁)) • a = a
      rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff]
      exact hg
    by_cases hj : j = i₁
    · subst hj
      have hz' : Pi.mulSingle j (t₂⁻¹ * φ t₁) ∈ K := by
        simpa only [Pi.mulSingle_inv, Pi.mulSingle_mul] using hz
      have heq : t₂⁻¹ * φ t₁ = 1 := hKsingle j _ hz'
      have ht₂_eq : t₂ = φ t₁ := inv_mul_eq_one.mp heq
      rw [ht₂_eq, MulEquiv.orderOf_eq]
    · have hcomm : Commute ((Pi.mulSingle i₁ t₂)⁻¹ : ∀ i, S i) (Pi.mulSingle j (φ t₁)) := by
        rw [← Pi.mulSingle_inv]
        exact Pi.mulSingle_commute (Ne.symm hj) t₂⁻¹ (φ t₁)
      have hdvd₁ : orderOf t₂ ∣ orderOf t₁ := by
        have hzpow : ((Pi.mulSingle i₁ t₂)⁻¹ * Pi.mulSingle j (φ t₁)) ^ orderOf t₁ ∈ K :=
          K.pow_mem hz (orderOf t₁)
        rw [hcomm.mul_pow, ← Pi.mulSingle_inv, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow] at hzpow
        have hφpow : (φ t₁) ^ orderOf t₁ = 1 := by
          rw [← map_pow, pow_orderOf_eq_one, map_one]
        rw [hφpow, Pi.mulSingle_one, mul_one] at hzpow
        have ht₂pow : t₂⁻¹ ^ orderOf t₁ = 1 := hKsingle i₁ _ hzpow
        rw [← orderOf_inv]
        exact orderOf_dvd_of_pow_eq_one ht₂pow
      have hdvd₂ : orderOf t₁ ∣ orderOf t₂ := by
        have hzpow : ((Pi.mulSingle i₁ t₂)⁻¹ * Pi.mulSingle j (φ t₁)) ^ orderOf t₂ ∈ K :=
          K.pow_mem hz (orderOf t₂)
        rw [hcomm.mul_pow, ← Pi.mulSingle_inv, ← Pi.mulSingle_pow, ← Pi.mulSingle_pow] at hzpow
        have ht₂pow : t₂⁻¹ ^ orderOf t₂ = 1 := by
          rw [inv_pow, pow_orderOf_eq_one, inv_one]
        rw [ht₂pow, Pi.mulSingle_one, one_mul] at hzpow
        have hφpow : (φ t₁) ^ orderOf t₂ = 1 := hKsingle j _ hzpow
        rw [← MulEquiv.orderOf_eq φ t₁]
        exact orderOf_dvd_of_pow_eq_one hφpow
      exact Nat.dvd_antisymm hdvd₂ hdvd₁
  have hcomm := IsSimpleGroup.comm_iff_isSolvable.mpr (isSolvable_of_orderOf_eq hord)
  obtain ⟨x, y, hxy⟩ := hnonab
  exact hxy (hcomm x y)

end ProductElimination

/-- Fact 3 (Burnside): Every nonabelian minimal normal subgroup of a finite faithful
2-transitive permutation group is simple. -/
theorem minimalNormal_simple_of_two_transitive
    [Finite G] [FaithfulSMul G V] [Nontrivial V]
    (h2 : WielTwoTrans G V) {N : Subgroup G} (hN : MinimalNormal N)
    (hnonab : ∃ x y : N, x * y ≠ y * x) (a : V) :
    IsSimpleGroup N := by
  letI : DecidableEq (MinimalNormals N) := Classical.decEq _
  haveI : MulAction.IsPreprimitive G V := h2.isPreprimitive
  letI : N.Normal := hN.1
  have hradG := radicalFree_of_two_transitive_nonabelian_minimalNormal h2 hN hnonab a
  have hradN := normal_subgroup_radicalFree hradG N
  have hsocN := minimalNormal_socle_eq_top hN
  letI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN.2.1
  letI : ∀ m : MinimalNormals N, IsSimpleGroup m.val :=
    fun m => minimalNormal_simple_factors hN m
  have hF_single : ∀ (m : MinimalNormals N) (x : m.val),
      normalCoordinateEmbedding N hradN hsocN (Pi.mulSingle m x) = ((x : N) : G) := by
    intro m x
    letI := Fintype.ofFinite (MinimalNormals N)
    have h1 : (GI.PrimitiveCartesian.intrinsicProductEquiv hradN hsocN (Pi.mulSingle m x) : N) = x :=
      Subgroup.noncommPiCoprod_mulSingle (hcomm := minimalNormals_commute) m x
    exact congrArg Subtype.val h1
  have hnot_all : ∀ m : MinimalNormals N,
      ∃ x : m.val, Pi.mulSingle m x ∉
        (MulAction.stabilizer G a).comap (normalCoordinateEmbedding N hradN hsocN) :=
    fun m => product_factor_not_le_stabilizer a (normalCoordinateEmbedding N hradN hsocN)
      (normalCoordinateEmbedding_injective N hradN hsocN)
      (minimalCoordinate_representatives hradG N hN a) m
  have hconj : ∀ (g : MulAction.stabilizer G a) (m : MinimalNormals N) (x : m.val),
      ∃ (j : MinimalNormals N) (φ : m.val ≃* j.val),
        (g : G) • (normalCoordinateEmbedding N hradN hsocN (Pi.mulSingle m x) • a) =
          normalCoordinateEmbedding N hradN hsocN (Pi.mulSingle j (φ x)) • a := by
    intro g m x
    let e := MulAut.conjNormal (H := N) (g : G)
    let j : MinimalNormals N := minimalNormalPerm e m
    let φ : m.val ≃* j.val := e.subgroupMap m.val
    refine ⟨j, φ, ?_⟩
    have hginv : (g : G)⁻¹ • a = a := by
      have hga : (g : G) • a = a := g.property
      calc (g : G)⁻¹ • a = (g : G)⁻¹ • ((g : G) • a) := by rw [hga]
        _ = a := inv_smul_smul (g : G) a
    rw [hF_single m x, hF_single j (φ x)]
    change (g : G) • (((x : N) : G) • a) = ((g : G) * ((x : N) : G) * (g : G)⁻¹) • a
    rw [mul_smul, mul_smul, hginv]
  haveI : Subsingleton (MinimalNormals N) := by
    by_cases hproper : ∃ i : MinimalNormals N,
        ((MulAction.stabilizer G a).comap (normalCoordinateEmbedding N hradN hsocN)).map
          (Pi.evalMonoidHom (fun M : MinimalNormals N => M.val) i) ≠ ⊤
    · obtain ⟨i, hi⟩ := hproper
      exact subsingleton_of_two_transitive_proper_envelope h2 a
        (normalCoordinateEmbedding N hradN hsocN) hnot_all
        (fun g m x => by obtain ⟨j, φ, h⟩ := hconj g m x; exact ⟨j, φ x, h⟩)
        (primitive_normal_product_stabilizer N hradN hsocN a i hi)
    · push Not at hproper
      constructor
      intro i₁ i₂
      exfalso
      exact false_of_two_transitive_subdirect h2 a
        (normalCoordinateEmbedding N hradN hsocN) i₁
        (minimalNormal_nonabelian hradN i₁.property) hnot_all hconj hproper
  letI := Fintype.ofFinite (MinimalNormals N)
  apply simple_of_socle_eq_top_count_le_one hsocN
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance

end GI.Proved
