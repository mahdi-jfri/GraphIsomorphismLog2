module

public import Workspace.PrimitiveAbelianNormal
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Module.ZMod

@[expose] public section

namespace GI.PrimitiveStructure

variable {G V : Type*} [Group G] [MulAction G V] [FaithfulSMul G V]

omit [FaithfulSMul G V] in
/-- A transitive subgroup of a group acting regularly is the whole group. -/
theorem eq_of_transitive_le_regular (N K : Subgroup G) (hle : K ≤ N)
    [MulAction.IsPretransitive K V] (a : V)
    (free : Function.Injective (fun n : N => n • a)) : K = N := by
  apply le_antisymm hle
  intro n hn
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K a ((⟨n, hn⟩ : N) • a)
  have he : Subgroup.inclusion hle k = ⟨n, hn⟩ := free hk
  have hv : (k : G) = n := congrArg Subtype.val he
  exact hv ▸ k.property

/-- The actual p-torsion subgroup of an abelian subgroup, viewed in the
ambient group. Its construction does not assume an elementary abelian model. -/
def abelianTorsion (N : Subgroup G) (comm : ∀ x y : N, x * y = y * x)
    (p : ℕ) : Subgroup G where
  carrier := {g | g ∈ N ∧ g ^ p = 1}
  one_mem' := ⟨N.one_mem, one_pow p⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨N.mul_mem hx.1 hy.1, ?_⟩
    have hcomm : Commute x y := congrArg Subtype.val (comm ⟨x, hx.1⟩ ⟨y, hy.1⟩)
    rw [hcomm.mul_pow, hx.2, hy.2, one_mul]
  inv_mem' := by
    intro x hx
    exact ⟨N.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem abelianTorsion_normal (N : Subgroup G) [N.Normal]
    (comm : ∀ x y : N, x * y = y * x) (p : ℕ) :
    (abelianTorsion N comm p).Normal := by
  constructor
  intro x hx g
  refine ⟨(inferInstance : N.Normal).conj_mem x hx.1 g, ?_⟩
  change ((MulAut.conj g) x) ^ p = 1
  rw [← map_pow, hx.2, map_one]

/-- Every nontrivial abelian normal subgroup of a finite faithful
primitive group has prime exponent. This proves the elementary abelian
part of the affine-type recognition without a classification theorem. -/
theorem abelian_normal_prime_exponent [Finite G] [MulAction.IsPreprimitive G V]
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊥)
    (comm : ∀ x y : N, x * y = y * x) (a : V) :
    ∃ p : ℕ, p.Prime ∧ ∀ x : N, x ^ p = 1 := by
  letI : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hne
  have hcard : Nat.card N ≠ 1 := by
    intro hc
    letI : Subsingleton N := (Nat.card_eq_one_iff_unique.mp hc).1
    obtain ⟨x, hx⟩ := exists_ne (1 : N)
    exact hx (Subsingleton.elim _ _)
  obtain ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd hcard
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := N) p hdvd
  let K := abelianTorsion N comm p
  letI : K.Normal := abelianTorsion_normal N comm p
  have hxpow : (x : G) ^ p = 1 := by
    have hh : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
    exact congrArg Subtype.val hh
  have hKne : K ≠ ⊥ := by
    intro heq
    have hxK : (x : G) ∈ K := ⟨x.property, hxpow⟩
    rw [heq] at hxK
    have hxone : x = 1 := Subtype.ext (Subgroup.mem_bot.mp hxK)
    have hpone : p = 1 := by simpa only [hxone, orderOf_one] using hx.symm
    exact hp.ne_one hpone
  letI : MulAction.IsPretransitive K V := normal_pretransitive K hKne
  have hKN : K = N := eq_of_transitive_le_regular N K (fun _ h => h.1) a
    (abelian_normal_regular N hne comm a).injective
  refine ⟨p, hp, fun y => ?_⟩
  apply Subtype.ext
  have hy : (y : G) ∈ K := hKN.symm ▸ y.property
  exact hy.2

end GI.PrimitiveStructure
