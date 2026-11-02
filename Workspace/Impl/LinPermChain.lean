import Workspace.Impl.LinCoordinateCertificate
import Workspace.Impl.LinIntPrefix

/-! Relate the permutation prefix values to the chains inside A. This is needed
because N is normal in A, not necessarily in the ambient symmetric group. -/
namespace GI.Impl
open GI.Cited
open scoped commutatorElement

theorem linChain_map {G H : Type*} [Group G] [Group H] (f : G →* H)
    (N : Subgroup G) (as : List G) (i : ℕ) :
    (linChain N as i).map f = linChain (N.map f) (as.map f) i := by
  rw [linChain, Subgroup.map_sup, MonoidHom.map_closure, linChain]
  congr 1
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, ← List.map_take, List.mem_map]

/-- An injective change of ambient group preserves the computed cyclic indices. -/
theorem linChain_relIndex_map {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Injective f) (N : Subgroup G) (as : List G) (i : ℕ) :
    (linChain N as i).relIndex (linChain N as (i + 1)) =
      (linChain (N.map f) (as.map f) i).relIndex (linChain (N.map f) (as.map f) (i + 1)) := by
  rw [← linChain_map, ← linChain_map]
  rw [linChain_orderRatio _ _ (linChain_mono N as (Nat.le_succ i)),
    linChain_orderRatio _ _ (Subgroup.map_mono (linChain_mono N as (Nat.le_succ i)))]
  rw [Subgroup.card_map_of_injective hf, Subgroup.card_map_of_injective hf]

/-- Every quotient is commutative when the kernel contains all commutators. -/
theorem linQuotient_comm {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hc : ∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ N) : IsMulCommutative (G ⧸ N) := by
  refine ⟨⟨?_⟩⟩
  intro x y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N y
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr (hc a b)

/-- The prefix power in the ambient permutation group really belongs to the
preceding prefix, using normality only inside A. -/
theorem linPermChain_power {n : ℕ} (A : Subgroup (Equiv.Perm (Fin n)))
    (ns as : List (Equiv.Perm (Fin n))) (hn : gens ns ≤ A)
    (ha : ∀ a ∈ as, a ∈ A)
    (hc : ∀ x y : A, (x : Equiv.Perm (Fin n)) * y * x⁻¹ * y⁻¹ ∈ gens ns)
    (i : ℕ) (hi : i < as.length) :
    as[i] ^ (linChain (gens ns) as i).relIndex (linChain (gens ns) as (i + 1)) ∈
      gens (ns ++ as.take i) := by
  let N := (gens ns).subgroupOf A
  let bs := linSubgroupGenerators A as ha
  have hbs : bs.map A.subtype = as := linSubgroupGenerators_map A as ha
  have hN : N.map A.subtype = gens ns := Subgroup.map_subgroupOf_eq_of_le hn
  have hcomm : ∀ x y : A, x * y * x⁻¹ * y⁻¹ ∈ N := hc
  have hlen : bs.length = as.length := by have := congrArg List.length hbs; simpa using this
  have hib : i < bs.length := by omega
  have hp := linChain_power N bs hcomm i hib
  have hidx := linChain_relIndex_map A.subtype Subtype.val_injective N bs i
  rw [hN, hbs] at hidx
  have hmap : (linChain N bs i).map A.subtype = linChain (gens ns) as i := by
    rw [linChain_map, hN, hbs]
  have helem : A.subtype bs[i] = as[i] := by
    have hh := congrArg (fun l => l[i]?) hbs
    simpa only [List.getElem?_map, List.getElem?_eq_getElem hib,
      List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] using hh
  have hh : as[i] ^ (linChain (gens ns) as i).relIndex (linChain (gens ns) as (i + 1)) ∈
      (linChain N bs i).map A.subtype := by
    refine ⟨bs[i] ^ (linChain N bs i).relIndex (linChain N bs (i + 1)), hp, ?_⟩
    rw [map_pow, helem, hidx]
  rw [hmap] at hh
  simpa only [linPrefix_gens ns as i] using hh

end GI.Impl
