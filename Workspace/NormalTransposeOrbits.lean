module

public import Workspace.NormalTransposeColumns

@[expose] public section

/-!
# Lemma A.14: equal column widths from the transitivity of `G`

"if the local variation group `N` is intransitive with `t` orbits of size
`u = b/t`". The paper does not prove that the `N`-orbits have one size; it follows
from the transitivity of `G`, as follows. `G = K R` with `R = s(Alt(m))` acting
purely on rows, so the block stabilizer of block `i0` is `K R_{i0}`, and `R_{i0}`
fixes the in-block coordinate of block `i0`. Hence `K`, and so the local group
`H = K[B]`, is transitive on `B`. The orbits of the normal subgroup `N ◁ H` of a
transitive group are permuted transitively by `H`, so they all have the same size.
-/

namespace GI.NormalTranspose

open Equiv GI.Paper

variable {V B I : Type*} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Perm V)} {K : Subgroup G} {e : B × I ≃ V}
variable {s : alternatingGroup I →* G}

omit [Fintype I] [DecidableEq I] in
/-- An element of `G` that preserves every block is a clean row permutation, and its
component at `i0` lies in the local group `H = K[B]`. -/
theorem local_component (i0 : I) (k : G) (hk : ∀ b i, (e.symm (k.val (e (b, i)))).2 = i) :
    ∃ h : cleanLocalGroup G e i0, ∀ b, e ((h : Perm B) b, i0) = k.val (e (b, i0)) := by
  let P : Perm (B × I) := (e.trans k.val).trans e.symm
  have hP : ∀ z, (P z).2 = z.2 := fun z => hk z.1 z.2
  let x := GI.rowComponents P hP
  have hx : cleanRowPerm e x = k.val := by
    change relabelPerm e (GI.rowCoordinatePerm x) = k.val
    rw [GI.rowCoordinatePerm_components P hP]
    ext v
    change e (e.symm (k.val (e (e.symm v)))) = k.val v
    simp
  refine ⟨⟨x i0, ⟨x, by change cleanRowPerm e x ∈ G; rw [hx]; exact k.property, rfl⟩⟩,
    fun b => ?_⟩
  change e ((e.symm (k.val (e (b, i0)))).1, i0) = k.val (e (b, i0))
  have h2 := hk b i0
  conv_rhs => rw [← e.apply_symm_apply (k.val (e (b, i0)))]
  congr 1
  exact Prod.ext rfl h2.symm

/-- **The local group is transitive.** If `G` is transitive on `V`, `G = K R` with
`K` preserving every block, and `R = s(Alt(m))` acts purely on rows, then
`H = K[B]` is transitive on `B`. -/
theorem local_transitive (i0 : I)
    (hpure : ∀ p b i, (s p).val (e (b, i)) = e (b, p.val i))
    (hK : ∀ k ∈ K, ∀ b i, (e.symm (k.val (e (b, i)))).2 = i)
    (hcompl : K.IsComplement' s.range)
    (htrans : ∀ v w : V, ∃ g : G, g.val v = w) (b b' : B) :
    ∃ h : cleanLocalGroup G e i0, (h : Perm B) b = b' := by
  obtain ⟨g, hg⟩ := htrans (e (b, i0)) (e (b', i0))
  obtain ⟨⟨⟨k, hkK⟩, ⟨r, p, rfl⟩⟩, hkr⟩ := hcompl.2 g
  simp only at hkr
  -- `g = k s(p)`: `s(p)` moves `e(b, i0)` to `e(b, p i0)`, and `k` keeps the row.
  have hrow := hK k hkK b (p.val i0)
  have hgk : k.val (e (b, p.val i0)) = e (b', i0) := by
    rw [← hpure p b i0, ← hg, ← hkr]
    rfl
  rw [hgk, e.symm_apply_apply] at hrow
  -- so `p` fixes `i0`, and `k` moves `e(b, i0)` to `e(b', i0)`
  rw [← hrow] at hgk
  obtain ⟨h, hh⟩ := local_component i0 k (hK k hkK)
  refine ⟨h, ?_⟩
  have := (hh b).trans hgk
  exact congrArg Prod.fst (e.injective this)

variable [Finite B]

/-- The orbits of a normal subgroup of a transitive group have one size. -/
theorem normal_orbit_ncard_eq {H : Subgroup (Perm B)} (N : Subgroup H) [N.Normal]
    (htrans : ∀ b b' : B, ∃ h : H, (h : Perm B) b = b') (b b' : B) :
    (MulAction.orbit N b).ncard = (MulAction.orbit N b').ncard := by
  have key : ∀ b b' : B, (MulAction.orbit N b).ncard ≤ (MulAction.orbit N b').ncard := by
    intro b b'
    obtain ⟨h, rfl⟩ := htrans b b'
    have hsub : (fun c => (h : Perm B) c) '' MulAction.orbit N b ⊆
        MulAction.orbit N ((h : Perm B) b) := by
      rintro _ ⟨c, ⟨n, rfl⟩, rfl⟩
      let n' : N := ⟨h * n.val * h⁻¹, ‹N.Normal›.conj_mem _ n.property h⟩
      refine ⟨n', ?_⟩
      change ((h * n.val * h⁻¹ : H) : Perm B) ((h : Perm B) b) = (h : Perm B) ((n.val : Perm B) b)
      simp [Perm.mul_apply]
    calc (MulAction.orbit N b).ncard
        = ((fun c => (h : Perm B) c) '' MulAction.orbit N b).ncard :=
          (Set.ncard_image_of_injective _ (h : Perm B).injective).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  exact le_antisymm (key b b') (key b' b)

/-- **Equal column widths `u = b/t`.** If all orbits of `N` have the same size `u`,
then every class of the orbit quotient has `u` points and `t u = b`, with `t` the
number of orbits. -/
theorem orbit_count_mul {H : Subgroup (Perm B)} (N : Subgroup H) [N.Normal]
    (htrans : ∀ b b' : B, ∃ h : H, (h : Perm B) b = b') (b₀ : B) :
    (∀ C : Quotient (MulAction.orbitRel N B),
      Nat.card {b : B // Quotient.mk _ b = C} = (MulAction.orbit N b₀).ncard) ∧
    Nat.card (Quotient (MulAction.orbitRel N B)) * (MulAction.orbit N b₀).ncard = Nat.card B := by
  classical
  haveI := Fintype.ofFinite B
  have fiber : ∀ C : Quotient (MulAction.orbitRel N B),
      Nat.card {b : B // Quotient.mk _ b = C} = (MulAction.orbit N b₀).ncard := by
    intro C
    induction C using Quotient.inductionOn with
    | h c =>
      rw [← normal_orbit_ncard_eq N htrans c b₀, ← Nat.card_coe_set_eq]
      apply Nat.card_congr
      refine Equiv.subtypeEquivRight fun b => ?_
      rw [Quotient.eq]
      exact Iff.rfl
  refine ⟨fiber, ?_⟩
  haveI : Fintype (Quotient (MulAction.orbitRel N B)) := Fintype.ofFinite _
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv
    (fun b : B => (Quotient.mk _ b : Quotient (MulAction.orbitRel N B))))
  rw [Fintype.card_sigma] at h
  have hc : ∀ C : Quotient (MulAction.orbitRel N B),
      Fintype.card {b : B // (Quotient.mk _ b : Quotient (MulAction.orbitRel N B)) = C} =
        (MulAction.orbit N b₀).ncard := by
    intro C
    rw [← Nat.card_eq_fintype_card]
    exact fiber C
  simp_rw [hc] at h
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, h]

end GI.NormalTranspose
