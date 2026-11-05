module

public import Workspace.Proved.VsTBasic

@[expose] public section

/-!
# LM Lemma 5.2 without irreducibility

Let `A` be an abelian normal subgroup of a linear group `G` on a finite-dimensional space `V`
over `ZMod p`, and let `B = 𝔽_p[A]` be the algebra spanned by `A` in `End V`. LM Lemma 5.2
assumes that `G` is irreducible and `A` cyclic. We assume instead that every nonzero element
of `B` is injective (`vsTDom`). This is what Step 1 of LM Proposition 5.12 gives when it does
not end with a decomposition or a proper submodule (`vsFField_of_top`).

* `vsT_card_roots`: in such a `B`, a nonzero polynomial `q` has at most `deg q` roots, because
  `B` is a commutative domain.
* `vsT_cyclic`: `A` is cyclic (a finite subgroup of the units of a domain).
* `vsT_index_centralizer`: `|G : C_G(A)| ≤ dim V`. With `A = ⟨a⟩`, the conjugates `g a g⁻¹`
  lie in `A ⊆ B` and are roots of the characteristic polynomial of `a`, of degree `dim V`.
-/

namespace GI.Proved

open Module Polynomial
open scoped IsMulCommutative

variable {p : ℕ} [hp : Fact p.Prime] {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- The elements of `A`, as endomorphisms. -/
def vsTSet (A : Subgroup (End (ZMod p) V)ˣ) : Set (End (ZMod p) V) :=
  (fun a : (End (ZMod p) V)ˣ => (a : End (ZMod p) V)) '' (A : Set (End (ZMod p) V)ˣ)

/-- The algebra `B = 𝔽_p[A]` spanned by `A`. -/
def vsTAlg (A : Subgroup (End (ZMod p) V)ˣ) : Subalgebra (ZMod p) (End (ZMod p) V) :=
  Algebra.adjoin (ZMod p) (vsTSet A)

/-- Every nonzero element of `B` is injective. -/
def vsTDom (B : Subalgebra (ZMod p) (End (ZMod p) V)) : Prop :=
  ∀ b ∈ B, b = 0 ∨ ∀ v, b v = 0 → v = 0

theorem vsTSet_comm {A : Subgroup (End (ZMod p) V)ˣ} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    ∀ x ∈ vsTSet A, ∀ y ∈ vsTSet A, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← Units.val_mul, hA a ha b hb, Units.val_mul]

theorem VsTAbNormal.conj_mem {G A : Subgroup (End (ZMod p) V)ˣ} (hA : VsTAbNormal G A)
    {g a : (End (ZMod p) V)ˣ} (hg : g ∈ G) (ha : a ∈ A) : g * a * g⁻¹ ∈ A := by
  have h := hA.2.1.conj_mem ⟨a, hA.1 ha⟩ (by simpa [Subgroup.mem_subgroupOf] using ha) ⟨g, hg⟩
  simpa [Subgroup.mem_subgroupOf] using h

/-- `aeval` commutes with conjugation by a unit. -/
theorem vsT_aeval_conj (u : (End (ZMod p) V)ˣ) (x : End (ZMod p) V) (q : (ZMod p)[X]) :
    aeval ((u : End (ZMod p) V) * x * ↑u⁻¹) q = u * aeval x q * ↑u⁻¹ := by
  induction q using Polynomial.induction_on' with
  | add q r hq hr => rw [map_add, map_add, hq, hr, mul_add, add_mul]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Units.conj_pow, ← Algebra.smul_def, ← Algebra.smul_def,
      mul_smul_comm, smul_mul_assoc]

/-- In a commutative algebra `adjoin s` whose nonzero elements are injective, a nonzero
polynomial `q` has at most `deg q` roots. Such an algebra is a commutative domain, and there the
roots of `q` form a multiset of size at most `deg q` (`Polynomial.card_roots'`). -/
theorem vsT_card_roots [FiniteDimensional (ZMod p) V] [Nontrivial V] {s : Set (End (ZMod p) V)}
    (hs : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (hdom : vsTDom (Algebra.adjoin (ZMod p) s))
    {q : (ZMod p)[X]} (hq : q ≠ 0) :
    Set.ncard {x : End (ZMod p) V | x ∈ Algebra.adjoin (ZMod p) s ∧ aeval x q = 0} ≤
      q.natDegree := by
  classical
  haveI : IsMulCommutative (Algebra.adjoin (ZMod p) s) := Algebra.isMulCommutative_adjoin (ZMod p) (fun x hx y hy _ => hs x hx y hy)
  set R := Algebra.adjoin (ZMod p) s
  haveI : Nontrivial R := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 : ((0 : R) : End (ZMod p) V) = ((1 : R) : End (ZMod p) V) := congrArg Subtype.val h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    have h2 := congrArg (fun f : End (ZMod p) V => f v) h1
    simpa using h2.symm
  haveI : NoZeroDivisors R := by
    refine ⟨fun {x y} hxy => ?_⟩
    rcases hdom x.1 x.2 with hx | hx
    · exact Or.inl (Subtype.ext hx)
    · right
      apply Subtype.ext
      ext v
      have h1 := congrArg (fun z : R => (z : End (ZMod p) V) v) hxy
      exact hx _ (by simpa using h1)
  haveI : IsDomain R := NoZeroDivisors.to_isDomain R
  set Q : R[X] := q.map (algebraMap (ZMod p) R)
  have hQ : Q ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap (ZMod p) R).injective).2 hq
  have hsub : {x : End (ZMod p) V | x ∈ R ∧ aeval x q = 0} ⊆
      (fun r : R => (r : End (ZMod p) V)) '' ((Q.roots.toFinset : Finset R) : Set R) := by
    rintro x ⟨hxR, hx0⟩
    refine ⟨⟨x, hxR⟩, ?_, rfl⟩
    rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hQ, IsRoot, eval_map_algebraMap]
    apply Subtype.ext
    rw [aeval_subalgebra_coe]
    exact hx0
  calc Set.ncard {x : End (ZMod p) V | x ∈ R ∧ aeval x q = 0}
      ≤ Set.ncard ((fun r : R => (r : End (ZMod p) V)) '' ((Q.roots.toFinset : Finset R) : Set R)) :=
        Set.ncard_le_ncard hsub ((Finset.finite_toSet _).image _)
    _ ≤ Set.ncard ((Q.roots.toFinset : Finset R) : Set R) := Set.ncard_image_le (Finset.finite_toSet _)
    _ = Q.roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card Q.roots := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := card_roots' Q
    _ ≤ q.natDegree := natDegree_map_le

/-- `A` is cyclic: it embeds in the units of the commutative domain `B`. -/
theorem vsT_cyclic [FiniteDimensional (ZMod p) V] [Nontrivial V]
    {A : Subgroup (End (ZMod p) V)ˣ} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hdom : vsTDom (vsTAlg A)) : IsCyclic A := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI : IsMulCommutative (vsTAlg A) :=
    Algebra.isMulCommutative_adjoin (ZMod p) (fun x hx y hy _ => vsTSet_comm hA x hx y hy)
  set R := vsTAlg A
  haveI : Nontrivial R := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 : ((0 : R) : End (ZMod p) V) = ((1 : R) : End (ZMod p) V) := congrArg Subtype.val h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    have h2 := congrArg (fun f : End (ZMod p) V => f v) h1
    simpa using h2.symm
  haveI : NoZeroDivisors R := by
    refine ⟨fun {x y} hxy => ?_⟩
    rcases hdom x.1 x.2 with hx | hx
    · exact Or.inl (Subtype.ext hx)
    · right
      apply Subtype.ext
      ext v
      have h1 := congrArg (fun z : R => (z : End (ZMod p) V) v) hxy
      exact hx _ (by simpa using h1)
  haveI : IsDomain R := NoZeroDivisors.to_isDomain R
  have hmem : ∀ a : A, ((a : (End (ZMod p) V)ˣ) : End (ZMod p) V) ∈ R := fun a =>
    Algebra.subset_adjoin ⟨a, a.2, rfl⟩
  let f : A →* R :=
    { toFun := fun a => ⟨_, hmem a⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hf : Function.Injective f := by
    intro a b hab
    have h := congrArg (fun u : R => (u : End (ZMod p) V)) hab
    exact Subtype.ext (Units.ext h)
  exact isCyclic_of_injective_ringHom f hf

/-- **LM Lemma 5.2, domain form.** If `A ≤ G` is abelian and normal and every nonzero element
of `𝔽_p[A]` is injective, then `|G : C_G(A)| ≤ dim V`. Let `A = ⟨a⟩` (`vsT_cyclic`). Let `G`
act on `End V` by conjugation. The stabilizer of `a` lies in `C_G(A)`, and the orbit of `a` lies
in the set of roots in `𝔽_p[A]` of the characteristic polynomial `χ` of `a`
(`χ(g a g⁻¹) = g χ(a) g⁻¹ = 0`). By `vsT_card_roots` it has at most `deg χ = dim V`
elements. -/
theorem vsT_index_centralizer [FiniteDimensional (ZMod p) V] [Nontrivial V]
    {G A : Subgroup (End (ZMod p) V)ˣ} (hA : VsTAbNormal G A) (hdom : vsTDom (vsTAlg A)) :
    (Subgroup.centralizer (A : Set (End (ZMod p) V)ˣ)).relIndex G ≤ finrank (ZMod p) V := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI := vsT_cyclic hA.2.2 hdom
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := A)
  set a' : G := ⟨a, hA.1 a.2⟩
  set S := (MulAction.stabilizer (ConjAct G) a').comap
    (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom
  -- the stabilizer of `a` lies in the centralizer
  have hstab : S ≤ (Subgroup.centralizer (A : Set (End (ZMod p) V)ˣ)).subgroupOf G := by
    intro g hg
    rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff] at hg
    change ConjAct.toConjAct g • a' = a' at hg
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at hg
    have hc : (g : (End (ZMod p) V)ˣ) * a = a * g := by
      have h := congrArg (fun x : G => (x : (End (ZMod p) V)ˣ)) hg
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, a'] at h
      exact mul_inv_eq_iff_eq_mul.1 h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (ha ⟨h, hh⟩)
    have hk' : h = (a : (End (ZMod p) V)ˣ) ^ k := by
      rw [← Subgroup.coe_zpow, hk]
    rw [hk']
    exact ((Commute.zpow_left hc.symm k).symm).eq.symm
  -- the orbit of `a` consists of roots of the characteristic polynomial of `a`
  set a0 : End (ZMod p) V := ((a : (End (ZMod p) V)ˣ) : End (ZMod p) V)
  set χ := LinearMap.charpoly a0
  set e : G → End (ZMod p) V := fun x => ((x : (End (ZMod p) V)ˣ) : End (ZMod p) V)
  have he : Function.Injective e := fun x y h => Subtype.ext (Units.ext h)
  have horb : e '' MulAction.orbit (ConjAct G) a' ⊆
      {x : End (ZMod p) V | x ∈ vsTAlg A ∧ aeval x χ = 0} := by
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    have hx : e (g • a') = ((ConjAct.ofConjAct g : G) : (End (ZMod p) V)ˣ) * a0 *
        ↑((ConjAct.ofConjAct g : G) : (End (ZMod p) V)ˣ)⁻¹ := by
      simp only [e, ConjAct.smul_def]
      rfl
    rw [hx]
    refine ⟨Algebra.subset_adjoin ⟨_, hA.conj_mem (ConjAct.ofConjAct g).2 a.2, by simp [a0]⟩, ?_⟩
    rw [vsT_aeval_conj, LinearMap.aeval_self_charpoly, mul_zero, zero_mul]
  have hcard := vsT_card_roots (vsTSet_comm hA.2.2) hdom (LinearMap.charpoly_monic a0).ne_zero
  rw [LinearMap.charpoly_natDegree] at hcard
  have hfin : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  calc (Subgroup.centralizer (A : Set (End (ZMod p) V)ˣ)).relIndex G
      ≤ S.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hfin) (Subgroup.index_dvd_of_le hstab)
    _ = (MulAction.stabilizer (ConjAct G) a').index :=
        Subgroup.index_comap_of_surjective _ (ConjAct.toConjAct : G ≃* ConjAct G).surjective
    _ = (MulAction.orbit (ConjAct G) a').ncard := MulAction.index_stabilizer _ _
    _ = (e '' MulAction.orbit (ConjAct G) a').ncard := (Set.ncard_image_of_injective _ he).symm
    _ ≤ _ := (Set.ncard_le_ncard horb (Set.toFinite _)).trans hcard

end GI.Proved
