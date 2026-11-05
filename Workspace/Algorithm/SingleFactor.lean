module

public import Workspace.Algorithm.Dispatch

@[expose] public section

/-!
# The single-factor normalization

Algorithm 5: "Normalize the single alternating factor, with at most two cosets." Section 6.1:
"The single-factor normalization has index at most two above the bounded exceptional degrees.
Its preimage is normal."

When the primitive quotient of a state is a single factor (`PrimitiveQuotient.SingleFactor`:
Maróti's case (i) with one coordinate), its image `ρ(G)` acts on the `k`-subsets of `[m]` as a
group of permutations of `[m]` that contains `Alt(m)`. This file builds the `Normalization`
(`PrimitiveQuotient.normalization`):

* the action on `k`-subsets is faithful for `0 < k < m` (`Product.kSetPerm_injective`), so
  each element of `ρ(G)` comes from one permutation of `[m]`, and this is a homomorphism
  `φ : ρ(G) → Sym(m)`;
* the normalized group `G'` is the preimage of `Alt(m)` under `φ ∘ ρ`; it is normal in `G`, and
  its index is at most two, since it is the kernel of `sign ∘ φ ∘ ρ`;
* `G'` maps onto `Alt(m)`, since `ρ(G)` contains the image of `Alt(m)`.

No cited result is used here (the single-factor case itself comes from Maróti's theorem in the
dispatcher).
-/

namespace GI.Algorithm

open Equiv Equiv.Perm

namespace Product

/-- **The action on `k`-subsets is faithful** for `0 < k < m`: if `a` moves `i` to `j`, a
`k`-subset that contains `i` and not `j` is moved. -/
theorem kSetPerm_injective {m k : ℕ} (hk : 0 < k) (hkm : k < m) {a b : Perm (Fin m)}
    (h : ∀ A : KSet m k, GI.Cited.kSetPerm a A = GI.Cited.kSetPerm b A) : a = b := by
  classical
  by_contra hab
  set c := b⁻¹ * a with hc
  have hc1 : c ≠ 1 := by
    intro h1
    apply hab
    have : b * c = b := by rw [h1, mul_one]
    rw [hc, ← mul_assoc, mul_inv_cancel, one_mul] at this
    exact this
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ i := by
    by_contra hall
    push Not at hall
    exact hc1 (Equiv.ext hall)
  set j := c i
  set U : Finset (Fin m) := (Finset.univ.erase i).erase j
  have hU : k - 1 ≤ U.card := by
    have h1 : U.card = m - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    omega
  obtain ⟨T, hTU, hTc⟩ := Finset.exists_subset_card_eq hU
  have hiT : i ∉ T := fun h => by
    have := hTU h
    simp [U] at this
  have hjT : j ∉ T := fun h => by
    have := hTU h
    simp [U] at this
  let A : KSet m k := ⟨insert i T, by rw [Finset.card_insert_of_notMem hiT, hTc]; omega⟩
  have hfix : GI.Cited.kSetPerm c A = A := by
    rw [hc, kSetPerm_mul, h A, ← kSetPerm_mul, inv_mul_cancel, kSetPerm_one]
  have hj : j ∈ (GI.Cited.kSetPerm c A).1 := by
    change c i ∈ (insert i T).map c.toEmbedding
    exact Finset.mem_map_of_mem _ (Finset.mem_insert_self _ _)
  rw [hfix] at hj
  rcases Finset.mem_insert.1 hj with h' | h'
  · exact hi h'
  · exact hjT h'

end Product

namespace PrimitiveQuotient

variable {Ω C : Type} {S : State Ω C} (Q : PrimitiveQuotient S)

section OneCoordinate

variable {m k : ℕ} (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)) (hS : Q.ProductStructure m k 1 e)

include hS in
/-- Every element of `ρ(G)` acts on the one coordinate by a permutation of `[m]`. -/
theorem exists_perm (x : Perm (Fin Q.d)) (hx : x ∈ Q.ρ.range) :
    ∃ h : Perm (Fin m), Product.IsProd e x 1 fun _ => h := by
  obtain ⟨σ, h, hh⟩ := hS.1 x hx
  have hσ : σ = 1 := Subsingleton.elim _ _
  subst hσ
  refine ⟨h 0, ?_⟩
  have : h = fun _ => h 0 := funext fun i => by rw [Subsingleton.elim i 0]
  rw [← this]
  exact hh

/-- The permutation of `[m]` is unique, since the action on `k`-subsets is faithful. -/
theorem perm_unique {x : Perm (Fin Q.d)} {h h' : Perm (Fin m)}
    (hh : Product.IsProd e x 1 fun _ => h) (hh' : Product.IsProd e x 1 fun _ => h') : h = h' := by
  have hb := Q.two_le_choose e
  have hk0 : k ≠ 0 := by rintro rfl; simp at hb
  have hkm : k < m := by
    by_contra hkm
    rcases Nat.lt_or_ge m k with hlt | hge
    · rw [Nat.choose_eq_zero_of_lt hlt] at hb; omega
    · have : k = m := by omega
      subst this
      simp at hb
  refine Product.kSetPerm_injective (Nat.pos_of_ne_zero hk0) hkm fun A => ?_
  have e1 := congrFun (hh (e.symm fun _ => A)) 0
  have e2 := congrFun (hh' (e.symm fun _ => A)) 0
  simp only [Equiv.apply_symm_apply, Perm.one_apply] at e1 e2
  exact e1.symm.trans e2

/-- The permutation of `[m]` of an element of `ρ(G)`. -/
noncomputable def permOf (x : Q.ρ.range) : Perm (Fin m) := (Q.exists_perm e hS x.1 x.2).choose

theorem permOf_spec (x : Q.ρ.range) : Product.IsProd e x.1 1 fun _ => Q.permOf e hS x :=
  (Q.exists_perm e hS x.1 x.2).choose_spec

/-- `φ : ρ(G) → Sym(m)` is a homomorphism. -/
noncomputable def permHom : Q.ρ.range →* Perm (Fin m) where
  toFun := Q.permOf e hS
  map_one' := Q.perm_unique e (Q.permOf_spec e hS 1) (Product.isProd_one e)
  map_mul' x y := by
    have h := Product.isProd_mul (Q.permOf_spec e hS x) (Q.permOf_spec e hS y)
    rw [mul_one] at h
    exact Q.perm_unique e (Q.permOf_spec e hS (x * y)) h

/-- The kernel of `sign ∘ φ ∘ ρ`: the elements that act on `[m]` by even permutations. -/
noncomputable def evenPart : Subgroup S.G :=
  (Perm.sign.comp ((Q.permHom e hS).comp Q.ρ.rangeRestrict)).ker

/-- **The normalized group** `G'`, as a subgroup of `Sym(Ω)`. -/
noncomputable def normGroup : Subgroup (Perm Ω) := (Q.evenPart e hS).map S.G.subtype

theorem normGroup_le : Q.normGroup e hS ≤ S.G := Subgroup.map_subtype_le _

theorem normGroup_subgroupOf : (Q.normGroup e hS).subgroupOf S.G = Q.evenPart e hS := by
  ext g
  simp [normGroup, Subgroup.mem_subgroupOf]

theorem sign_of_mem {g : Perm Ω} (hg : g ∈ Q.normGroup e hS) :
    Perm.sign (Q.permHom e hS (Q.ρ.rangeRestrict ⟨g, Q.normGroup_le e hS hg⟩)) = 1 := by
  obtain ⟨x, hx, rfl⟩ := hg
  exact hx

/-- The map `G' → Alt(m)`. -/
noncomputable def normPi : Q.normGroup e hS →* alternatingGroup (Fin m) where
  toFun g := ⟨Q.permHom e hS (Q.ρ.rangeRestrict ⟨g.1, Q.normGroup_le e hS g.2⟩),
    Perm.mem_alternatingGroup.2 (Q.sign_of_mem e hS g.2)⟩
  map_one' := by
    apply Subtype.ext
    show Q.permHom e hS (Q.ρ.rangeRestrict 1) = 1
    simp
  map_mul' g h := by
    apply Subtype.ext
    show Q.permHom e hS (Q.ρ.rangeRestrict (⟨g.1, Q.normGroup_le e hS g.2⟩ *
      ⟨h.1, Q.normGroup_le e hS h.2⟩)) = _
    rw [map_mul, map_mul]
    rfl

theorem normPi_surjective : Function.Surjective (Q.normPi e hS) := by
  intro a
  obtain ⟨x, hx⟩ := hS.2 (fun _ => a.1) (fun _ => a.2)
  have hprod : Product.IsProd e (Q.ρ x) 1 fun _ => a.1 := by
    intro y
    rw [hx]
    funext i
    simp [Equiv.piCongrRight]
  have hφ : Q.permHom e hS (Q.ρ.rangeRestrict x) = a.1 :=
    Q.perm_unique e (Q.permOf_spec e hS (Q.ρ.rangeRestrict x)) hprod
  have hmem : x ∈ Q.evenPart e hS := by
    change Perm.sign (Q.permHom e hS (Q.ρ.rangeRestrict x)) = 1
    rw [hφ]
    exact Perm.mem_alternatingGroup.1 a.2
  refine ⟨⟨x.1, x, hmem, rfl⟩, Subtype.ext ?_⟩
  exact hφ

theorem index_le_two : ((Q.normGroup e hS).subgroupOf S.G).index ≤ 2 := by
  rw [Q.normGroup_subgroupOf, evenPart, Subgroup.index_ker]
  calc Nat.card (Perm.sign.comp ((Q.permHom e hS).comp Q.ρ.rangeRestrict)).range
      ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = 2 := by rw [Nat.card_eq_fintype_card]; rfl

end OneCoordinate

open scoped Pointwise in
/-- **The choices of a single-factor normalization.** The paper normalizes "the single
alternating factor" of a primitive quotient and branches over "at most two cosets"; it does
not fix how the quotient is written as a product with one coordinate, nor the coset
representatives. A choice is any product structure `e` with one coordinate (`ProductStructure`)
and any representatives `τ` of the cosets of the normalized group `G'` in `G`. The normalized
group does not depend on `e`: it is the kernel of the sign of the block permutation. The labels
`π` depend on `e` only through a relabeling of the `m` points. -/
structure NormChoice where
  m : ℕ
  k : ℕ
  e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)
  hS : Q.ProductStructure m k 1 e
  /-- The coset representatives. -/
  τ : Fin ((Q.normGroup e hS).subgroupOf S.G).index → Perm Ω
  τ_mem : ∀ j, τ j ∈ S.G
  cover : (S.G : Set (Perm Ω)) ⊆ ⋃ j, τ j • (Q.normGroup e hS : Set (Perm Ω))

/-- **The single-factor normalization of a choice** (Algorithm 5: "Normalize the single
alternating factor, with at most two cosets"; Section 6.1: "The single-factor normalization has
index at most two … Its preimage is normal"): the preimage `G'` of `Alt(m)` maps onto `Alt(m)`,
is normal in `G`, and has at most two cosets in `G`. -/
noncomputable def normalizationOf (c : Q.NormChoice) : Normalization S :=
  { G' := Q.normGroup c.e c.hS
    le := Q.normGroup_le c.e c.hS
    normal := by rw [Q.normGroup_subgroupOf]; exact MonoidHom.normal_ker _
    k := ((Q.normGroup c.e c.hS).subgroupOf S.G).index
    k_le := Q.index_le_two c.e c.hS
    τ := c.τ
    τ_mem := c.τ_mem
    cover := c.cover
    q := c.m
    π := Q.normPi c.e c.hS
    π_surj := Q.normPi_surjective c.e c.hS
    hier' := Q.pre ++ Q.top :: Q.post
    rho_le := Q.rho_le
    Q_le := Q.Q_le
    drop := Q.drop }

/-- The default choice: a product structure given by `SingleFactor`, and representatives given
by `exists_coset_cover`. -/
noncomputable def defaultChoice [Finite Ω] (h : Q.SingleFactor) : Q.NormChoice where
  m := h.choose
  k := h.choose_spec.choose
  e := h.choose_spec.choose_spec.choose
  hS := h.choose_spec.choose_spec.choose_spec
  τ := (CitedInstances.exists_coset_cover S.G (Q.normGroup _ h.choose_spec.choose_spec.choose_spec)).choose
  τ_mem := (CitedInstances.exists_coset_cover S.G
    (Q.normGroup _ h.choose_spec.choose_spec.choose_spec)).choose_spec.1
  cover := (CitedInstances.exists_coset_cover S.G
    (Q.normGroup _ h.choose_spec.choose_spec.choose_spec)).choose_spec.2

/-- The single-factor normalization with the default choice. -/
noncomputable def normalization [Finite Ω] (h : Q.SingleFactor) : Normalization S :=
  Q.normalizationOf (Q.defaultChoice h)

/-- A choice gives the single-factor case. -/
theorem NormChoice.singleFactor (c : Q.NormChoice) : Q.SingleFactor := ⟨c.m, c.k, c.e, c.hS⟩

end PrimitiveQuotient

end GI.Algorithm
