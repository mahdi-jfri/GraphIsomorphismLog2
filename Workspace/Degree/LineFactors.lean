module

public import Workspace.Degree.RadicalFreeCount
public import Workspace.Degree.SubgroupIndex
public import Workspace.Degree.LinearSteps
public import Workspace.Proved.PalfyHard
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# The simple factors act on the lines of `V`

Let `H ≤ GL(V)` be irreducible and let `C` be normalized by `H`, with scalar solvable radical `R`.
Put `Q = C / R`. Let `T_1, …, T_b` be the simple factors of the socle of `Q`, and let `f_i` be the
least index of a proper subgroup of `T_i`. Then `∏ f_i ≤ |V|²` (`GI.Degree.prod_index_le`).

The socle acts on the lines of `V`, since `R` is scalar. The preimage `P` of the socle is
normalized by `H`, so it is completely reducible. Let `F_i` be the space fixed by the commutators
of the preimage of `T_i`. A vector `v` outside every `F_i` exists (`GI.Degree.exists_not_mem`), and
no `T_i` can stabilize the line of `v`, because a commutator acts trivially on a stable line. So
`GI.Degree.prod_le_index_sq'` applies to the stabilizer of this line, and its index is at most `|V|`.
-/

@[expose] public section

namespace GI.Degree

open GI.Proved GI.RadicalSocle GI.SocleOuter
open scoped commutatorElement

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/-! ### Characteristic subgroups -/

section Char

variable {G : Type*} [Group G] [Finite G]

theorem map_solvableRadical_le (φ : G ≃* G) :
    (solvableRadical G).map φ.toMonoidHom ≤ solvableRadical G := by
  haveI : ((solvableRadical G).map φ.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance _ φ.surjective
  haveI : Group.IsSolvable ((solvableRadical G).map φ.toMonoidHom) :=
    solvable_of_surjective (φ.toMonoidHom.subgroupMap_surjective _)
  exact le_solvableRadical _

theorem map_solvableRadical_eq (φ : G ≃* G) :
    (solvableRadical G).map φ.toMonoidHom = solvableRadical G := by
  refine le_antisymm (map_solvableRadical_le φ) fun x hx => ?_
  exact ⟨φ.symm x, map_solvableRadical_le φ.symm ⟨x, hx, rfl⟩, φ.apply_symm_apply x⟩

omit [Finite G] in
theorem map_mem_socle (e : G ≃* G) {x : G} (hx : x ∈ socle G) : e x ∈ socle G := by
  haveI : ((socle G).comap e.toMonoidHom).Normal := Subgroup.Normal.comap inferInstance _
  have h : socle G ≤ (socle G).comap e.toMonoidHom :=
    socle_le_normal _ fun M hM y hy => minimalNormal_le_socle (hM.map e) ⟨y, hy, rfl⟩
  exact h hx

end Char

/-- Conjugation by `h` as an automorphism of a subgroup normalized by `H`. -/
def conjAut {C H : Subgroup (Module.End K V)ˣ} (hC : palfyNormal C H) (h : (Module.End K V)ˣ)
    (hh : h ∈ H) : C ≃* C where
  toFun c := ⟨h * c * h⁻¹, hC.2 h hh c c.2⟩
  invFun c := ⟨h⁻¹ * c * h, by simpa using hC.2 h⁻¹ (H.inv_mem hh) c c.2⟩
  left_inv c := Subtype.ext (by simp [mul_assoc])
  right_inv c := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

/-! ### A vector outside a family of subspaces -/

/-- If each `F i` is proper with a complement `X i`, and a sum `v + u` with `v ∈ F i`, `u ∈ X i`
lies in `F j` only if `v` does, then some vector is outside every `F i`. -/
theorem exists_not_mem [Finite V] {ι : Type*} [Fintype ι] (F X : ι → Submodule K V)
    (hc : ∀ i, IsCompl (F i) (X i)) (hne : ∀ i, F i ≠ ⊤)
    (hsum : ∀ i j, ∀ v ∈ F i, ∀ u ∈ X i, v + u ∈ F j → v ∈ F j) :
    ∃ v : V, ∀ i, v ∉ F i := by
  classical
  haveI : Nonempty V := ⟨0⟩
  obtain ⟨v, hv⟩ := Finite.exists_max fun v : V => (Finset.univ.filter fun i => v ∉ F i).card
  refine ⟨v, fun i hi => ?_⟩
  obtain ⟨u, hu, hu0⟩ : ∃ u ∈ X i, u ≠ 0 := by
    by_contra hall
    push Not at hall
    have : X i = ⊥ := (Submodule.eq_bot_iff _).2 hall
    have h2 := (hc i).sup_eq_top
    rw [this, sup_bot_eq] at h2
    exact hne i h2
  have hsub : (Finset.univ.filter fun j => v ∉ F j) ⊂
      Finset.univ.filter fun j => v + u ∉ F j := by
    refine Finset.ssubset_iff_of_subset ?_ |>.2 ⟨i, ?_, ?_⟩
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact fun h => hj (hsum i j v hi u hu h)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro h
      apply hu0
      have hu' : u ∈ F i := by simpa using (F i).sub_mem h hi
      have := Submodule.mem_inf.2 ⟨hu', hu⟩
      rwa [(hc i).inf_eq_bot, Submodule.mem_bot] at this
    · simpa using hi
  exact absurd (hv (v + u)) (not_le.2 (Finset.card_lt_card hsub))

/-! ### The stabilizer of a line -/

/-- The elements of `C` that map the line of `v` to itself. -/
def lineStab (C : Subgroup (Module.End K V)ˣ) (v : V) : Subgroup C where
  carrier := {c | Submodule.span K {((c : (Module.End K V)ˣ) : Module.End K V) v} =
    Submodule.span K {v}}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have h1 : Submodule.span K {((a * b : C) : (Module.End K V)ˣ).val v} =
        (Submodule.span K {((b : C) : (Module.End K V)ˣ).val v}).map
          ((a : (Module.End K V)ˣ) : Module.End K V) := by
      rw [Submodule.map_span, Set.image_singleton]
      rfl
    rw [h1, hb, Submodule.map_span, Set.image_singleton, ha]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : Submodule.span K {((a⁻¹ : C) : (Module.End K V)ˣ).val v} =
        (Submodule.span K {v}).map (((a⁻¹ : C) : (Module.End K V)ˣ) : Module.End K V) := by
      rw [Submodule.map_span, Set.image_singleton]
    rw [h1, ← ha, Submodule.map_span, Set.image_singleton, ← Module.End.mul_apply, ← Units.val_mul,
      ← Subgroup.coe_mul]
    simpa using ha.symm

theorem index_lineStab_le [Finite V] (C : Subgroup (Module.End K V)ˣ) (v : V) :
    (lineStab C v).index ≤ Nat.card V := by
  refine Nat.card_le_card_of_injective
    (fun q : C ⧸ lineStab C v => (((q.out : C) : (Module.End K V)ˣ) : Module.End K V) v) ?_
  intro a b h
  rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b]
  refine QuotientGroup.eq.2 ?_
  change Submodule.span K {(((a.out⁻¹ * b.out : C) : (Module.End K V)ˣ) : Module.End K V) v} = _
  congr 2
  have h' : (((a.out : C) : (Module.End K V)ˣ) : Module.End K V) v =
      (((b.out : C) : (Module.End K V)ˣ) : Module.End K V) v := h
  change (((a.out⁻¹ : C) : (Module.End K V)ˣ) : Module.End K V)
    ((((b.out : C) : (Module.End K V)ˣ) : Module.End K V) v) = v
  rw [← h', ← Module.End.mul_apply, ← Units.val_mul, ← Subgroup.coe_mul]
  simp

/-- A scalar is in the stabilizer of every line. -/
theorem mem_lineStab_of_scalar [Nontrivial V] {C : Subgroup (Module.End K V)ˣ} (v : V) (c : C)
    (hc : palfySc ((c : (Module.End K V)ˣ) : Module.End K V)) : c ∈ lineStab C v := by
  obtain ⟨k, hk⟩ := hc
  change Submodule.span K {((c : (Module.End K V)ˣ) : Module.End K V) v} = _
  have hk0 : k ≠ 0 := by
    rintro rfl
    have h1 : ((c : (Module.End K V)ˣ) : Module.End K V) = 0 := by rw [← hk, map_zero]
    exact Units.ne_zero (c : (Module.End K V)ˣ) h1
  rw [← hk, Module.algebraMap_end_apply]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 k hk0) v

/-- An element stabilizing the line of a nonzero `v` multiplies `v` by a scalar. -/
theorem exists_smul_of_mem_lineStab {C : Subgroup (Module.End K V)ˣ} {v : V} {c : C}
    (hc : c ∈ lineStab C v) :
    ∃ k : K, ((c : (Module.End K V)ˣ) : Module.End K V) v = k • v := by
  have h : ((c : (Module.End K V)ˣ) : Module.End K V) v ∈ Submodule.span K {v} := by
    have hc' : Submodule.span K {((c : (Module.End K V)ˣ) : Module.End K V) v} =
      Submodule.span K {v} := hc
    rw [← hc']
    exact Submodule.mem_span_singleton_self _
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.1 h
  exact ⟨k, hk.symm⟩

/-! ### The space fixed by the commutators of a subgroup -/

/-- The vectors fixed by all commutators of `A`. -/
def commFix {C : Subgroup (Module.End K V)ˣ} (A : Subgroup C) : Submodule K V where
  carrier := {v | ∀ a ∈ A, ∀ b ∈ A,
    (((a * b * a⁻¹ * b⁻¹ : C) : (Module.End K V)ˣ) : Module.End K V) v = v}
  add_mem' := fun ha hb a h b h' => by rw [map_add, ha a h b h', hb a h b h']
  zero_mem' := fun _ _ _ _ => map_zero _
  smul_mem' := fun k v hv a h b h' => by rw [map_smul, hv a h b h']

theorem commFix_inv {C : Subgroup (Module.End K V)ˣ} {A : Subgroup C} {p : C}
    (hp : ∀ a ∈ A, p⁻¹ * a * p ∈ A) {v : V} (hv : v ∈ commFix A) :
    ((p : (Module.End K V)ˣ) : Module.End K V) v ∈ commFix A := by
  intro a ha b hb
  have h := hv _ (hp a ha) _ (hp b hb)
  have e : a * b * a⁻¹ * b⁻¹ * p =
      p * ((p⁻¹ * a * p) * (p⁻¹ * b * p) * (p⁻¹ * a * p)⁻¹ * (p⁻¹ * b * p)⁻¹) := by group
  rw [← Module.End.mul_apply, ← Units.val_mul, ← Subgroup.coe_mul, e, Subgroup.coe_mul,
    Units.val_mul, Module.End.mul_apply, h]

/-- If every element of `A` multiplies `v` by a scalar, then `v ∈ commFix A`. -/
theorem mem_commFix_of_smul {C : Subgroup (Module.End K V)ˣ} {A : Subgroup C} {v : V}
    (h : ∀ a ∈ A, ∃ k : K, ((a : (Module.End K V)ˣ) : Module.End K V) v = k • v) :
    v ∈ commFix A := by
  intro a ha b hb
  obtain ⟨k, hk⟩ := h a ha
  obtain ⟨l, hl⟩ := h b hb
  obtain ⟨k', hk'⟩ := h a⁻¹ (A.inv_mem ha)
  obtain ⟨l', hl'⟩ := h b⁻¹ (A.inv_mem hb)
  have hkk' : (((a * a⁻¹ : C) : (Module.End K V)ˣ) : Module.End K V) v = (k * k') • v := by
    simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, hk', map_smul, hk, smul_smul,
      mul_comm k k']
  have hll' : (((b * b⁻¹ : C) : (Module.End K V)ˣ) : Module.End K V) v = (l * l') • v := by
    simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, hl', map_smul, hl, smul_smul,
      mul_comm l l']
  simp only [mul_inv_cancel, OneMemClass.coe_one, Units.val_one, Module.End.one_apply] at hkk' hll'
  simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply, hl', map_smul, hk', hl, hk,
    smul_smul]
  calc _ = (l * l' * (k * k')) • v := by congr 1; ring
    _ = (l * l') • (k * k') • v := by rw [smul_smul]
    _ = v := by rw [← hkk', ← hll']

/-! ### The main count -/

section Main

variable [Finite K] [Finite V] [Nontrivial V] {H C : Subgroup (Module.End K V)ˣ}

local notation "R₀" => solvableRadical C
local notation "Q" => C ⧸ solvableRadical C
local notation "q" => QuotientGroup.mk' (solvableRadical C)

/-- The preimage in `C` of the socle of `Q`. -/
noncomputable def socPre (C : Subgroup (Module.End K V)ˣ) : Subgroup C :=
  (socle (C ⧸ solvableRadical C)).comap (QuotientGroup.mk' (solvableRadical C))

/-- The preimage in `C` of a simple factor. -/
noncomputable def facPre (N : Factors (C ⧸ solvableRadical C)) : Subgroup C :=
  (N.val.map (socle (C ⧸ solvableRadical C)).subtype).comap (QuotientGroup.mk' (solvableRadical C))

omit [Finite K] [Nontrivial V] in
/-- The preimage of the socle is normalized by `H`. -/
theorem socPre_normal (hC : palfyNormal C H) :
    palfyNormal ((socPre C).map C.subtype) H := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨c, -, rfl⟩
    exact hC.1 c.2
  · rintro h hh _ ⟨c, hc, rfl⟩
    let φ := conjAut hC h hh
    let φbar : Q ≃* Q := QuotientGroup.congr _ _ φ (map_solvableRadical_eq φ)
    refine ⟨φ c, ?_, rfl⟩
    have : q (φ c) = φbar (q c) := rfl
    change q (φ c) ∈ socle Q
    rw [this]
    exact map_mem_socle φbar hc

omit [Finite K] [Nontrivial V] in
theorem facPre_conj (N : Factors Q) {p : C} (hp : p ∈ socPre C) {a : C} (ha : a ∈ facPre N) :
    p⁻¹ * a * p ∈ facPre N := by
  obtain ⟨n, hn, hna⟩ : q a ∈ N.val.map (socle Q).subtype := ha
  have hN : N.val.Normal := N.property.1
  have hc := hN.conj_mem n hn (⟨q p, hp⟩ : socle Q)⁻¹
  refine ⟨_, hc, ?_⟩
  simp only [map_mul, map_inv, inv_inv, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  have hna' : ((n : socle Q) : Q) = q a := hna
  rw [hna']

omit [Finite K] [Nontrivial V] in
theorem facPre_le (N : Factors Q) : facPre N ≤ socPre C := by
  intro a ha
  obtain ⟨n, -, hna⟩ : q a ∈ N.val.map (socle Q).subtype := ha
  change q a ∈ socle Q
  rw [← hna]
  exact n.2

/-- A simple factor that does not commute gives `commFix ≠ ⊤`. -/
theorem commFix_ne_top (N : Factors Q) (hN : ∃ x y : N.val, x * y ≠ y * x) :
    commFix (facPre N) ≠ (⊤ : Submodule K V) := by
  intro htop
  obtain ⟨x, y, hxy⟩ := hN
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective R₀ ((x.1 : socle Q) : Q)
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective R₀ ((y.1 : socle Q) : Q)
  have ham : a ∈ facPre N := ⟨x.1, x.2, ha.symm⟩
  have hbm : b ∈ facPre N := ⟨y.1, y.2, hb.symm⟩
  have h1 : a * b * a⁻¹ * b⁻¹ = 1 := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    have : v ∈ commFix (facPre N) := htop ▸ Submodule.mem_top
    exact this a ham b hbm
  have h2 : a * b = b * a := by
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  apply hxy
  apply Subtype.ext
  apply Subtype.ext
  have h3 := congrArg q h2
  simp only [map_mul, ha, hb] at h3
  exact h3

variable (hH : palfyIrr H) (hC : palfyNormal C H)
  (hR : ∀ r : C, r ∈ solvableRadical C → palfySc ((r : (Module.End K V)ˣ) : Module.End K V))

include hH hC in
/-- Some vector is outside the fixed space of the commutators of every factor. -/
theorem exists_moved_vector (hna : ∀ N : Factors Q, ∃ x y : N.val, x * y ≠ y * x) :
    ∃ v : V, ∀ N : Factors Q, v ∉ commFix (facPre N) := by
  classical
  letI := Fintype.ofFinite (Factors Q)
  have hP := socPre_normal hC
  have hCR : palfyCR ((socPre C).map C.subtype) := palfy_clifford hH hP
  have hinv : ∀ N : Factors Q, palfyInv ((socPre C).map C.subtype) (commFix (facPre N)) := by
    rintro N _ ⟨p, hp, rfl⟩ v hv
    exact commFix_inv (fun a ha => facPre_conj N hp ha) hv
  choose X hX hcompl using fun N => hCR _ (hinv N)
  refine exists_not_mem (fun N => commFix (facPre N)) X hcompl
    (fun N => commFix_ne_top N (hna N)) ?_
  intro N N' v hv u hu hvu a ha b hb
  set g : C := a * b * a⁻¹ * b⁻¹ with hg
  have hgP : g ∈ socPre C := by
    have h1 := facPre_le N' ha
    have h2 := facPre_le N' hb
    exact (socPre C).mul_mem ((socPre C).mul_mem ((socPre C).mul_mem h1 h2)
      ((socPre C).inv_mem h1)) ((socPre C).inv_mem h2)
  have hgP' : (g : (Module.End K V)ˣ) ∈ (socPre C).map C.subtype := ⟨g, hgP, rfl⟩
  have h1 := hvu a ha b hb
  rw [← hg, map_add] at h1
  have h2 := hinv N _ hgP' v hv
  have h3 := hX N _ hgP' u hu
  have h4 : ((g : (Module.End K V)ˣ) : Module.End K V) v - v ∈
      commFix (facPre N) ⊓ X N := by
    refine ⟨Submodule.sub_mem _ h2 hv, ?_⟩
    have : ((g : (Module.End K V)ˣ) : Module.End K V) v - v =
        u - ((g : (Module.End K V)ˣ) : Module.End K V) u := by
      rw [sub_eq_sub_iff_add_eq_add, h1]
      abel
    rw [this]
    exact Submodule.sub_mem _ hu h3
  rw [(hcompl N).inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at h4
  exact h4

include hH hC hR in
/-- **The count on lines.** -/
theorem prod_index_le [Fintype (Factors Q)]
    (rf : ∀ N : Subgroup Q, N.Normal → IsSolvable N → N = ⊥)
    (f : Factors Q → ℕ) (hf : ∀ N, ∀ A : Subgroup N.val, A ≠ ⊤ → f N ≤ A.index) :
    ∏ N, f N ≤ Nat.card V ^ 2 := by
  classical
  have rfE := normal_subgroup_radicalFree rf (socle Q)
  have hna : ∀ N : Factors Q, ∃ x y : N.val, x * y ≠ y * x :=
    socle_intrinsic_factor_nonabelian rf
  obtain ⟨v, hv⟩ := exists_moved_vector hH hC hna
  let ψ := intrinsicProductEquiv rfE socle_idempotent
  let SQ : Subgroup Q := (lineStab C v).map q
  let φ : (∀ N : Factors Q, N.val) →* Q := (socle Q).subtype.comp ψ.toMonoidHom
  let S : Subgroup (∀ N : Factors Q, N.val) := SQ.comap φ
  have hperf : ∀ N : Factors Q, ⁅(⊤ : Subgroup N.val), (⊤ : Subgroup N.val)⁆ = ⊤ := by
    intro N
    have hs : IsSimpleGroup N.val := socle_intrinsic_factor_simple N
    rcases hs.eq_bot_or_eq_top_of_normal (H := ⁅(⊤ : Subgroup N.val), (⊤ : Subgroup N.val)⁆) with h | h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hna N
      apply hxy
      have : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup N.val), (⊤ : Subgroup N.val)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [h, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    · exact h
  have hS : ∀ N : Factors Q, ¬ ∀ t : N.val, MonoidHom.mulSingle (fun N : Factors Q => N.val) N t ∈ S := by
    intro N hall
    apply hv N
    refine mem_commFix_of_smul fun a ha => ?_
    obtain ⟨n, hn, hna'⟩ : q a ∈ N.val.map (socle Q).subtype := ha
    have h1 := hall ⟨n, hn⟩
    have h2 : φ (MonoidHom.mulSingle (fun N : Factors Q => N.val) N ⟨n, hn⟩) = q a := by
      change ((ψ (Pi.mulSingle N ⟨n, hn⟩) : socle Q) : Q) = q a
      rw [intrinsicProductEquiv_single rfE socle_idempotent N ⟨n, hn⟩]
      exact hna'
    have h3 : q a ∈ SQ := by
      rw [← h2]
      exact h1
    obtain ⟨s, hs, hsa⟩ := h3
    have hmem : s⁻¹ * a ∈ solvableRadical C := QuotientGroup.eq.1 hsa
    have h4 : a ∈ lineStab C v := by
      have := (lineStab C v).mul_mem hs (mem_lineStab_of_scalar v _ (hR _ hmem))
      simpa using this
    exact exists_smul_of_mem_lineStab h4
  have h1 := prod_le_index_sq' S f hperf hf hS
  have h2 : S.index ≤ SQ.index := index_comap_le' φ SQ
  have h3 : SQ.index ≤ (lineStab C v).index :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _))
  exact h1.trans (Nat.pow_le_pow_left (h2.trans (h3.trans (index_lineStab_le C v))) 2)

end Main

end GI.Degree
