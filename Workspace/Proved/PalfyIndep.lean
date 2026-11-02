import Workspace.Proved.PalfyBasic

/-!
# Groups whose commutators and central elements are scalar

Let `N ≤ GL_K(V)` be a finite group in which every commutator `y x y⁻¹ x⁻¹` is a scalar and
every element of the center is a scalar. Let `S` be the subgroup of scalars in `N`. Then
`|N : S| ≤ (dim V)^2` and `|N| ≤ |K| · (dim V)^2` (`GI.Proved.palfy_card_le_of_scalar`).

*Proof.* For `x ∈ N`, the map `ω_x(y) = y x y⁻¹ x⁻¹` is a homomorphism from `N` to `K^×`, and
`y x y⁻¹ = ω_x(y) x`. If `ω_x = ω_{x'}`, then `x'⁻¹ x` is central, so `x` and `x'` lie in the same
coset of `S`. Take one representative `x_q` of each coset `q`. If `∑ g_q x_q = 0`, conjugating by
`y` gives `∑ g_q ω_q(y) x_q = 0`. Applying a linear functional `φ` gives the relation
`∑ g_q φ(x_q) ω_q = 0` among distinct characters, so `g_q φ(x_q) = 0` by Artin's independence
of characters. Taking `φ` with `φ(x_q) ≠ 0` gives `g_q = 0`. So the `x_q` are linearly
independent in `End_K(V)`, whose dimension is `(dim V)^2`, and `|N| = |S| |N : S| ≤ |K| (dim V)^2`.
-/

namespace GI.Proved

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

/-- `x` is a scalar operator. -/
def palfySc (x : Module.End K V) : Prop := ∃ k : K, algebraMap K (Module.End K V) k = x

theorem palfySc_one : palfySc (1 : Module.End K V) := ⟨1, map_one _⟩

theorem palfySc_mul {x y : Module.End K V} (hx : palfySc x) (hy : palfySc y) :
    palfySc (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, map_mul _ a b⟩

theorem palfySc_comm {x : Module.End K V} (hx : palfySc x) (y : Module.End K V) :
    x * y = y * x := by
  obtain ⟨a, rfl⟩ := hx
  exact Algebra.commutes a y

theorem palfySc_inv {u : (Module.End K V)ˣ} (hu : palfySc (u : Module.End K V)) :
    palfySc ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) := by
  obtain ⟨a, ha⟩ := hu
  refine ⟨a⁻¹, ?_⟩
  by_cases ha0 : a = 0
  · -- then `u = 0`, so the ring is trivial
    have h0 : (u : Module.End K V) = 0 := by rw [← ha, ha0, map_zero]
    have h1 : (1 : Module.End K V) = 0 := by
      rw [← Units.mul_inv u, h0, zero_mul]
    exact (subsingleton_of_zero_eq_one h1.symm).elim _ _
  · symm
    apply Units.inv_eq_of_mul_eq_one_right
    rw [← ha, ← map_mul, mul_inv_cancel₀ ha0, map_one]

theorem palfySc_unique [Nontrivial V] {a b : K}
    (h : algebraMap K (Module.End K V) a = algebraMap K (Module.End K V) b) : a = b :=
  (algebraMap K (Module.End K V)).injective h

/-- The scalars in `N`. -/
def palfyScSub (N : Subgroup (Module.End K V)ˣ) : Subgroup N where
  carrier := {x | palfySc (((x : N) : (Module.End K V)ˣ) : Module.End K V)}
  mul_mem' := fun ha hb => palfySc_mul ha hb
  one_mem' := palfySc_one
  inv_mem' := fun ha => palfySc_inv ha

section

variable [Nontrivial V] (N : Subgroup (Module.End K V)ˣ)
  (hcomm : ∀ x ∈ N, ∀ y ∈ N, palfySc ((y * x * y⁻¹ * x⁻¹ : (Module.End K V)ˣ) :
    Module.End K V))

/-- The character `y ↦ y x y⁻¹ x⁻¹`. -/
noncomputable def palfyChar (x : N) : N →* K where
  toFun y := Classical.choose (hcomm x x.2 y y.2)
  map_one' := by
    apply palfySc_unique (V := V)
    rw [Classical.choose_spec (hcomm x x.2 1 (1 : N).2), map_one]
    simp
  map_mul' a b := by
    apply palfySc_unique (V := V)
    rw [Classical.choose_spec (hcomm x x.2 _ (a * b).2), map_mul,
      Classical.choose_spec (hcomm x x.2 _ a.2), Classical.choose_spec (hcomm x x.2 _ b.2)]
    have key : ((a * b : N) : (Module.End K V)ˣ) * x * ((a * b : N) : (Module.End K V)ˣ)⁻¹ *
        (x : (Module.End K V)ˣ)⁻¹ = (a : (Module.End K V)ˣ) * ((b : (Module.End K V)ˣ) * x * (b : (Module.End K V)ˣ)⁻¹ *
          (x : (Module.End K V)ˣ)⁻¹) * (a : (Module.End K V)ˣ)⁻¹ *
          ((a : (Module.End K V)ˣ) * x * (a : (Module.End K V)ˣ)⁻¹ * (x : (Module.End K V)ˣ)⁻¹)
          := by
      simp only [Subgroup.coe_mul]
      group
    rw [key]
    obtain ⟨c, hc⟩ := hcomm x x.2 b b.2
    have hB : ∀ g : (Module.End K V)ˣ, g * ((b : (Module.End K V)ˣ) * x *
        (b : (Module.End K V)ˣ)⁻¹ * (x : (Module.End K V)ˣ)⁻¹) * g⁻¹ =
        (b : (Module.End K V)ˣ) * x * (b : (Module.End K V)ˣ)⁻¹ * (x : (Module.End K V)ˣ)⁻¹ := by
      intro g
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, ← hc, ← palfySc_comm ⟨c, rfl⟩ (g : Module.End K V),
        mul_assoc, Units.mul_inv, mul_one]
    rw [hB, Units.val_mul, ← hc]
    exact palfySc_comm ⟨c, rfl⟩ _

theorem palfyChar_spec (x y : N) :
    ((y : (Module.End K V)ˣ) : Module.End K V) * ((x : (Module.End K V)ˣ) : Module.End K V) *
      (((y : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ) : Module.End K V) =
      algebraMap K (Module.End K V) (palfyChar N hcomm x y) *
        ((x : (Module.End K V)ˣ) : Module.End K V) := by
  have h := Classical.choose_spec (hcomm x x.2 y y.2)
  change algebraMap K _ (palfyChar N hcomm x y) = _ at h
  rw [h]
  simp only [Units.val_mul]
  rw [mul_assoc _ (((x : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ) : Module.End K V),
    Units.inv_mul, mul_one]

theorem palfyChar_ne_zero (x y : N) : palfyChar N hcomm x y ≠ 0 := by
  intro h0
  have := map_mul (palfyChar N hcomm x) y y⁻¹
  rw [mul_inv_cancel, map_one, h0, zero_mul] at this
  exact one_ne_zero this

omit [Nontrivial V] in
theorem palfy_cancel_aux {c : K} (hc : c ≠ 0) {Y X X' X'' : Module.End K V}
    (hinv1 : X'' * X' = 1) (hinv2 : X' * X'' = 1)
    (h1 : Y * X = algebraMap K _ c * X * Y) (h2 : Y * X' = algebraMap K _ c * X' * Y) :
    X'' * X * Y = Y * (X'' * X) := by
  have hc' : algebraMap K (Module.End K V) c⁻¹ * algebraMap K (Module.End K V) c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  have e1 : X'' * Y = algebraMap K _ c * Y * X'' := by
    calc X'' * Y = X'' * (Y * X') * X'' := by rw [mul_assoc, mul_assoc, hinv2, mul_one]
      _ = X'' * (algebraMap K _ c * X' * Y) * X'' := by rw [h2]
      _ = algebraMap K _ c * (X'' * X') * Y * X'' := by
        simp only [mul_assoc]
        rw [← mul_assoc X'' (algebraMap K _ c), ← Algebra.commutes c X'', mul_assoc]
      _ = algebraMap K _ c * Y * X'' := by rw [hinv1, mul_one]
  have e2 : algebraMap K _ c * (X'' * X * Y) = algebraMap K _ c * (Y * (X'' * X)) := by
    calc algebraMap K _ c * (X'' * X * Y) = X'' * (Y * X) := by
          rw [h1]
          simp only [mul_assoc]
          rw [← mul_assoc X'' (algebraMap K _ c), ← Algebra.commutes c X'', mul_assoc]
      _ = algebraMap K _ c * (Y * (X'' * X)) := by
          rw [← mul_assoc, e1]; simp only [mul_assoc]
  calc X'' * X * Y = algebraMap K _ c⁻¹ * (algebraMap K _ c * (X'' * X * Y)) := by
        rw [← mul_assoc, hc', one_mul]
    _ = Y * (X'' * X) := by rw [e2, ← mul_assoc, hc', one_mul]

variable (hcent : ∀ x ∈ N, (∀ y ∈ N, x * y = y * x) →
  palfySc ((x : (Module.End K V)ˣ) : Module.End K V))

include hcomm hcent in
theorem palfyChar_inj {x x' : N} (h : palfyChar N hcomm x = palfyChar N hcomm x') :
    x'⁻¹ * x ∈ palfyScSub N := by
  apply hcent _ (x'⁻¹ * x).2
  intro y hy
  apply Units.ext
  have h1 := palfyChar_spec N hcomm x ⟨y, hy⟩
  have h2 := palfyChar_spec N hcomm x' ⟨y, hy⟩
  rw [h] at h1
  set c := palfyChar N hcomm x' ⟨y, hy⟩
  have hY : ∀ X : Module.End K V, (y : Module.End K V) * X *
      ((y⁻¹ : (Module.End K V)ˣ) : Module.End K V) = algebraMap K _ c * X →
      (y : Module.End K V) * X = algebraMap K _ c * X * (y : Module.End K V) := by
    intro X hX
    rw [← hX, mul_assoc _ _ (y : Module.End K V), Units.inv_mul, mul_one]
  have := palfy_cancel_aux (palfyChar_ne_zero N hcomm x' ⟨y, hy⟩)
    (Units.inv_mul ((x' : N) : (Module.End K V)ˣ)) (Units.mul_inv ((x' : N) : (Module.End K V)ˣ))
    (hY _ h1) (hY _ h2)
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] using this

include hcomm hcent in
/-- **Order bound.** -/
theorem palfy_card_le_of_scalar [Finite K] [Finite V] :
    (palfyScSub N).index ≤ Module.finrank K V ^ 2 ∧
      Nat.card N ≤ Nat.card K * Module.finrank K V ^ 2 := by
  classical
  haveI : Module.Finite K V := Module.Finite.of_finite
  set S := palfyScSub N
  haveI : Fintype (N ⧸ S) := Fintype.ofFinite _
  let v : N ⧸ S → Module.End K V := fun q => (((q.out : N) : (Module.End K V)ˣ) : Module.End K V)
  let χ : N ⧸ S → (N →* K) := fun q => palfyChar N hcomm q.out
  have hχ : Function.Injective χ := by
    intro q q' hq
    have := palfyChar_inj N hcomm hcent hq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact (QuotientGroup.eq.mpr this).symm
  have hLI' : LinearIndependent K (fun q => ((χ q : N →* K) : N → K)) :=
    (linearIndependent_monoidHom N K).comp χ hχ
  have hv : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg q
    have hconj : ∀ y : N, ∑ q, (g q * χ q y) • v q = 0 := by
      intro y
      have := congrArg (fun F => ((y : (Module.End K V)ˣ) : Module.End K V) * F *
        (((y : (Module.End K V)ˣ)⁻¹ : (Module.End K V)ˣ) : Module.End K V)) hg
      simp only [mul_zero, zero_mul, Finset.mul_sum, Finset.sum_mul] at this
      rw [← this]
      apply Finset.sum_congr rfl
      intro q _
      rw [mul_smul_comm, smul_mul_assoc, palfyChar_spec N hcomm q.out y, ← Algebra.smul_def,
        smul_smul]
    have hφ : ∀ φ : Module.Dual K (Module.End K V), g q * φ (v q) = 0 := by
      intro φ
      have := Fintype.linearIndependent_iff.mp hLI' (fun q => g q * φ (v q)) (by
        funext y
        have := congrArg φ (hconj y)
        simp only [map_sum, map_smul, smul_eq_mul, map_zero] at this
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        rw [← this]
        apply Finset.sum_congr rfl
        intro q _
        ring)
      exact this q
    by_contra hg0
    have : v q = 0 := (Module.forall_dual_apply_eq_zero_iff K (v q)).mp
      (fun φ => (mul_eq_zero.mp (hφ φ)).resolve_left hg0)
    exact Units.ne_zero _ this
  have hcardQ : Fintype.card (N ⧸ S) ≤ Module.finrank K V ^ 2 := by
    have := hv.fintype_card_le_finrank
    rwa [Module.finrank_linearMap, ← sq] at this
  have hS : Nat.card S ≤ Nat.card K := by
    apply Nat.card_le_card_of_injective (fun s : S => Classical.choose (show palfySc _ from s.2))
    intro a b hab
    have ha := Classical.choose_spec (show palfySc _ from a.2)
    have hb := Classical.choose_spec (show palfySc _ from b.2)
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    rw [← ha, ← hb]
    simp only at hab
    rw [hab]
  have hidx : S.index ≤ Module.finrank K V ^ 2 := by
    rw [Subgroup.index, Nat.card_eq_fintype_card (α := N ⧸ S)]
    exact hcardQ
  refine ⟨hidx, ?_⟩
  rw [← Subgroup.card_mul_index S]
  exact Nat.mul_le_mul hS hidx

end

end GI.Proved
