module

public import Workspace.Proved.VsMBasic

@[expose] public section

/-!
# Idempotents of commuting elements of order `r`

Let `R` be a commutative algebra over a field `K` in which `r` is invertible, `ζ ∈ R` with
`ζ ^ r = 1` and `∑_l ζ^(m l) = 0` for `m ≠ 0` in `ZMod r` (`ζ` is a primitive root of unity in
a domain). For `x` with `x ^ r = 1` put
`e_j(x) = r⁻¹ ∑_l ζ^(-j l) x^l` (`vsMIdem`). Then `x e_j = ζ^j e_j`, `∑_j e_j = 1` and
`e_j e_{j'} = δ_{j j'} e_j`. For a family `x_1, …, x_k` the products
`π_c = ∏_i e_{c_i}(x_i)` (`vsMIdemP`) are orthogonal idempotents with sum `1`, and
`x_i π_c = ζ^(c_i) π_c`. Exponents in `ZMod r` act through `ZMod.val`.
-/

namespace GI.Proved

variable (K : Type*) {R : Type*} [Field K] [CommRing R] [Algebra K R] {r : ℕ} [NeZero r]

theorem vsM_pow_mod {M : Type*} [Monoid M] {x : M} (hx : x ^ r = 1) (n : ℕ) :
    x ^ (n % r) = x ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n r, pow_add, pow_mul, hx, one_pow, one_mul]

theorem vsM_zp_add {M : Type*} [Monoid M] {x : M} (hx : x ^ r = 1) (a b : ZMod r) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [ZMod.val_add, vsM_pow_mod hx, pow_add]

theorem vsM_zp_mul {M : Type*} [Monoid M] {x : M} (hx : x ^ r = 1) (a b : ZMod r) :
    x ^ (a * b).val = (x ^ b.val) ^ a.val := by
  rw [ZMod.val_mul, vsM_pow_mod hx, ← pow_mul, mul_comm]

theorem vsM_zp_one {M : Type*} [Monoid M] {x : M} (hx : x ^ r = 1) :
    x ^ (1 : ZMod r).val = x := by
  rw [ZMod.val_one_eq_one_mod, vsM_pow_mod hx, pow_one]

theorem vsM_zp_zero {M : Type*} [Monoid M] (x : M) : x ^ (0 : ZMod r).val = 1 := by
  rw [ZMod.val_zero, pow_zero]

/-- `e_j(x) = r⁻¹ ∑_l ζ^(-j l) x^l`. -/
noncomputable def vsMIdem (ζ x : R) (j : ZMod r) : R :=
  (r : K)⁻¹ • ∑ l : ZMod r, ζ ^ (-(j * l)).val * x ^ l.val

/-- `π_c = ∏_i e_{c_i}(x_i)`. -/
noncomputable def vsMIdemP {k : ℕ} (ζ : R) (x : Fin k → R) (c : Fin k → ZMod r) : R :=
  ∏ i, vsMIdem K ζ (x i) (c i)

variable {K} {ζ : R} (hζ : ζ ^ r = 1)
  (hgeo : ∀ m : ZMod r, m ≠ 0 → ∑ l : ZMod r, ζ ^ (m * l).val = 0) (hrK : (r : K) ≠ 0)

include hζ in
theorem vsM_idem_eig {x : R} (hx : x ^ r = 1) (j : ZMod r) :
    x * vsMIdem K ζ x j = ζ ^ j.val * vsMIdem K ζ x j := by
  unfold vsMIdem
  rw [mul_smul_comm, mul_smul_comm, Finset.mul_sum, Finset.mul_sum]
  congr 1
  conv_rhs => rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod r))]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [Equiv.coe_addRight]
  have hz : ζ ^ (-(j * l)).val = ζ ^ j.val * ζ ^ (-(j * (l + 1))).val := by
    rw [← vsM_zp_add hζ, show j + -(j * (l + 1)) = -(j * l) by ring]
  rw [vsM_zp_add hx l 1, vsM_zp_one hx, hz]
  ring

include hζ in
theorem vsM_idem_pow {x : R} (hx : x ^ r = 1) (j : ZMod r) (l : ZMod r) :
    x ^ l.val * vsMIdem K ζ x j = ζ ^ (j * l).val * vsMIdem K ζ x j := by
  have h : ∀ n : ℕ, x ^ n * vsMIdem K ζ x j = (ζ ^ j.val) ^ n * vsMIdem K ζ x j := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, vsM_idem_eig hζ hx, ← mul_assoc, mul_comm (x ^ n),
        mul_assoc, ih, ← mul_assoc, pow_succ, mul_comm (ζ ^ j.val)]
  rw [h, vsM_zp_mul hζ, ← pow_mul, ← pow_mul, Nat.mul_comm]

include hgeo hrK in
theorem vsM_idem_sum {x : R} (hx : x ^ r = 1) : ∑ j : ZMod r, vsMIdem K ζ x j = 1 := by
  unfold vsMIdem
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  rw [Finset.sum_eq_single (0 : ZMod r)]
  · simp only [mul_zero, neg_zero, vsM_zp_zero, Finset.sum_const, Finset.card_univ, ZMod.card,
      mul_one]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hrK, one_smul]
  · intro l _ hl
    have : ∑ j : ZMod r, ζ ^ (-(j * l)).val = ∑ j : ZMod r, ζ ^ (-l * j).val :=
      Finset.sum_congr rfl fun j _ => by ring_nf
    rw [this, hgeo (-l) (neg_ne_zero.2 hl), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

include hζ hgeo hrK in
theorem vsM_idem_mul {x : R} (hx : x ^ r = 1) (j j' : ZMod r) :
    vsMIdem K ζ x j' * vsMIdem K ζ x j = if j' = j then vsMIdem K ζ x j else 0 := by
  have h1 : vsMIdem K ζ x j' * vsMIdem K ζ x j =
      (r : K)⁻¹ • ((∑ l : ZMod r, ζ ^ ((j - j') * l).val) * vsMIdem K ζ x j) := by
    conv_lhs => rw [vsMIdem]
    rw [smul_mul_assoc, Finset.sum_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_assoc, vsM_idem_pow hζ hx, ← mul_assoc, ← vsM_zp_add hζ]
    congr 3
    ring
  rw [h1]
  split_ifs with hj
  · subst hj
    simp only [sub_self, zero_mul, vsM_zp_zero, Finset.sum_const, Finset.card_univ, ZMod.card,
      nsmul_eq_mul, mul_one]
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hrK, one_smul]
  · rw [hgeo _ (sub_ne_zero.2 (Ne.symm hj)), zero_mul, smul_zero]

include hζ hgeo hrK in
theorem vsM_idemP_sum {k : ℕ} {x : Fin k → R} (hx : ∀ i, x i ^ r = 1) :
    ∑ c : Fin k → ZMod r, vsMIdemP K ζ x c = 1 := by
  unfold vsMIdemP
  rw [← Fintype.prod_sum]
  exact Finset.prod_eq_one fun i _ => vsM_idem_sum hgeo hrK (hx i)

include hζ hgeo hrK in
theorem vsM_idemP_mul {k : ℕ} {x : Fin k → R} (hx : ∀ i, x i ^ r = 1)
    (c c' : Fin k → ZMod r) :
    vsMIdemP K ζ x c' * vsMIdemP K ζ x c = if c' = c then vsMIdemP K ζ x c else 0 := by
  unfold vsMIdemP
  rw [← Finset.prod_mul_distrib]
  split_ifs with hc
  · subst hc
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [vsM_idem_mul hζ hgeo hrK (hx i), if_pos rfl]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by
      rw [vsM_idem_mul hζ hgeo hrK (hx i), if_neg hi])

include hζ in
theorem vsM_idemP_eig {k : ℕ} {x : Fin k → R} (hx : ∀ i, x i ^ r = 1) (c : Fin k → ZMod r)
    (i : Fin k) : x i * vsMIdemP K ζ x c = ζ ^ (c i).val * vsMIdemP K ζ x c := by
  unfold vsMIdemP
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), ← mul_assoc, vsM_idem_eig hζ (hx i),
    mul_assoc]

end GI.Proved
