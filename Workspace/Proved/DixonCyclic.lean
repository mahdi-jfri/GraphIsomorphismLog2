module

public import Workspace.Proved.DixonSemiregular

@[expose] public section

/-!
# A normal subgroup of prime order in the transitive case

Let `H` act faithfully by automorphisms on a finite commutative group `V ≠ 1`, transitively on
`V \ {1}`. Let `A` be a commutative normal subgroup of `H` and `a ∈ A` of prime order `q`. Then
every conjugate of `a` is a power of `a` (`GI.Proved.dixon_conj_mem_zpowers`), and so the derived
subgroup of `H` centralizes `a` (`GI.Proved.dixon_commutator_le_centralizer`).

*Proof.* By `GI.Proved.dixon_semiregular`, `A` acts semiregularly on `V \ {1}`. For `x ∈ A` with
`x ≠ 1` and `x^q = 1`, the product `Φ_x(v) = ∏_{j<q} x^j v` is fixed by `x`, so it is `1`.
Let `b = h a h⁻¹` and suppose `b` is not a power of `a`. Then no `a^i b` is `1`, and
`1 = ∏_{i<q} Φ_{a^i b}(v) = ∏_{j<q} Φ_{a^j}(b^j v) = v^q`, because `(a^i b)^j = (a^j)^i b^j` and
the factors with `j ≠ 0` are `1`. So a nonidentity `v` has order `q`, and `q` divides `|V|`.
But `⟨a⟩` is a `q`-group whose only fixed point is `1`, so `|V| ≡ 1 (mod q)`. This is a
contradiction.
-/

namespace GI.Proved

open MulAction Subgroup
open scoped commutatorElement

variable {H V : Type*} [Group H] [CommGroup V] [MulDistribMulAction H V]

omit [CommGroup V] [MulDistribMulAction H V] in
/-- If every conjugate of `a` is a power of `a`, then every commutator commutes with `a`. -/
theorem dixon_commutator_le_centralizer {a : H} (hn : ∀ h : H, h * a * h⁻¹ ∈ zpowers a) :
    commutator H ≤ centralizer {a} := by
  have hconj : ∀ x y : H, (x * y) * a * (x * y)⁻¹ = (y * x) * a * (y * x)⁻¹ := by
    intro x y
    obtain ⟨kx, hkx⟩ := mem_zpowers_iff.mp (hn x)
    obtain ⟨ky, hky⟩ := mem_zpowers_iff.mp (hn y)
    have e1 : (x * y) * a * (x * y)⁻¹ = x * (y * a * y⁻¹) * x⁻¹ := by group
    have e2 : (y * x) * a * (y * x)⁻¹ = y * (x * a * x⁻¹) * y⁻¹ := by group
    rw [e1, e2, ← hky, ← hkx, ← conj_zpow, ← conj_zpow, ← hkx, ← hky, ← zpow_mul, ← zpow_mul,
      mul_comm]
  rw [commutator_def, commutator_le]
  intro x _ y _
  rw [mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  rw [hz]
  obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hn (y * x)⁻¹)
  rw [inv_inv] at hm
  have h1 : (x * y) * a ^ m * (x * y)⁻¹ = a := by
    rw [← conj_zpow, hconj, conj_zpow, hm]
    group
  have h2 : ⁅x, y⁆ * a * ⁅x, y⁆⁻¹ = (x * y) * ((y * x)⁻¹ * a * (y * x)) * (x * y)⁻¹ := by
    rw [commutatorElement_def]
    group
  have h3 : ⁅x, y⁆ * a * ⁅x, y⁆⁻¹ = a := by rw [h2, ← hm, h1]
  rw [mul_inv_eq_iff_eq_mul] at h3
  exact h3.symm

variable [FaithfulSMul H V]

omit [FaithfulSMul H V] in
/-- `∏_{j<q} x^j v` is fixed by `x` when `x^q = 1`. -/
theorem dixon_smul_prod_pow {x : H} {q : ℕ} (hxq : x ^ q = 1) (v : V) :
    x • ∏ j ∈ Finset.range q, (x ^ j) • v = ∏ j ∈ Finset.range q, (x ^ j) • v := by
  rw [Finset.smul_prod']
  have h := Finset.prod_range_succ' (fun j => (x ^ j) • v) q
  rw [Finset.prod_range_succ, pow_zero, one_smul, hxq, one_smul] at h
  simp only [← mul_smul, ← pow_succ']
  exact (mul_right_cancel h).symm

/-- **Conjugates of `a` are powers of `a`.** -/
theorem dixon_conj_mem_zpowers [Finite H] [Finite V] [Nontrivial V]
    (htr : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ h : H, h • v = w)
    (A : Subgroup H) [A.Normal] (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    {q : ℕ} [hq : Fact q.Prime] {a : H} (haA : a ∈ A) (hao : orderOf a = q) (h : H) :
    h * a * h⁻¹ ∈ zpowers a := by
  have hsr := fun {x} (hx : x ∈ A) {v : V} (hv : v ≠ 1) (hxv : x • v = v) =>
    dixon_semiregular htr A hA hx hv hxv
  -- `Φ_x(v) = 1`
  have hphi : ∀ x ∈ A, x ≠ 1 → x ^ q = 1 → ∀ v : V,
      ∏ j ∈ Finset.range q, (x ^ j) • v = 1 := by
    intro x hx hx1 hxq v
    by_contra hne
    exact hx1 (hsr hx hne (dixon_smul_prod_pow hxq v))
  have haq : a ^ q = 1 := hao ▸ pow_orderOf_eq_one a
  set b := h * a * h⁻¹ with hb
  have hbA : b ∈ A := (inferInstance : A.Normal).conj_mem a haA h
  have hbq : b ^ q = 1 := by rw [hb, conj_pow, haq]; group
  by_contra hbz
  have hab : ∀ i : ℕ, a ^ i * b ≠ 1 := by
    intro i hi
    apply hbz
    rw [eq_inv_of_mul_eq_one_right hi]
    exact (zpowers a).inv_mem (npow_mem_zpowers a i)
  have hcomm : ∀ i j : ℕ, (a ^ i * b) ^ j = (a ^ j) ^ i * b ^ j := by
    intro i j
    rw [(Commute.mul_pow (hA _ (A.pow_mem haA i) _ hbA) j), ← pow_mul, ← pow_mul, mul_comm i j]
  have hvq : ∀ v : V, v ^ q = 1 := by
    intro v
    have h0 : ∏ i ∈ Finset.range q, ∏ j ∈ Finset.range q, ((a ^ i * b) ^ j) • v = 1 := by
      apply Finset.prod_eq_one
      intro i _
      apply hphi _ (A.mul_mem (A.pow_mem haA i) hbA) (hab i)
      rw [Commute.mul_pow (hA _ (A.pow_mem haA i) _ hbA), ← pow_mul, mul_comm, pow_mul, haq,
        one_pow, hbq, one_mul]
    simp only [hcomm, mul_smul] at h0
    rw [Finset.prod_comm, Finset.prod_eq_single 0] at h0
    · simpa using h0
    · intro j hj hj0
      apply hphi _ (A.pow_mem haA j) (pow_ne_one_of_lt_orderOf hj0 (hao ▸ Finset.mem_range.mp hj))
      rw [← pow_mul, mul_comm, pow_mul, haq, one_pow]
    · intro h0q
      exact absurd (Finset.mem_range.mpr hq.out.pos) h0q
  obtain ⟨v, hv⟩ := exists_ne (1 : V)
  have hov : orderOf v = q := by
    rcases hq.out.eq_one_or_self_of_dvd _ (orderOf_dvd_of_pow_eq_one (hvq v)) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hv
    · exact h1
  have hdvd : q ∣ Nat.card V := hov ▸ orderOf_dvd_natCard v
  have hpg : IsPGroup q (zpowers a) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
  have hfix : fixedPoints (zpowers a) V = {1} := by
    ext w
    rw [mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hw
      by_contra hw1
      have := hsr haA hw1 (hw ⟨a, mem_zpowers a⟩)
      rw [this, orderOf_one] at hao
      exact hq.out.one_lt.ne hao
    · rintro rfl g
      exact smul_one _
  have hmod := hpg.card_modEq_card_fixedPoints V
  rw [hfix, Nat.card_coe_set_eq, Set.ncard_singleton] at hmod
  have h01 : 0 ≡ 1 [MOD q] := ((Nat.modEq_zero_iff_dvd.mpr hdvd).symm).trans hmod
  have := (Nat.modEq_iff_dvd' (Nat.zero_le 1)).mp h01
  exact hq.out.one_lt.ne' (Nat.dvd_one.mp this)

end GI.Proved
