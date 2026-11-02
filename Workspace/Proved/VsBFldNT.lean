import Mathlib

/-!
# Number theory for the field line

The field-line base finds the kernel of `λ : H → L*` by a chain of small orbits, one for each
prime `q ≤ n`. At the stage of `q` an element acts through `λ(h)^{F_q}`, where `F_q` is the
product of the numbers `j ≤ n` that `q` does not divide. This file proves the two facts the
chain needs. The stages of the chain are `q = 2, …, max n 2`.

* `vsBE n` is `lcm(1, …, n)`; the order of a permutation of `Fin n` divides it (`vsB_orderOf_dvd`).
* `vsB_dvd_F`: for `q ≥ 2` with least prime factor `r`, `lcm(1, …, n)` divides `F_q · r^{log_r n}`.
  So `λ(h)^{F_q}` is a root of unity of order at most `n + 1`, and the orbits of the chain are
  small. (No primality test is needed: the stages run over all `2 ≤ q ≤ max n 2`.)
* `vsB_eq_one`: if `x^{F_q} = 1` for every `2 ≤ q ≤ max n 2`, then `x = 1`.
* `vsB_roots_le`: in a commutative domain, at most `R` elements have `z^R = 1`.
-/

namespace GI.Proved

/-- `lcm(1, …, n)`. -/
def vsBE (n : ℕ) : ℕ := (Finset.Icc 1 n).lcm id

/-- The product of the numbers `1 ≤ j ≤ n` not divisible by `q`. -/
def vsBF (n q : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun j => ¬ q ∣ j).prod id

theorem vsB_dvd_E {n j : ℕ} (h1 : 1 ≤ j) (hj : j ≤ n) : j ∣ vsBE n :=
  Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨h1, hj⟩)

theorem vsB_orderOf_dvd {n : ℕ} (σ : Equiv.Perm (Fin n)) : orderOf σ ∣ vsBE n := by
  rw [← Equiv.Perm.lcm_cycleType]
  refine Multiset.lcm_dvd.mpr fun k hk => ?_
  have h2 := Equiv.Perm.two_le_of_mem_cycleType hk
  have hle := (Equiv.Perm.le_card_support_of_mem_cycleType hk).trans (Finset.card_le_univ _)
  rw [Fintype.card_fin] at hle
  exact vsB_dvd_E (by omega) hle

theorem vsB_dvd_F {n q : ℕ} (hq : 2 ≤ q) :
    vsBE n ∣ vsBF n q * q.minFac ^ Nat.log q.minFac n := by
  have hr := Nat.minFac_prime (show q ≠ 1 by omega)
  refine Finset.lcm_dvd fun j hj => ?_
  obtain ⟨h1, hjn⟩ := Finset.mem_Icc.mp hj
  obtain ⟨e, j', hj', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show j ≠ 0 by omega) q.minFac hr.ne_one
  have hj'0 : j' ≠ 0 := by rintro rfl; simp at h1
  rw [id, Nat.mul_comm (q.minFac ^ e)]
  refine Nat.mul_dvd_mul ?_ (Nat.pow_dvd_pow _ ?_)
  · refine Finset.dvd_prod_of_mem (f := id) (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩,
      fun hqj => hj' ((Nat.minFac_dvd q).trans hqj)⟩)
    · omega
    · exact le_trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos hr.pos)) hjn
  · refine Nat.le_log_of_pow_le hr.one_lt (le_trans ?_ hjn)
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hj'0)

theorem vsB_log_pow_le {n q : ℕ} (hn : 1 ≤ n) : q ^ Nat.log q n ≤ n :=
  Nat.pow_log_le_self q (by omega)

/-- A prime divides `F_q` only if it is not `q`. -/
theorem vsB_not_dvd_F {n q : ℕ} (hq : q.Prime) : ¬ q ∣ vsBF n q := by
  intro h
  obtain ⟨j, hj, hqj⟩ := (Prime.dvd_finset_prod_iff hq.prime id).mp h
  exact (Finset.mem_filter.mp hj).2 hqj

theorem vsB_prime_le {n q : ℕ} (hq : q.Prime) (h : q ∣ vsBE n) : q ≤ n := by
  by_contra hlt
  have : vsBE n ∣ ((Finset.Icc 1 n).filter fun j => ¬ q ∣ j).prod id := by
    refine Finset.lcm_dvd fun j hj => Finset.dvd_prod_of_mem (f := id)
      (Finset.mem_filter.mpr ⟨hj, fun hd => ?_⟩)
    obtain ⟨h1, hjn⟩ := Finset.mem_Icc.mp hj
    have := Nat.le_of_dvd (by omega) hd
    omega
  exact vsB_not_dvd_F hq (h.trans this)

/-- The end of the chain: an element killed by every `F_q`, `2 ≤ q ≤ max n 2`, is `1`. -/
theorem vsB_eq_one {M : Type*} [Monoid M] {n : ℕ} {x : M}
    (hF : ∀ q, 2 ≤ q → q ≤ max n 2 → x ^ vsBF n q = 1) : x = 1 := by
  have hpos : 0 < vsBF n 2 := Finset.prod_pos fun j hj => by
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1; simpa using this
  have ho : orderOf x ∣ vsBF n 2 := orderOf_dvd_of_pow_eq_one (hF 2 le_rfl (le_max_right _ _))
  rw [← orderOf_eq_one_iff]
  by_contra hne
  have hq := Nat.minFac_prime hne
  set r := (orderOf x).minFac
  have hro : r ∣ orderOf x := Nat.minFac_dvd _
  obtain ⟨j, hj, hrj⟩ := (Prime.dvd_finset_prod_iff hq.prime id).mp (hro.trans ho)
  obtain ⟨hjI, -⟩ := Finset.mem_filter.mp hj
  obtain ⟨h1, hjn⟩ := Finset.mem_Icc.mp hjI
  have hrj' : r ∣ j := hrj
  have hrn : r ≤ n := (Nat.le_of_dvd (by omega) hrj').trans hjn
  exact vsB_not_dvd_F hq (hro.trans (orderOf_dvd_of_pow_eq_one
    (hF r hq.two_le (hrn.trans (le_max_left _ _)))))

/-- The orbit bound: `x^{F_q}` is killed by `r^{log_r n}`, `r` the least prime factor of `q`. -/
theorem vsB_pow_F {M : Type*} [Monoid M] {n q : ℕ} (hq : 2 ≤ q) {x : M} (hE : x ^ vsBE n = 1) :
    (x ^ vsBF n q) ^ (q.minFac ^ Nat.log q.minFac n) = 1 := by
  rw [← pow_mul]
  obtain ⟨c, hc⟩ := vsB_dvd_F (n := n) hq
  rw [hc, pow_mul, hE, one_pow]

theorem vsB_minFac_pow_le (n q : ℕ) : q.minFac ^ Nat.log q.minFac n ≤ n + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (Nat.pow_log_le_self _ (by omega)).trans (by omega)

/-- In a commutative domain at most `R` elements are `R`-th roots of `1`. -/
theorem vsB_roots_le {A : Type*} [CommRing A] [Nontrivial A]
    (hA : ∀ a b : A, a * b = 0 → a = 0 ∨ b = 0) {R : ℕ} (hR : 0 < R) :
    {z : A | z ^ R = 1}.ncard ≤ R := by
  classical
  haveI : NoZeroDivisors A := ⟨fun h => hA _ _ h⟩
  haveI : IsDomain A := NoZeroDivisors.to_isDomain A
  have : {z : A | z ^ R = 1} = ((Polynomial.nthRoots R (1 : A)).toFinset : Set A) := by
    ext z; simp [Polynomial.mem_nthRoots hR]
  rw [this, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots R 1)

end GI.Proved

namespace GI.Proved

/-- The walk that computes `x^{F_q}`: for `j = 1, …, n`, raise to the power `j` unless `q ∣ j`. -/
def vsBWalk {M : Type*} [Monoid M] (n q : ℕ) (x : M) : M :=
  (List.range n).foldl (fun X i => if q ∣ i + 1 then X else X ^ (i + 1)) x

theorem vsBF_succ (n q : ℕ) : vsBF (n + 1) q = vsBF n q * (if q ∣ n + 1 then 1 else n + 1) := by
  unfold vsBF
  rw [Finset.prod_filter, Finset.prod_filter, Finset.prod_Icc_succ_top (by omega)]
  simp only [id]
  split_ifs <;> simp

theorem vsBWalk_eq {M : Type*} [Monoid M] (n q : ℕ) (x : M) : vsBWalk n q x = x ^ vsBF n q := by
  induction n with
  | zero => simp [vsBWalk, vsBF]
  | succ n ih =>
    rw [vsBWalk, List.range_succ, List.foldl_append, ← vsBWalk, ih, vsBF_succ]
    simp only [List.foldl_cons, List.foldl_nil]
    split_ifs <;> simp [pow_mul]

end GI.Proved
