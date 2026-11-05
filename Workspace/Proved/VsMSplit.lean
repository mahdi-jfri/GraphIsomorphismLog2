module

public import Workspace.Proved.VsMFourier
public import Workspace.Proved.VsMBlocks

@[expose] public section

/-!
# The pieces of `𝔽_p[A ∪ {t_i}]` for commuting `t_i` of order `r`

Setting (`VsMSplitHyp`): `L = 𝔽_p[A]` is a field, `ζ ∈ S` has order `r` (prime), and
`t_1, …, t_k` commute with each other and with `A`, with `t_i ^ r = 1`. Then `r ≠ p`, and in the
commutative algebra `B = 𝔽_p[A ∪ {t_i}]` the idempotents `π_c` of `VsMFourier.lean` exist
(`c : Fin k → ZMod r`). The candidate pieces are
`P c = ⋂_i ker (t_i - ζ^(c_i))` (`vsMP`), and `P c` is the image of `π_c`.

* Every `y ∈ B` acts on `P c` as an element of `L`; a Frobenius fixed point acts as a scalar.
* `B` has no nonzero `y` with `y ^ p = 0`.
* If there are shift elements `s_i` (`s_i t_j s_i⁻¹ = ζ^(δ_ij) t_j`, `s_i` centralizing `A`),
  all `P c` have the same dimension and are nonzero, and the nonzero joint eigenspaces of any
  spanning family of Frobenius fixed points are exactly the `P c`: there are `r ^ k` of them.
* A unit commuting with all `t_i` and with `ζ` fixes each piece; this bounds the index of the
  stabilizer by `r ^ k · r` in any group whose elements move `t_i` and `ζ` only by scalars.
-/

namespace GI.Proved

open Module Polynomial
open scoped commutatorElement IsMulCommutative

variable {p : ℕ} [hp : Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

local notation "𝔼" => End (ZMod p) V

/-- Sums over `ZMod r` of a function of the value. -/
theorem vsM_sum_zmod {M : Type*} [AddCommMonoid M] {r : ℕ} [NeZero r] (f : ℕ → M) :
    ∑ l : ZMod r, f l.val = ∑ n ∈ Finset.range r, f n := by
  refine Finset.sum_nbij' (fun l => l.val) (fun n => (n : ZMod r)) ?_ ?_ ?_ ?_ ?_
  · intro l _; exact Finset.mem_range.2 (ZMod.val_lt l)
  · intro _ _; exact Finset.mem_univ _
  · intro l _; exact ZMod.natCast_zmod_val l
  · intro n hn; exact ZMod.val_cast_of_lt (Finset.mem_range.1 hn)
  · intro l _; rfl

/-- The hypotheses of the split. -/
structure VsMSplitHyp (A : Subgroup 𝔼ˣ) (r : ℕ) (ζ : 𝔼ˣ) {k : ℕ} (t : Fin k → 𝔼ˣ) : Prop where
  hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a
  hdom : vsTDom (vsTAlg A)
  hr : r.Prime
  hζ : ζ ∈ vsMScal A
  hζ1 : ζ ≠ 1
  hζr : ζ ^ r = 1
  htA : ∀ i, t i ∈ Subgroup.centralizer (A : Set 𝔼ˣ)
  htt : ∀ i j, t i * t j = t j * t i
  htr : ∀ i, t i ^ r = 1

/-- The candidate piece `P c = ⋂_i ker (t_i - ζ^(c_i))`. -/
def vsMP {r : ℕ} (ζ : 𝔼ˣ) {k : ℕ} (t : Fin k → 𝔼ˣ) (c : Fin k → ZMod r) :
    Submodule (ZMod p) V :=
  ⨅ i, LinearMap.ker ((t i : 𝔼) - (ζ : 𝔼) ^ (c i).val)

theorem mem_vsMP {r : ℕ} (ζ : 𝔼ˣ) {k : ℕ} (t : Fin k → 𝔼ˣ) (c : Fin k → ZMod r) (v : V) :
    v ∈ vsMP ζ t c ↔ ∀ i, (t i : 𝔼) v = ((ζ : 𝔼) ^ (c i).val) v := by
  simp only [vsMP, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]

section Hyp

variable [FiniteDimensional (ZMod p) V] [Nontrivial V] {A : Subgroup (End (ZMod p) V)ˣ} {r : ℕ}
  {ζ : (End (ZMod p) V)ˣ}
  {k : ℕ} {t : Fin k → (End (ZMod p) V)ˣ}

theorem VsMSplitHyp.L_le (h : VsMSplitHyp A r ζ t) : vsTAlg A ≤ vsMAlgE A t :=
  Algebra.adjoin_mono Set.subset_union_left

theorem VsMSplitHyp.gen_comm (h : VsMSplitHyp A r ζ t) :
    ∀ x ∈ vsTSet A ∪ Set.range (fun i => ((t i : 𝔼ˣ) : 𝔼)),
      ∀ y ∈ vsTSet A ∪ Set.range (fun i => ((t i : 𝔼ˣ) : 𝔼)), x * y = y * x := by
  have hta : ∀ i, ∀ a ∈ A, ((t i : 𝔼ˣ) : 𝔼) * (a : 𝔼) = (a : 𝔼) * (t i : 𝔼) := by
    intro i a ha
    rw [← Units.val_mul, ← Units.val_mul, (Subgroup.mem_centralizer_iff.1 (h.htA i) a ha)]
  rintro _ (⟨a, ha, rfl⟩ | ⟨i, rfl⟩) _ (⟨b, hb, rfl⟩ | ⟨j, rfl⟩)
  · rw [← Units.val_mul, ← Units.val_mul, h.hA a ha b hb]
  · exact (hta j a ha).symm
  · exact hta i b hb
  · simp only; rw [← Units.val_mul, ← Units.val_mul, h.htt]

theorem VsMSplitHyp.comm (h : VsMSplitHyp A r ζ t) :
    ∀ x ∈ vsMAlgE A t, ∀ y ∈ vsMAlgE A t, Commute x y := by
  haveI : IsMulCommutative (vsMAlgE A t) :=
    Algebra.isMulCommutative_adjoin (ZMod p) (fun x hx y hy _ => h.gen_comm x hx y hy)
  intro x hx y hy
  have : (⟨x, hx⟩ : vsMAlgE A t) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := IsMulCommutative.is_comm.comm _ _
  exact congrArg Subtype.val this

theorem VsMSplitHyp.ζ_mem (h : VsMSplitHyp A r ζ t) : (ζ : 𝔼) ∈ vsMAlgE A t := h.L_le h.hζ.1

theorem VsMSplitHyp.t_mem (h : VsMSplitHyp A r ζ t) (i : Fin k) : (t i : 𝔼) ∈ vsMAlgE A t :=
  Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)

theorem VsMSplitHyp.ord (h : VsMSplitHyp A r ζ t) : orderOf ζ = r := by
  haveI : Fact r.Prime := ⟨h.hr⟩
  exact orderOf_eq_prime h.hζr h.hζ1

/-- A nonzero element of `L` is injective. -/
theorem VsMSplitHyp.inj (h : VsMSplitHyp A r ζ t) {l : 𝔼} (hl : l ∈ vsTAlg A) (hl0 : l ≠ 0) :
    ∀ v, l v = 0 → v = 0 := by
  rcases h.hdom l hl with h0 | hi
  · exact absurd h0 hl0
  · exact hi

/-- `ζ^a = ζ^b` with `a, b : ZMod r` forces `a = b`. -/
theorem VsMSplitHyp.zp_inj (h : VsMSplitHyp A r ζ t) {a b : ZMod r}
    (hab : (ζ : 𝔼) ^ a.val = (ζ : 𝔼) ^ b.val) : a = b := by
  haveI : NeZero r := ⟨h.hr.ne_zero⟩
  have h1 : ζ ^ a.val = ζ ^ b.val := Units.ext (by rw [Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, hab])
  have := pow_injOn_Iio_orderOf (x := ζ) (by rw [h.ord]; exact ZMod.val_lt a)
    (by rw [h.ord]; exact ZMod.val_lt b) h1
  exact ZMod.val_injective r this

/-- `r ≠ p`: in characteristic `p` there is no nontrivial `p`-th root of unity in a domain. -/
theorem VsMSplitHyp.r_ne (h : VsMSplitHyp A r ζ t) : (r : ZMod p) ≠ 0 := by
  intro hr0
  have hpr : p = r := by
    rw [ZMod.natCast_eq_zero_iff] at hr0
    exact ((Nat.prime_dvd_prime_iff_eq hp.out h.hr).1 hr0)
  subst hpr
  have hd : (ζ : 𝔼) - 1 ∈ vsTAlg A := sub_mem h.hζ.1 (one_mem _)
  have hd0 : (ζ : 𝔼) - 1 ≠ 0 := by
    intro h0
    exact h.hζ1 (Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h0))
  have hp0 : ((ζ : 𝔼) - 1) ^ p = 0 := by
    rw [vsFA_sub_pow (Commute.one_right _), one_pow, ← Units.val_pow_eq_pow_val, h.hζr,
      Units.val_one, sub_self]
  -- an injective map has injective powers
  have hinj := h.inj hd hd0
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have : ∀ n : ℕ, ∀ w : V, (((ζ : 𝔼) - 1) ^ n) w = 0 → w = 0 := by
    intro n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
      intro w hw
      rw [pow_succ, Module.End.mul_apply] at hw
      exact hinj _ (ih _ hw)
  exact hv (this p v (by rw [hp0, LinearMap.zero_apply]))

/-- `∑_l ζ^(m l) = 0` for `m ≠ 0`. -/
theorem VsMSplitHyp.geo (h : VsMSplitHyp A r ζ t) (m : ZMod r) (hm : m ≠ 0) :
    haveI : NeZero r := ⟨h.hr.ne_zero⟩
    ∑ l : ZMod r, (ζ : 𝔼) ^ (m * l).val = 0 := by
  haveI : NeZero r := ⟨h.hr.ne_zero⟩
  have hζr : (ζ : 𝔼) ^ r = 1 := by rw [← Units.val_pow_eq_pow_val, h.hζr, Units.val_one]
  set η := (ζ : 𝔼) ^ m.val
  have h1 : ∑ l : ZMod r, (ζ : 𝔼) ^ (m * l).val = ∑ n ∈ Finset.range r, η ^ n := by
    rw [← vsM_sum_zmod (fun n => η ^ n)]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm, vsM_zp_mul hζr]
  rw [h1]
  have hη : η ∈ vsTAlg A := pow_mem h.hζ.1 _
  have hη1 : η - 1 ≠ 0 := by
    intro h0
    apply hm
    have : (ζ : 𝔼) ^ m.val = (ζ : 𝔼) ^ (0 : ZMod r).val := by
      rw [ZMod.val_zero, pow_zero]; exact sub_eq_zero.1 h0
    exact h.zp_inj this
  have hgs : (∑ n ∈ Finset.range r, η ^ n) * (η - 1) = 0 := by
    rw [geom_sum_mul, ← pow_mul, mul_comm, pow_mul, hζr, one_pow, sub_self]
  have hsL : (∑ n ∈ Finset.range r, η ^ n) ∈ vsTAlg A := sum_mem fun n _ => pow_mem hη n
  have hcomm := (vsTAlg_comm h.hA _ hsL _ (sub_mem hη (one_mem _))).eq
  rw [hcomm] at hgs
  ext v
  exact h.inj (sub_mem hη (one_mem _)) hη1 _ (by
    rw [← Module.End.mul_apply, hgs, LinearMap.zero_apply])

/-- Powers of an injective map are injective. -/
theorem vsM_pow_inj' {l : 𝔼} (hl : ∀ v, l v = 0 → v = 0) :
    ∀ (n : ℕ) (w : V), (l ^ n) w = 0 → w = 0 := by
  intro n
  induction n with
  | zero => intro w hw; simpa using hw
  | succ n ih =>
    intro w hw
    rw [pow_succ, Module.End.mul_apply] at hw
    exact hl _ (ih _ hw)

/-- The idempotents `π_c`, as endomorphisms. -/
def VsMIdemProp (A : Subgroup 𝔼ˣ) {r : ℕ} [NeZero r] (ζ : 𝔼ˣ) {k : ℕ} (t : Fin k → 𝔼ˣ)
    (π : (Fin k → ZMod r) → 𝔼) : Prop :=
  (∀ c, π c ∈ vsMAlgE A t) ∧ ∑ c, π c = 1 ∧
    (∀ c c', π c' * π c = if c' = c then π c else 0) ∧
    ∀ c i, (t i : 𝔼) * π c = (ζ : 𝔼) ^ (c i).val * π c

theorem VsMSplitHyp.idem [NeZero r] (h : VsMSplitHyp A r ζ t) :
    ∃ π : (Fin k → ZMod r) → 𝔼, VsMIdemProp A ζ t π := by
  haveI : IsMulCommutative (vsMAlgE A t) :=
    Algebra.isMulCommutative_adjoin (ZMod p) (fun x hx y hy _ => h.gen_comm x hx y hy)
  let ζR : vsMAlgE A t := ⟨ζ, h.ζ_mem⟩
  let tR : Fin k → vsMAlgE A t := fun i => ⟨t i, h.t_mem i⟩
  have hζR : ζR ^ r = 1 := Subtype.ext (by
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    change (ζ : 𝔼) ^ r = 1
    rw [← Units.val_pow_eq_pow_val, h.hζr, Units.val_one])
  have htR : ∀ i, tR i ^ r = 1 := fun i => Subtype.ext (by
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    change (t i : 𝔼) ^ r = 1
    rw [← Units.val_pow_eq_pow_val, h.htr i, Units.val_one])
  have hgeo : ∀ m : ZMod r, m ≠ 0 → ∑ l : ZMod r, ζR ^ (m * l).val = 0 := by
    intro m hm
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum, ZeroMemClass.coe_zero]
    simp only [SubmonoidClass.coe_pow]
    exact h.geo m hm
  refine ⟨fun c => ((vsMIdemP (ZMod p) ζR tR c : vsMAlgE A t) : 𝔼),
    fun c => (vsMIdemP (ZMod p) ζR tR c : vsMAlgE A t).2,
    ?_, ?_, ?_⟩
  · have := congrArg Subtype.val (vsM_idemP_sum hζR hgeo h.r_ne htR)
    rw [AddSubmonoidClass.coe_finset_sum, OneMemClass.coe_one] at this
    exact this
  · intro c c'
    have := congrArg Subtype.val (vsM_idemP_mul hζR hgeo h.r_ne htR c c')
    rw [MulMemClass.coe_mul] at this
    split_ifs at this ⊢ with hc
    · exact this
    · rw [this, ZeroMemClass.coe_zero]
  · intro c i
    have := congrArg Subtype.val (vsM_idemP_eig (K := ZMod p) hζR htR c i)
    rw [MulMemClass.coe_mul, MulMemClass.coe_mul, SubmonoidClass.coe_pow] at this
    exact this

variable [NeZero r] {π : (Fin k → ZMod r) → End (ZMod p) V}

theorem VsMSplitHyp.mem_P (h : VsMSplitHyp A r ζ t) (hπ : VsMIdemProp A ζ t π)
    (c : Fin k → ZMod r) (v : V) : v ∈ vsMP ζ t c ↔ π c v = v := by
  constructor
  · intro hv
    rw [mem_vsMP] at hv
    have h0 : ∀ c', c' ≠ c → π c' v = 0 := by
      intro c' hc'
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hc'
      set w := π c' v
      have h1 : (t i : 𝔼) w = ((ζ : 𝔼) ^ (c' i).val) w := by
        simp only [w]; rw [← Module.End.mul_apply, hπ.2.2.2, Module.End.mul_apply]
      have h2 : (t i : 𝔼) w = ((ζ : 𝔼) ^ (c i).val) w := by
        simp only [w]
        rw [← Module.End.mul_apply, ((h.comm _ (h.t_mem i) _ (hπ.1 c'))).eq,
          Module.End.mul_apply, hv i, ← Module.End.mul_apply, ← Module.End.mul_apply,
          ((h.comm _ (hπ.1 c') _ (pow_mem h.ζ_mem _))).eq]
      have hd : (ζ : 𝔼) ^ (c i).val - (ζ : 𝔼) ^ (c' i).val ≠ 0 := by
        intro h0
        exact hi (h.zp_inj (sub_eq_zero.1 h0)).symm
      exact h.inj (sub_mem (pow_mem h.hζ.1 _) (pow_mem h.hζ.1 _)) hd w (by
        rw [LinearMap.sub_apply, ← h1, ← h2, sub_self])
    have := congrArg (fun f : 𝔼 => f v) hπ.2.1
    simp only [LinearMap.sum_apply, Module.End.one_apply] at this
    rw [Finset.sum_eq_single c (fun c' _ hc' => h0 c' hc') (fun h' => absurd (Finset.mem_univ c) h')]
      at this
    exact this
  · intro hv
    rw [mem_vsMP]
    intro i
    rw [← hv, ← Module.End.mul_apply, hπ.2.2.2, Module.End.mul_apply]

theorem VsMSplitHyp.π_mem_P (h : VsMSplitHyp A r ζ t) (hπ : VsMIdemProp A ζ t π)
    (c : Fin k → ZMod r) (v : V) : π c v ∈ vsMP ζ t c := by
  rw [h.mem_P hπ, ← Module.End.mul_apply, hπ.2.2.1 c c, if_pos rfl]

theorem VsMSplitHyp.P_disj (h : VsMSplitHyp A r ζ t) (hπ : VsMIdemProp A ζ t π)
    {c c' : Fin k → ZMod r} (hc : c ≠ c') {v : V} (hv : v ∈ vsMP ζ t c) (hv' : v ∈ vsMP ζ t c') :
    v = 0 := by
  rw [h.mem_P hπ] at hv hv'
  rw [← hv, ← hv', ← Module.End.mul_apply, hπ.2.2.1 c' c, if_neg hc, LinearMap.zero_apply]

theorem VsMSplitHyp.exists_P (h : VsMSplitHyp A r ζ t) (hπ : VsMIdemProp A ζ t π) :
    ∃ c : Fin k → ZMod r, vsMP ζ t c ≠ ⊥ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  by_contra hall
  push Not at hall
  apply hv
  have := congrArg (fun f : 𝔼 => f v) hπ.2.1
  simp only [LinearMap.sum_apply, Module.End.one_apply] at this
  rw [← this]
  refine Finset.sum_eq_zero fun c _ => ?_
  have := h.π_mem_P hπ c v
  rw [hall c] at this
  exact (Submodule.mem_bot _).1 this

/-- Every `y ∈ B` acts on the image of `π_c` as an element of `L`. -/
theorem VsMSplitHyp.act (h : VsMSplitHyp A r ζ t) (hπ : VsMIdemProp A ζ t π)
    (c : Fin k → ZMod r) {y : 𝔼} (hy : y ∈ vsMAlgE A t) :
    ∃ l ∈ vsTAlg A, y * π c = l * π c := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | ⟨i, rfl⟩
    · exact ⟨x, Algebra.subset_adjoin hx, rfl⟩
    · exact ⟨_, pow_mem h.hζ.1 _, hπ.2.2.2 c i⟩
  | algebraMap a => exact ⟨_, Subalgebra.algebraMap_mem _ a, rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨l1, hl1, e1⟩ := hx
    obtain ⟨l2, hl2, e2⟩ := hy
    exact ⟨l1 + l2, add_mem hl1 hl2, by rw [add_mul, add_mul, e1, e2]⟩
  | mul x y hx' _ hx hy =>
    obtain ⟨l1, hl1, e1⟩ := hx
    obtain ⟨l2, hl2, e2⟩ := hy
    refine ⟨l2 * l1, mul_mem hl2 hl1, ?_⟩
    rw [mul_assoc, e2, ← mul_assoc, (h.comm _ hx' _ (h.L_le hl2)).eq, mul_assoc, e1, ← mul_assoc]

theorem VsMSplitHyp.act_pow (h : VsMSplitHyp A r ζ t) (hπ : VsMIdemProp A ζ t π)
    (c : Fin k → ZMod r) {y l : 𝔼} (hy : y ∈ vsMAlgE A t) (hl : l ∈ vsTAlg A)
    (e : y * π c = l * π c) (n : ℕ) : y ^ n * π c = l ^ n * π c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, (h.comm _ hy _ (h.L_le (pow_mem hl n))).eq,
      mul_assoc, e, ← mul_assoc, pow_succ]

/-- A Frobenius fixed point of `L` is a scalar. -/
theorem VsMSplitHyp.fix_scalar (h : VsMSplitHyp A r ζ t) {l : 𝔼} (hl : l ∈ vsTAlg A)
    (hlp : l ^ p = l) : ∃ a : ZMod p, l = algebraMap (ZMod p) 𝔼 a := by
  classical
  have hq : (X ^ p - X : (ZMod p)[X]) ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) hp.out.one_lt
  have hcard := vsT_card_roots (vsTSet_comm h.hA) h.hdom hq
  rw [natDegree_sub_eq_left_of_natDegree_lt (by
    rw [natDegree_X, natDegree_X_pow]; exact hp.out.one_lt), natDegree_X_pow] at hcard
  set T := {x : 𝔼 | x ∈ Algebra.adjoin (ZMod p) (vsTSet A) ∧
    aeval x (X ^ p - X : (ZMod p)[X]) = 0}
  set I := Set.range (algebraMap (ZMod p) 𝔼)
  have hIT : I ⊆ T := by
    rintro _ ⟨a, rfl⟩
    refine ⟨Subalgebra.algebraMap_mem _ a, ?_⟩
    rw [map_sub, map_pow, aeval_X, ← map_pow, ZMod.pow_card, sub_self]
  have hIcard : I.ncard = p := by
    rw [Set.ncard_range_of_injective (algebraMap (ZMod p) 𝔼).injective, Nat.card_zmod]
  have hTfin : T.Finite := by
    haveI : Finite V := Module.finite_of_finite (ZMod p)
    exact Set.toFinite T
  have hIeq : I = T := Set.eq_of_subset_of_ncard_le hIT (hcard.trans hIcard.ge) hTfin
  have hlT : l ∈ T := ⟨hl, by rw [map_sub, map_pow, aeval_X, hlp, sub_self]⟩
  rw [← hIeq] at hlT
  obtain ⟨a, ha⟩ := hlT
  exact ⟨a, ha.symm⟩

/-- A Frobenius fixed point of `B` acts on `P c` as a scalar. -/
theorem VsMSplitHyp.fix_act (h : VsMSplitHyp A r ζ t) (hπ : VsMIdemProp A ζ t π)
    (c : Fin k → ZMod r) {y : 𝔼} (hy : y ∈ vsMAlgE A t) (hyp : y ^ p = y) :
    ∃ a : ZMod p, ∀ v ∈ vsMP ζ t c, y v = a • v := by
  by_cases hP : vsMP ζ t c = ⊥
  · exact ⟨0, fun v hv => by rw [hP, Submodule.mem_bot] at hv; simp [hv]⟩
  obtain ⟨v0, hv0, hv00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
  obtain ⟨l, hl, e⟩ := h.act hπ c hy
  have e' := h.act_pow hπ c hy hl e p
  rw [hyp, e] at e'
  have hlp : l ^ p = l := by
    by_contra hne
    apply hv00
    refine h.inj (sub_mem (pow_mem hl p) hl) (sub_ne_zero.2 hne) v0 ?_
    have hv0' := (h.mem_P hπ c v0).1 hv0
    rw [← hv0', LinearMap.sub_apply, ← Module.End.mul_apply, ← Module.End.mul_apply, ← e',
      sub_self]
  obtain ⟨a, rfl⟩ := h.fix_scalar hl hlp
  refine ⟨a, fun v hv => ?_⟩
  rw [← (h.mem_P hπ c v).1 hv, ← Module.End.mul_apply, e, Module.End.mul_apply,
    Module.algebraMap_end_apply]

/-- `B` has no nonzero `y` with `y ^ p = 0`. -/
theorem VsMSplitHyp.reduced (h : VsMSplitHyp A r ζ t) (hπ : VsMIdemProp A ζ t π) :
    ∀ y ∈ vsMAlgE A t, y ^ p = 0 → y = 0 := by
  intro y hy hyp
  have hc : ∀ c, y * π c = 0 := by
    intro c
    by_cases hP : vsMP ζ t c = ⊥
    · have : π c = 0 := by
        ext v
        have := h.π_mem_P hπ c v
        rw [hP, Submodule.mem_bot] at this
        exact this
      rw [this, mul_zero]
    obtain ⟨v0, hv0, hv00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    obtain ⟨l, hl, e⟩ := h.act hπ c hy
    have e' := h.act_pow hπ c hy hl e p
    rw [hyp, zero_mul] at e'
    have hl0 : l = 0 := by
      by_contra hne
      apply hv00
      refine vsM_pow_inj' (h.inj hl hne) p v0 ?_
      rw [← (h.mem_P hπ c v0).1 hv0, ← Module.End.mul_apply, ← e', LinearMap.zero_apply]
    rw [e, hl0, zero_mul]
  calc y = y * ∑ c, π c := by rw [hπ.2.1, mul_one]
    _ = 0 := by rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun c _ => hc c

/-! ### Shifts: all pieces have the same dimension -/

theorem VsMSplitHyp.shift (h : VsMSplitHyp A r ζ t) {i : Fin k} {s : 𝔼ˣ}
    (hsA : s ∈ Subgroup.centralizer (A : Set 𝔼ˣ))
    (hst : ∀ j, s * t j * s⁻¹ = if j = i then ζ * t j else t j) (c : Fin k → ZMod r)
    {v : V} (hv : v ∈ vsMP ζ t c) :
    ((s⁻¹ : 𝔼ˣ) : 𝔼) v ∈ vsMP ζ t (c + Pi.single i 1) := by
  have hζr : (ζ : 𝔼) ^ r = 1 := by rw [← Units.val_pow_eq_pow_val, h.hζr, Units.val_one]
  rw [mem_vsMP] at hv ⊢
  intro j
  have hcomm : ∀ l ∈ vsTAlg A, ((s⁻¹ : 𝔼ˣ) : 𝔼) * l = l * ((s⁻¹ : 𝔼ˣ) : 𝔼) := fun l hl =>
    vsM_comm_alg ((Subgroup.centralizer (A : Set 𝔼ˣ)).inv_mem hsA) hl
  have e1 : (t j : 𝔼) * ((s⁻¹ : 𝔼ˣ) : 𝔼) = ((s⁻¹ : 𝔼ˣ) : 𝔼) * ((s * t j * s⁻¹ : 𝔼ˣ) : 𝔼) := by
    rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
  by_cases hji : j = i
  · subst hji
    rw [Pi.add_apply, Pi.single_eq_same]
    have hL : (ζ : 𝔼) * (ζ : 𝔼) ^ (c j).val ∈ vsTAlg A := mul_mem h.hζ.1 (pow_mem h.hζ.1 _)
    calc (t j : 𝔼) (((s⁻¹ : 𝔼ˣ) : 𝔼) v) = (((s⁻¹ : 𝔼ˣ) : 𝔼) * ((ζ : 𝔼) * t j)) v := by
          rw [← Module.End.mul_apply, e1, hst j, if_pos rfl, Units.val_mul]
      _ = (((s⁻¹ : 𝔼ˣ) : 𝔼) * ((ζ : 𝔼) * (ζ : 𝔼) ^ (c j).val)) v := by
          simp only [Module.End.mul_apply]; rw [hv j]
      _ = (((ζ : 𝔼) * (ζ : 𝔼) ^ (c j).val) * ((s⁻¹ : 𝔼ˣ) : 𝔼)) v := by rw [hcomm _ hL]
      _ = ((ζ : 𝔼) ^ (c j + 1).val) (((s⁻¹ : 𝔼ˣ) : 𝔼) v) := by
          rw [vsM_zp_add hζr, vsM_zp_one hζr, pow_mul_comm']
          simp only [Module.End.mul_apply]
  · rw [Pi.add_apply, Pi.single_eq_of_ne hji, add_zero]
    calc (t j : 𝔼) (((s⁻¹ : 𝔼ˣ) : 𝔼) v) = (((s⁻¹ : 𝔼ˣ) : 𝔼) * (t j : 𝔼)) v := by
          rw [← Module.End.mul_apply, e1, hst j, if_neg hji]
      _ = (((s⁻¹ : 𝔼ˣ) : 𝔼) * (ζ : 𝔼) ^ (c j).val) v := by
          simp only [Module.End.mul_apply]; rw [hv j]
      _ = ((ζ : 𝔼) ^ (c j).val) (((s⁻¹ : 𝔼ˣ) : 𝔼) v) := by
          rw [hcomm _ (pow_mem h.hζ.1 _)]
          simp only [Module.End.mul_apply]

theorem VsMSplitHyp.finrank_le (h : VsMSplitHyp A r ζ t) (s : Fin k → 𝔼ˣ)
    (hsA : ∀ i, s i ∈ Subgroup.centralizer (A : Set 𝔼ˣ))
    (hst : ∀ i j, s i * t j * (s i)⁻¹ = if j = i then ζ * t j else t j)
    (c d : Fin k → ZMod r) :
    finrank (ZMod p) (vsMP ζ t c) ≤ finrank (ZMod p) (vsMP ζ t (c + d)) := by
  have hstep : ∀ (i : Fin k) (c : Fin k → ZMod r), finrank (ZMod p) (vsMP ζ t c) ≤
      finrank (ZMod p) (vsMP ζ t (c + Pi.single i 1)) := by
    intro i c
    have hle : (vsMP ζ t c).map (((s i)⁻¹ : 𝔼ˣ) : 𝔼) ≤ vsMP ζ t (c + Pi.single i 1) := by
      rintro _ ⟨v, hv, rfl⟩
      exact h.shift (hsA i) (hst i) c hv
    calc finrank (ZMod p) (vsMP ζ t c)
        = finrank (ZMod p) ((vsMP ζ t c).map (((s i)⁻¹ : 𝔼ˣ) : 𝔼)) :=
          (Submodule.equivMapOfInjective _ (vsT_unit_inj (s i)⁻¹) _).finrank_eq
      _ ≤ _ := Submodule.finrank_mono hle
  have hn : ∀ (i : Fin k) (n : ℕ) (c : Fin k → ZMod r), finrank (ZMod p) (vsMP ζ t c) ≤
      finrank (ZMod p) (vsMP ζ t (c + n • Pi.single i 1)) := by
    intro i n
    induction n with
    | zero => intro c; rw [zero_nsmul, add_zero]
    | succ n ih =>
      intro c
      rw [succ_nsmul, ← add_assoc]
      exact (ih c).trans (hstep i _)
  have hsum : ∀ (S : Finset (Fin k)) (c : Fin k → ZMod r), finrank (ZMod p) (vsMP ζ t c) ≤
      finrank (ZMod p) (vsMP ζ t (c + ∑ i ∈ S, Pi.single i (d i))) := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro c; rw [Finset.sum_empty, add_zero]
    | insert j S hj ih =>
      intro c
      rw [Finset.sum_insert hj, ← add_assoc]
      have hd : (Pi.single j (d j) : Fin k → ZMod r) =
          (d j).val • (Pi.single j 1 : Fin k → ZMod r) := by
        ext l
        by_cases hl : l = j
        · subst hl; simp
        · simp [Pi.single_eq_of_ne hl]
      refine le_trans ?_ (ih _)
      rw [hd]
      exact hn j _ c
  have := hsum Finset.univ c
  rwa [Finset.univ_sum_single d] at this

theorem VsMSplitHyp.finrank_eq (h : VsMSplitHyp A r ζ t) (s : Fin k → 𝔼ˣ)
    (hsA : ∀ i, s i ∈ Subgroup.centralizer (A : Set 𝔼ˣ))
    (hst : ∀ i j, s i * t j * (s i)⁻¹ = if j = i then ζ * t j else t j)
    (c c' : Fin k → ZMod r) :
    finrank (ZMod p) (vsMP ζ t c) = finrank (ZMod p) (vsMP ζ t c') := by
  have h1 := h.finrank_le s hsA hst c (c' - c)
  have h2 := h.finrank_le s hsA hst c' (c - c')
  rw [add_sub_cancel] at h1 h2
  exact le_antisymm h1 h2

theorem VsMSplitHyp.P_ne_bot (h : VsMSplitHyp A r ζ t) (hπ : VsMIdemProp A ζ t π)
    (s : Fin k → 𝔼ˣ) (hsA : ∀ i, s i ∈ Subgroup.centralizer (A : Set 𝔼ˣ))
    (hst : ∀ i j, s i * t j * (s i)⁻¹ = if j = i then ζ * t j else t j)
    (c : Fin k → ZMod r) : vsMP ζ t c ≠ ⊥ := by
  obtain ⟨c0, hc0⟩ := h.exists_P hπ
  intro h0
  apply hc0
  rw [← Submodule.finrank_eq_zero, h.finrank_eq s hsA hst c0 c, h0, finrank_bot]

/-! ### The pieces of a spanning family -/

theorem VsMSplitHyp.piece_eq (h : VsMSplitHyp A r ζ t) (hπ : VsMIdemProp A ζ t π)
    {ι : Type} (f : ι → 𝔼) (hfB : ∀ i, f i ∈ vsMAlgE A t) (hf : ∀ i, f i ^ p = f i)
    (hspan : ∀ s ∈ vsMAlgE A t, s ^ p = s → s ∈ Submodule.span (ZMod p) (Set.range f))
    {a : ι → ZMod p} (ha : vsFEig f a ≠ ⊥) : ∃ c : Fin k → ZMod r, vsFEig f a = vsMP ζ t c := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha
  have hidem : ∀ c, π c * π c = π c := fun c => by rw [hπ.2.2.1 c c, if_pos rfl]
  have hpow : ∀ c (n : ℕ), π c ^ (n + 1) = π c := by
    intro c n
    induction n with
    | zero => rw [zero_add, pow_one]
    | succ n ih => rw [pow_succ, ih, hidem]
  have hμ : ∀ c, ∃ μ : ZMod p, ∀ v ∈ vsFEig f a, π c v = μ • v := fun c =>
    vsFEig_scalar f a (hspan _ (hπ.1 c) (by
      obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero hp.out.ne_zero
      have := hpow c n
      rwa [← hn] at this))
  choose μ hμ using hμ
  have hsum : w = ∑ c, μ c • w := by
    have := congrArg (fun F : 𝔼 => F w) hπ.2.1
    simp only [LinearMap.sum_apply, Module.End.one_apply] at this
    calc w = ∑ c, π c w := this.symm
      _ = ∑ c, μ c • w := Finset.sum_congr rfl fun c _ => hμ c w hw
  obtain ⟨c, hc⟩ : ∃ c, μ c ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hw0
    rw [hsum]
    exact Finset.sum_eq_zero fun c _ => by rw [hall c, zero_smul]
  have hc1 : μ c = 1 := by
    have e1 : π c (π c w) = π c w := by rw [← Module.End.mul_apply, hidem]
    rw [hμ c w hw, map_smul, hμ c w hw, smul_smul] at e1
    have e2 : (μ c * μ c - μ c) • w = 0 := by rw [sub_smul, e1, sub_self]
    rcases smul_eq_zero.1 e2 with h0 | h0
    · have : μ c * (μ c - 1) = 0 := by rw [mul_sub, mul_one]; exact h0
      rcases mul_eq_zero.1 this with h1 | h1
      · exact absurd h1 hc
      · exact sub_eq_zero.1 h1
    · exact absurd h0 hw0
  have hWP : vsFEig f a ≤ vsMP ζ t c := by
    intro v hv
    rw [h.mem_P hπ, hμ c v hv, hc1, one_smul]
  -- `P c` lies in a joint eigenspace
  have hsc : ∀ i, ∃ b : ZMod p, ∀ v ∈ vsMP ζ t c, f i v = b • v := fun i =>
    h.fix_act hπ c (hfB i) (hf i)
  choose b hb using hsc
  have hPb : vsMP ζ t c ≤ vsFEig f b := by
    intro v hv
    rw [mem_vsFEig]
    exact fun i => hb i v hv
  have hab : a = b := by
    by_contra hne
    exact hw0 (vsFEig_disjoint f hne hw (hPb (hWP hw)))
  subst hab
  exact ⟨c, le_antisymm hWP hPb⟩

theorem VsMSplitHyp.pieces (h : VsMSplitHyp A r ζ t) (s : Fin k → 𝔼ˣ)
    (hsA : ∀ i, s i ∈ Subgroup.centralizer (A : Set 𝔼ˣ))
    (hst : ∀ i j, s i * t j * (s i)⁻¹ = if j = i then ζ * t j else t j)
    {ι : Type} (f : ι → 𝔼) (hfB : ∀ i, f i ∈ vsMAlgE A t) (hf : ∀ i, f i ^ p = f i)
    (hspan : ∀ s ∈ vsMAlgE A t, s ^ p = s → s ∈ Submodule.span (ZMod p) (Set.range f)) :
    {a | vsFEig f a ≠ ⊥}.ncard = r ^ k ∧
    (∀ a b, vsFEig f a ≠ ⊥ → vsFEig f b ≠ ⊥ →
      finrank (ZMod p) (vsFEig f a) = finrank (ZMod p) (vsFEig f b)) ∧
    ∀ K : Subgroup 𝔼ˣ, (∀ g ∈ K, (∀ i, ⁅g, t i⁆ ∈ vsMScal A) ∧ g * ζ * g⁻¹ ∈ vsMScal A) →
      (vsMStab (fun a : {a // vsFEig f a ≠ ⊥} => vsFEig f a.1)).relIndex K ≤ r ^ k * r := by
  classical
  obtain ⟨π, hπ⟩ := h.idem
  have hne := h.P_ne_bot hπ s hsA hst
  -- each `P c` is a joint eigenspace
  have hPeq : ∀ c : Fin k → ZMod r, ∃ a, vsFEig f a = vsMP ζ t c := by
    intro c
    have hsc : ∀ i, ∃ b : ZMod p, ∀ v ∈ vsMP ζ t c, f i v = b • v := fun i =>
      h.fix_act hπ c (hfB i) (hf i)
    choose b hb using hsc
    have hPb : vsMP ζ t c ≤ vsFEig f b := fun v hv => (mem_vsFEig f b v).2 fun i => hb i v hv
    have hb0 : vsFEig f b ≠ ⊥ := fun h0 => hne c (eq_bot_iff.2 (h0 ▸ hPb))
    obtain ⟨c', hc'⟩ := h.piece_eq hπ f hfB hf hspan hb0
    have hcc : c = c' := by
      by_contra hcc
      apply hne c
      rw [eq_bot_iff]
      intro v hv
      exact (Submodule.mem_bot _).2 (h.P_disj hπ hcc hv (hc' ▸ hPb hv))
    exact ⟨b, hcc ▸ hc'⟩
  choose a ha using hPeq
  have hPinj : ∀ c c' : Fin k → ZMod r, vsMP ζ t c = vsMP ζ t c' → c = c' := by
    intro c c' hcc
    by_contra hne'
    apply hne c
    rw [eq_bot_iff]
    intro v hv
    exact (Submodule.mem_bot _).2 (h.P_disj hπ hne' hv (hcc ▸ hv))
  have hEinj : ∀ a1 a2, vsFEig f a1 ≠ ⊥ → vsFEig f a1 = vsFEig f a2 → a1 = a2 := by
    intro a1 a2 h1 h12
    by_contra hne'
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h1
    exact hw0 (vsFEig_disjoint f hne' hw (h12 ▸ hw))
  refine ⟨?_, ?_, ?_⟩
  · have : {a | vsFEig f a ≠ ⊥}.ncard = (Set.univ : Set (Fin k → ZMod r)).ncard := by
      symm
      refine Set.ncard_congr (fun c _ => a c) ?_ ?_ ?_
      · intro c _
        show vsFEig f (a c) ≠ ⊥
        rw [ha c]; exact hne c
      · intro c c' _ _ hcc
        apply hPinj
        rw [← ha c, ← ha c']
        exact congrArg (vsFEig f) hcc
      · intro b hb
        obtain ⟨c, hc⟩ := h.piece_eq hπ f hfB hf hspan hb
        refine ⟨c, Set.mem_univ _, ?_⟩
        exact hEinj _ _ (by rw [ha c]; exact hne c) ((ha c).trans hc.symm)
    rw [this, Set.ncard_univ, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  · intro a1 a2 h1 h2
    obtain ⟨c1, hc1⟩ := h.piece_eq hπ f hfB hf hspan h1
    obtain ⟨c2, hc2⟩ := h.piece_eq hπ f hfB hf hspan h2
    rw [hc1, hc2]
    exact h.finrank_eq s hsA hst c1 c2
  · intro K hK
    haveI : Finite V := Module.finite_of_finite (ZMod p)
    -- the discrete logarithm
    have hdl : ∀ u : 𝔼ˣ, u ∈ vsMScal A → u ^ r = 1 → ∃ j < r, u = ζ ^ j := fun u hu hur =>
      vsM_dlog A r ζ u h.hA h.hdom h.hr h.hζ h.hζ1 h.hζr hu hur
    let dl : 𝔼ˣ → Fin r := fun u =>
      if hu : ∃ j < r, u = ζ ^ j then ⟨Classical.choose hu, (Classical.choose_spec hu).1⟩ else 0
    have hdl' : ∀ u : 𝔼ˣ, u ∈ vsMScal A → u ^ r = 1 → u = ζ ^ (dl u : ℕ) := by
      intro u hu hur
      have hex := hdl u hu hur
      simp only [dl, dif_pos hex]
      exact (Classical.choose_spec hex).2
    have hfix : ∀ g : 𝔼ˣ, (∀ i, g * t i = t i * g) → g * ζ = ζ * g →
        g ∈ vsMStab (fun a : {a // vsFEig f a ≠ ⊥} => vsFEig f a.1) := by
      intro g hgt hgζ ⟨b, hb⟩
      obtain ⟨c, hc⟩ := h.piece_eq hπ f hfB hf hspan hb
      show (vsFEig f b).map (g : 𝔼) = vsFEig f b
      rw [hc]
      have hle : (vsMP ζ t c).map (g : 𝔼) ≤ vsMP ζ t c := by
        rintro _ ⟨v, hv, rfl⟩
        rw [SetLike.mem_coe, mem_vsMP] at hv
        rw [mem_vsMP]
        intro i
        have e1 : (t i : 𝔼) * g = g * t i := by rw [← Units.val_mul, ← Units.val_mul, hgt]
        have e2 : ((ζ : 𝔼) ^ (c i).val) * g = g * (ζ : 𝔼) ^ (c i).val := by
          have hc : Commute (ζ ^ (c i).val) g := Commute.pow_left (show Commute ζ g from hgζ.symm) _
          rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul, hc.eq]
        calc (t i : 𝔼) ((g : 𝔼) v) = ((t i : 𝔼) * g) v := rfl
          _ = (g * (t i : 𝔼)) v := by rw [e1]
          _ = (g : 𝔼) (((ζ : 𝔼) ^ (c i).val) v) := by rw [Module.End.mul_apply, hv i]
          _ = (((ζ : 𝔼) ^ (c i).val) * g) v := by rw [e2]; rfl
          _ = ((ζ : 𝔼) ^ (c i).val) ((g : 𝔼) v) := rfl
      exact Submodule.eq_of_le_of_finrank_eq hle
        (Submodule.equivMapOfInjective _ (vsT_unit_inj g) _).finrank_eq.symm
    have hpowr : ∀ g ∈ K, ∀ i, ⁅g, t i⁆ ^ r = 1 := by
      intro g hg i
      have hν := (hK g hg).1 i
      have e1 : g * t i * g⁻¹ = ⁅g, t i⁆ * t i := by rw [commutatorElement_def]; group
      have hc : Commute ⁅g, t i⁆ (t i) := (vsM_comm_scal (h.htA i) hν).symm
      have e2 : (g * t i * g⁻¹) ^ r = 1 := by rw [conj_pow, h.htr i, mul_one, mul_inv_cancel]
      rw [e1, hc.mul_pow, h.htr i, mul_one] at e2
      exact e2
    have hpowζ : ∀ g ∈ K, (g * ζ * g⁻¹) ^ r = 1 := by
      intro g _
      rw [conj_pow, h.hζr, mul_one, mul_inv_cancel]
    let Φ : 𝔼ˣ → (Fin k → Fin r) × Fin r := fun g => (fun i => dl ⁅g, t i⁆, dl (g * ζ * g⁻¹))
    have hb := vsM_relIndex_le (vsMStab (fun a : {a // vsFEig f a ≠ ⊥} => vsFEig f a.1)) K Φ
      Set.univ Set.finite_univ (fun _ _ => Set.mem_univ _) (by
        intro g hg g' hg' hgg
        have h1 : ∀ i, ⁅g, t i⁆ = ⁅g', t i⁆ := by
          intro i
          have := congrArg (fun F => F i) (congrArg Prod.fst hgg)
          simp only [Φ] at this
          rw [hdl' _ ((hK g hg).1 i) (hpowr g hg i), hdl' _ ((hK g' hg').1 i) (hpowr g' hg' i), this]
        have h2 : g * ζ * g⁻¹ = g' * ζ * g'⁻¹ := by
          have := congrArg Prod.snd hgg
          simp only [Φ] at this
          rw [hdl' _ (hK g hg).2 (hpowζ g hg), hdl' _ (hK g' hg').2 (hpowζ g' hg'), this]
        apply hfix
        · intro i
          have := h1 i
          simp only [commutatorElement_def] at this
          calc g⁻¹ * g' * t i = g⁻¹ * (g' * t i * g'⁻¹ * (t i)⁻¹) * t i * g' := by group
            _ = g⁻¹ * (g * t i * g⁻¹ * (t i)⁻¹) * t i * g' := by rw [this]
            _ = t i * (g⁻¹ * g') := by group
        · calc g⁻¹ * g' * ζ = g⁻¹ * (g' * ζ * g'⁻¹) * g' := by group
            _ = g⁻¹ * (g * ζ * g⁻¹) * g' := by rw [h2]
            _ = ζ * (g⁻¹ * g') := by group)
    rw [Set.ncard_univ, Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_fin] at hb
    exact hb

end Hyp

end GI.Proved
