module

public import Workspace.Proved.VsMSplit

@[expose] public section

/-!
# The hard case, part A (pairing, shifts, the bound `|Ȳ| ≤ r^(2k+2)`)

Setting: `VsMHard H A Y r` and a greedy maximal good isotropic family `e_1, …, e_k`
(`VsMIso A Y r e`). We write `S = vsMScal A`.

* Basic facts: `Y` commutes with `S`, commutators of `Y` are `r`-th roots of unity in `S`,
  an element of `Y` central in `Y` lies in `S` (minimality and `Y` not abelian), and there is
  `ζ ∈ S` of order `r`.
* Shifts (`VsMHard.exists_shift`): for every `v : Fin k → ZMod r` there is `y ∈ Y` with
  `⁅y, e_j⁆ = ζ^(v_j)`. Otherwise a nonzero linear form vanishes on all these vectors and gives
  an element `e_i ∏_{j<i} e_j^(b_j)` central in `Y`, hence in `S`, against independence.
* `|Y : Y ∩ S| ≤ r^(2k+2)` and `k = 0 → r = 2`.
-/

namespace GI.Proved

open Module
open scoped commutatorElement

/-! ### Group lemmas -/

theorem vsM_pow_comm_aux {G : Type*} [Group G] {x y c : G} (hcy : Commute c y)
    (hyx : y * x = c * (x * y)) : ∀ n : ℕ, y ^ n * x = c ^ n * (x * y ^ n)
  | 0 => by simp
  | n + 1 => by
    have ih := vsM_pow_comm_aux hcy hyx n
    have hc : y ^ n * c = c * y ^ n := ((hcy.pow_right n).eq).symm
    calc y ^ (n + 1) * x = y ^ n * (y * x) := by rw [pow_succ, mul_assoc]
      _ = (y ^ n * c) * (x * y) := by rw [hyx, mul_assoc]
      _ = c * (y ^ n * x) * y := by rw [hc]; group
      _ = c * (c ^ n * (x * y ^ n)) * y := by rw [ih]
      _ = c ^ (n + 1) * (x * y ^ (n + 1)) := by group

/-- `(x y)^n = c^(n(n-1)/2) x^n y^n` when `y x = c x y` and `c` is central in `⟨x, y⟩`. -/
theorem vsM_mul_pow_comm {G : Type*} [Group G] {x y c : G} (hcx : Commute c x)
    (hcy : Commute c y) (hyx : y * x = c * (x * y)) :
    ∀ n : ℕ, (x * y) ^ n = c ^ (∑ i ∈ Finset.range n, i) * (x ^ n * y ^ n)
  | 0 => by simp
  | n + 1 => by
    have ih := vsM_mul_pow_comm hcx hcy hyx n
    have h1 := vsM_pow_comm_aux hcy hyx n
    have hc : x ^ n * c ^ n = c ^ n * x ^ n := ((hcx.pow_pow n n).eq).symm
    rw [Finset.sum_range_succ, pow_succ, ih]
    calc c ^ (∑ i ∈ Finset.range n, i) * (x ^ n * y ^ n) * (x * y)
        = c ^ (∑ i ∈ Finset.range n, i) * x ^ n * (y ^ n * x) * y := by group
      _ = c ^ (∑ i ∈ Finset.range n, i) * (x ^ n * c ^ n) * x * y ^ n * y := by rw [h1]; group
      _ = c ^ (∑ i ∈ Finset.range n, i + n) * (x ^ (n + 1) * y ^ (n + 1)) := by rw [hc]; group

theorem vsM_mul_pow_odd {G : Type*} [Group G] {x y c : G} (hcx : Commute c x)
    (hcy : Commute c y) (hyx : y * x = c * (x * y)) {r : ℕ} (hr : Odd r) (hc : c ^ r = 1) :
    (x * y) ^ r = x ^ r * y ^ r := by
  rw [vsM_mul_pow_comm hcx hcy hyx, Finset.sum_range_id]
  obtain ⟨m, rfl⟩ := hr
  have : (2 * m + 1) * (2 * m + 1 - 1) / 2 = (2 * m + 1) * m := by
    rw [Nat.add_sub_cancel, mul_left_comm, Nat.mul_div_cancel_left _ two_pos]
  rw [this, pow_mul, hc, one_pow, one_mul]

theorem vsM_mul_sq {G : Type*} [Group G] {x y c : G} (hcx : Commute c x)
    (hcy : Commute c y) (hyx : y * x = c * (x * y)) : (x * y) ^ 2 = c * (x ^ 2 * y ^ 2) := by
  rw [vsM_mul_pow_comm hcx hcy hyx]
  simp [Finset.sum_range_succ]

/-- `y x = ⁅y, x⁆ x y`. -/
theorem vsM_swap {G : Type*} [Group G] (x y : G) : y * x = ⁅y, x⁆ * (x * y) := by
  rw [commutatorElement_def]; group

/-- If `K` commutes with `S`, the elements of `K ⊔ S` are the products `a s`. -/
theorem vsM_mem_sup_comm {G : Type*} [Group G] {K S : Subgroup G}
    (h : ∀ a ∈ K, ∀ s ∈ S, a * s = s * a) {x : G} (hx : x ∈ K ⊔ S) :
    ∃ a ∈ K, ∃ s ∈ S, x = a * s := by
  let T : Subgroup G :=
    { carrier := {x | ∃ a ∈ K, ∃ s ∈ S, x = a * s}
      mul_mem' := by
        rintro _ _ ⟨a, ha, s, hs, rfl⟩ ⟨a', ha', s', hs', rfl⟩
        refine ⟨a * a', K.mul_mem ha ha', s * s', S.mul_mem hs hs', ?_⟩
        calc a * s * (a' * s') = a * (a' * s) * s' := by rw [h a' ha' s hs]; group
          _ = a * a' * (s * s') := by group
      one_mem' := ⟨1, K.one_mem, 1, S.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, s, hs, rfl⟩
        refine ⟨a⁻¹, K.inv_mem ha, s⁻¹, S.inv_mem hs, ?_⟩
        rw [mul_inv_rev, h a⁻¹ (K.inv_mem ha) s⁻¹ (S.inv_mem hs)] }
  have hle : K ⊔ S ≤ T := sup_le (fun a ha => ⟨a, ha, 1, S.one_mem, by simp⟩)
    (fun s hs => ⟨1, K.one_mem, s, hs, by simp⟩)
  exact hle hx

/-- If `P` is covered by `n` left cosets `g_i W`, then `|P : P ∩ W| ≤ n`. -/
theorem vsM_relIndex_cosets {G : Type*} [Group G] (W P : Subgroup G) (g : ℕ → G) (n : ℕ)
    (h : ∀ y ∈ P, ∃ i, i < n ∧ (g i)⁻¹ * y ∈ W) : W.relIndex P ≤ n := by
  classical
  let f : G → ℕ := fun y => if hy : ∃ i, i < n ∧ (g i)⁻¹ * y ∈ W then Nat.find hy else n
  have hb := vsM_relIndex_le W P f (Set.Iio n) (Set.finite_Iio n) ?_ ?_
  · rwa [Set.ncard_eq_toFinset_card', Set.toFinset_Iio, Nat.card_Iio] at hb
  · intro y hy
    have hex := h y hy
    simp only [f, dif_pos hex, Set.mem_Iio]
    exact (Nat.find_spec hex).1
  · intro y hy y' hy' hf
    have hex := h y hy
    have hex' := h y' hy'
    simp only [f, dif_pos hex, dif_pos hex'] at hf
    have h1 := (Nat.find_spec hex).2
    have h2 := (Nat.find_spec hex').2
    rw [hf] at h1
    have := W.mul_mem (W.inv_mem h1) h2
    rwa [mul_inv_rev, inv_inv, mul_assoc, ← mul_assoc (g _), mul_inv_cancel, one_mul] at this

/-! ### Discrete logarithms with values in `ZMod r` -/

/-- An exponent `a : ZMod r` with `c = ζ ^ a.val`, if there is one. -/
noncomputable def vsMDl {G : Type*} [Monoid G] (r : ℕ) (ζ c : G) : ZMod r := by
  classical exact if h : ∃ a : ZMod r, c = ζ ^ a.val then h.choose else 0

theorem vsMDl_spec {G : Type*} [Monoid G] {r : ℕ} {ζ c : G}
    (h : ∃ a : ZMod r, c = ζ ^ a.val) : c = ζ ^ (vsMDl r ζ c).val := by
  unfold vsMDl
  rw [dif_pos h]
  exact h.choose_spec

theorem vsM_zp_inj {G : Type*} [Group G] {r : ℕ} [NeZero r] {ζ : G} (hord : orderOf ζ = r)
    {a b : ZMod r} (h : ζ ^ a.val = ζ ^ b.val) : a = b := by
  rw [pow_inj_mod, hord, Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at h
  exact ZMod.val_injective r h

/-! ### The hard case: basic facts -/

variable {p : ℕ} [hp : Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

local notation "𝔼" => End (ZMod p) V

variable {H A Y : Subgroup (End (ZMod p) V)ˣ} {r : ℕ}

theorem VsMHard.solv (h : VsMHard H A Y r) : IsSolvable H := h.1
theorem VsMHard.abn (h : VsMHard H A Y r) : VsTAbNormal H A := h.2.1
theorem VsMHard.hA (h : VsMHard H A Y r) : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := h.2.1.2.2
theorem VsMHard.dom (h : VsMHard H A Y r) : vsTDom (vsTAlg A) := h.2.2.1
theorem VsMHard.prime (h : VsMHard H A Y r) : r.Prime := h.2.2.2.1
theorem VsMHard.norm (h : VsMHard H A Y r) : VsMNorm H Y := h.2.2.2.2.1
theorem VsMHard.cent (h : VsMHard H A Y r) : Y ≤ Subgroup.centralizer (A : Set 𝔼ˣ) :=
  h.2.2.2.2.2.1
theorem VsMHard.comm (h : VsMHard H A Y r) : ∀ x ∈ Y, ∀ y ∈ Y, ⁅x, y⁆ ∈ vsMScal A :=
  h.2.2.2.2.2.2.1
theorem VsMHard.pow (h : VsMHard H A Y r) : ∀ y ∈ Y, y ^ r ∈ vsMScal A := h.2.2.2.2.2.2.2.1
theorem VsMHard.min (h : VsMHard H A Y r) : VsMMin H (vsMScal A) Y := h.2.2.2.2.2.2.2.2.1
theorem VsMHard.nab (h : VsMHard H A Y r) : ∃ x ∈ Y, ∃ y ∈ Y, x * y ≠ y * x :=
  h.2.2.2.2.2.2.2.2.2

theorem VsMHard.scal_comm (h : VsMHard H A Y r) {y s : 𝔼ˣ} (hy : y ∈ Y)
    (hs : s ∈ vsMScal A) : y * s = s * y :=
  vsM_comm_scal (h.cent hy) hs

/-- Elements of `S` commute with elements of `Y` (as `Commute`). -/
theorem VsMHard.commute (h : VsMHard H A Y r) {y s : 𝔼ˣ} (hy : y ∈ Y)
    (hs : s ∈ vsMScal A) : Commute s y :=
  (h.scal_comm hy hs).symm

theorem VsMHard.comm_pow (h : VsMHard H A Y r) {x y : 𝔼ˣ} (hx : x ∈ Y) (hy : y ∈ Y) :
    ⁅x, y⁆ ^ r = 1 := by
  have hc := h.comm x hx y hy
  rw [← vsM_comm_pow_left (h.commute hx hc) (h.commute hy hc) r,
    commutatorElement_eq_one_iff_mul_comm]
  exact (h.scal_comm hy (h.pow x hx)).symm

/-- An element of `Y` central in `Y` lies in `S`. -/
theorem VsMHard.central (h : VsMHard H A Y r) {x : 𝔼ˣ} (hx : x ∈ Y)
    (hxc : ∀ y ∈ Y, x * y = y * x) : x ∈ vsMScal A := by
  by_contra hxS
  have hle := h.min x hx hxS
  have hC : vsMSpin H x ⊔ vsMScal A ≤ Subgroup.centralizer (Y : Set 𝔼ˣ) := by
    refine sup_le ((Subgroup.closure_le _).2 ?_) ?_
    · rintro _ ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ Y := h.norm g⁻¹ (H.inv_mem hg) y hy
      rw [inv_inv] at hy'
      have e1 := hxc _ hy'
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [← e1]
        _ = g * x * g⁻¹ * y := by group
    · intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact h.scal_comm hy hs
  obtain ⟨a, ha, b, hb, hab⟩ := h.nab
  exact hab (Subgroup.mem_centralizer_iff.1 (hC (hle hb)) a ha)

theorem VsMHard.exists_zeta (h : VsMHard H A Y r) :
    ∃ ζ ∈ vsMScal A, ζ ≠ 1 ∧ ζ ^ r = 1 := by
  obtain ⟨a, ha, b, hb, hab⟩ := h.nab
  exact ⟨⁅a, b⁆, h.comm a ha b hb, fun h1 => hab (commutatorElement_eq_one_iff_mul_comm.1 h1),
    h.comm_pow ha hb⟩

theorem vsM_comm_pow_right {G : Type*} [Group G] {x y : G} (h1 : Commute ⁅y, x⁆ y)
    (h2 : Commute ⁅y, x⁆ x) (n : ℕ) : ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  conv_lhs => rw [← commutatorElement_inv]
  rw [vsM_comm_pow_left h1 h2 n, ← inv_pow, commutatorElement_inv]

theorem vsM_scal_pow_card {A : Subgroup 𝔼ˣ} {c : 𝔼ˣ} (hc : c ∈ vsMScal A) :
    c ^ Nat.card (vsMScal A) = 1 := by
  have h1 := congrArg Subtype.val (pow_card_eq_one' (x := (⟨c, hc⟩ : vsMScal A)))
  rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1

/-! ### The hard case with a root of unity `ζ` of order `r` -/

section Zeta

variable [FiniteDimensional (ZMod p) V] [Nontrivial V] {ζ : (End (ZMod p) V)ˣ} {k : ℕ}
  {e : Fin k → (End (ZMod p) V)ˣ}

theorem VsMHard.ord (h : VsMHard H A Y r) (hζ1 : ζ ≠ 1) (hζr : ζ ^ r = 1) : orderOf ζ = r := by
  haveI : Fact r.Prime := ⟨h.prime⟩
  exact orderOf_eq_prime hζr hζ1

theorem VsMHard.card_dvd (h : VsMHard H A Y r) (hζ : ζ ∈ vsMScal A) (hζ1 : ζ ≠ 1)
    (hζr : ζ ^ r = 1) : r ∣ Nat.card (vsMScal A) := by
  have := orderOf_dvd_natCard (⟨ζ, hζ⟩ : vsMScal A)
  rwa [Subgroup.orderOf_mk, h.ord hζ1 hζr] at this

theorem VsMHard.dl (h : VsMHard H A Y r) (hζ : ζ ∈ vsMScal A) (hζ1 : ζ ≠ 1) (hζr : ζ ^ r = 1)
    {c : 𝔼ˣ} (hc : c ∈ vsMScal A) (hcr : c ^ r = 1) : c = ζ ^ (vsMDl r ζ c).val := by
  apply vsMDl_spec
  obtain ⟨j, hj, rfl⟩ := vsM_dlog A r ζ c h.hA h.dom h.prime hζ hζ1 hζr hc hcr
  haveI : NeZero r := ⟨h.prime.ne_zero⟩
  exact ⟨(j : ZMod r), by rw [ZMod.val_cast_of_lt hj]⟩

theorem VsMHard.dl_comm (h : VsMHard H A Y r) (hζ : ζ ∈ vsMScal A) (hζ1 : ζ ≠ 1)
    (hζr : ζ ^ r = 1) {x y : 𝔼ˣ} (hx : x ∈ Y) (hy : y ∈ Y) :
    ⁅x, y⁆ = ζ ^ (vsMDl r ζ ⁅x, y⁆).val :=
  h.dl hζ hζ1 hζr (h.comm x hx y hy) (h.comm_pow hx hy)

omit [FiniteDimensional (ZMod p) V] [Nontrivial V] in
/-- Products `∏_{j ∈ T} e_j^(b_j)` pair with `y` by `ζ^(∑ b_j d_j)`. -/
theorem VsMHard.exists_prod (h : VsMHard H A Y r) (he : ∀ i, e i ∈ Y) (hζr : ζ ^ r = 1)
    (T : Finset (Fin k)) (b : Fin k → ZMod r) :
    ∃ w ∈ Subgroup.closure (e '' (T : Set (Fin k))), ∀ y ∈ Y, ∀ d : Fin k → ZMod r,
      (∀ j, ⁅y, e j⁆ = ζ ^ (d j).val) → ⁅y, w⁆ = ζ ^ (∑ j ∈ T, b j * d j).val := by
  classical
  haveI : NeZero r := ⟨h.prime.ne_zero⟩
  have hcl : ∀ T : Set (Fin k), Subgroup.closure (e '' T) ≤ Y := fun T =>
    (Subgroup.closure_le Y).2 (by rintro _ ⟨i, _, rfl⟩; exact he i)
  have key : ∀ T : Finset (Fin k), ∃ w ∈ Subgroup.closure (e '' (T : Set (Fin k))),
      ∀ y ∈ Y, ∀ d : Fin k → ZMod r,
        (∀ j, ⁅y, e j⁆ = ζ ^ (d j).val) → ⁅y, w⁆ = ζ ^ (∑ j ∈ T, b j * d j).val := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨1, Subgroup.one_mem _, fun y _ d _ => by simp⟩
    | insert j T hj ih =>
      obtain ⟨w, hw, hw'⟩ := ih
      refine ⟨e j ^ (b j).val * w, Subgroup.mul_mem _ (Subgroup.pow_mem _
        (Subgroup.subset_closure (Set.mem_image_of_mem e
          (by simp : j ∈ ((insert j T : Finset (Fin k)) : Set (Fin k))))) _) (Subgroup.closure_mono
        (Set.image_mono (Finset.coe_subset.2 (Finset.subset_insert _ _))) hw), ?_⟩
      intro y hy d hd
      have hwY : w ∈ Y := hcl _ hw
      have hc := h.comm (e j) (he j) y hy
      rw [vsM_comm_mul_right (h.commute (Y.pow_mem (he j) _) (h.comm y hy w hwY)),
        vsM_comm_pow_right (h.commute (he j) hc) (h.commute hy hc), hd j, hw' y hy d hd,
        ← vsM_zp_mul hζr, ← vsM_zp_add hζr, Finset.sum_insert hj]
  exact key T

/-- **Shifts.** Every vector of exponents is realized by the pairing with some `y ∈ Y`. -/
theorem VsMHard.exists_shift (h : VsMHard H A Y r) (he : VsMIso A Y r e)
    (hζ : ζ ∈ vsMScal A) (hζ1 : ζ ≠ 1) (hζr : ζ ^ r = 1) (v : Fin k → ZMod r) :
    ∃ y ∈ Y, ∀ j, ⁅y, e j⁆ = ζ ^ (v j).val := by
  classical
  haveI : Fact r.Prime := ⟨h.prime⟩
  haveI : NeZero r := ⟨h.prime.ne_zero⟩
  letI : AddCommGroup (ZMod r) := (ZMod.commRing r).toAddCommGroup
  let M : Submodule (ZMod r) (Fin k → ZMod r) :=
    { carrier := {v | ∃ y ∈ Y, ∀ j, ⁅y, e j⁆ = ζ ^ (v j).val}
      add_mem' := by
        rintro a b ⟨y, hy, hya⟩ ⟨y', hy', hyb⟩
        refine ⟨y * y', Y.mul_mem hy hy', fun j => ?_⟩
        have hc := h.comm y' hy' (e j) (he.1 j)
        rw [vsM_comm_mul_left (h.commute hy hc) (h.commute (he.1 j) hc), hya j, hyb j,
          Pi.add_apply, vsM_zp_add hζr]
      zero_mem' := ⟨1, Y.one_mem, fun j => by simp⟩
      smul_mem' := by
        rintro c a ⟨y, hy, hya⟩
        refine ⟨y ^ c.val, Y.pow_mem hy _, fun j => ?_⟩
        have hc := h.comm y hy (e j) (he.1 j)
        rw [vsM_comm_pow_left (h.commute hy hc) (h.commute (he.1 j) hc), hya j, Pi.smul_apply,
          smul_eq_mul, vsM_zp_mul hζr] }
  have hM : M = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hf⟩ := M.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hne)
    let a : Fin k → ZMod r := fun i => f (fun j => if i = j then 1 else 0)
    have hfa : ∀ x, f x = ∑ i, x i * a i := fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ f x]; rfl
    have ha0 : ∃ i, a i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hf0 (LinearMap.ext fun x => by
        rw [hfa, LinearMap.zero_apply]
        exact Finset.sum_eq_zero fun i _ => by rw [hall i, mul_zero])
    obtain ⟨i, hi, himax⟩ := (Finset.univ.filter fun j => a j ≠ 0).exists_max_image id
      (by obtain ⟨j, hj⟩ := ha0; exact ⟨j, by simp [hj]⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, id] at hi himax
    let b : Fin k → ZMod r := fun j => a j * (a i)⁻¹
    obtain ⟨w, hw, hw'⟩ := h.exists_prod he.1 hζr (Finset.univ.filter (· < i)) b
    have hset : ((Finset.univ.filter (· < i) : Finset (Fin k)) : Set (Fin k)) = {j | j < i} := by
      ext j; simp
    rw [hset] at hw
    have hwY : w ∈ Y := (Subgroup.closure_le Y).2 (by rintro _ ⟨l, _, rfl⟩; exact he.1 l) hw
    have hz : ∀ y ∈ Y, e i * w * y = y * (e i * w) := by
      intro y hy
      let d : Fin k → ZMod r := fun j => vsMDl r ζ ⁅y, e j⁆
      have hd : ∀ j, ⁅y, e j⁆ = ζ ^ (d j).val := fun j => h.dl_comm hζ hζ1 hζr hy (he.1 j)
      have hfd : ∑ j, d j * a j = 0 := by rw [← hfa]; exact hf ⟨y, hy, hd⟩
      have h1 : ∑ j, b j * d j = 0 := by
        have : ∑ j, b j * d j = (a i)⁻¹ * ∑ j, d j * a j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by simp only [b]; ring
        rw [this, hfd, mul_zero]
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· < i)] at h1
      have h2 : ∑ j ∈ Finset.univ.filter (fun j => ¬ j < i), b j * d j = d i := by
        rw [Finset.sum_eq_single i]
        · simp only [b]; rw [mul_inv_cancel₀ hi, one_mul]
        · intro j hj hji
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hj
          have : a j = 0 := by
            by_contra hne
            exact hji (le_antisymm (himax j hne) hj)
          simp only [b, this, zero_mul]
        · intro hi'; simp at hi'
      rw [h2] at h1
      have hc : ⁅y, e i * w⁆ = 1 := by
        rw [vsM_comm_mul_right (h.commute (he.1 i) (h.comm y hy w hwY)), hd i, hw' y hy d hd,
          ← vsM_zp_add hζr, add_comm, h1, ZMod.val_zero, pow_zero]
      exact (commutatorElement_eq_one_iff_mul_comm.1 hc).symm
    have hzS := h.central (Y.mul_mem (he.1 i) hwY) hz
    apply he.2.2.2.1 i
    have : e i = (e i * w) * w⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hzS)
      (Subgroup.mem_sup_left (Subgroup.inv_mem _ hw))
  have : v ∈ M := hM ▸ Submodule.mem_top
  exact this

/-- The shifts `s_i ∈ Y` with `⁅s_i, e_j⁆ = ζ^(δ_ij)`. -/
theorem VsMHard.shifts (h : VsMHard H A Y r) (he : VsMIso A Y r e)
    (hζ : ζ ∈ vsMScal A) (hζ1 : ζ ≠ 1) (hζr : ζ ^ r = 1) :
    ∃ s : Fin k → 𝔼ˣ, (∀ i, s i ∈ Y) ∧ ∀ i j, ⁅s i, e j⁆ = if j = i then ζ else 1 := by
  classical
  haveI : NeZero r := ⟨h.prime.ne_zero⟩
  have hs : ∀ i, ∃ s ∈ Y, ∀ j, ⁅s, e j⁆ = if j = i then ζ else 1 := by
    intro i
    obtain ⟨s, hs, hs'⟩ := h.exists_shift he hζ hζ1 hζr (Pi.single i 1)
    refine ⟨s, hs, fun j => ?_⟩
    rw [hs' j]
    by_cases hji : j = i
    · subst hji; rw [Pi.single_eq_same, if_pos rfl, vsM_zp_one hζr]
    · rw [Pi.single_eq_of_ne hji, if_neg hji, ZMod.val_zero, pow_zero]
  choose s hsY hs' using hs
  exact ⟨s, hsY, hs'⟩

/-- An element commuting with the elements of `Y` that commute with `E`, and with the shifts,
commutes with all of `Y`. -/
theorem VsMHard.comm_of_shifts (h : VsMHard H A Y r) (he : VsMIso A Y r e)
    (hζ : ζ ∈ vsMScal A) (hζ1 : ζ ≠ 1) (hζr : ζ ^ r = 1) (s : Fin k → 𝔼ˣ)
    (hsY : ∀ i, s i ∈ Y) (hs : ∀ i j, ⁅s i, e j⁆ = if j = i then ζ else 1) {x : 𝔼ˣ}
    (hxp : ∀ y ∈ Y, (∀ j, y * e j = e j * y) → x * y = y * x)
    (hxs : ∀ i, x * s i = s i * x) : ∀ y ∈ Y, x * y = y * x := by
  classical
  haveI : NeZero r := ⟨h.prime.ne_zero⟩
  let C := Subgroup.centralizer ({x} : Set 𝔼ˣ)
  have key : ∀ T : Finset (Fin k), ∀ y ∈ Y, (∀ j ∉ T, ⁅y, e j⁆ = 1) → y ∈ C := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro y hy hy1
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hxp y hy fun j =>
        commutatorElement_eq_one_iff_mul_comm.1 (hy1 j (Finset.notMem_empty j))).symm
    | insert j T hj ih =>
      intro y hy hy1
      obtain ⟨D, hD⟩ : ∃ D : ZMod r, ⁅y, e j⁆ = ζ ^ D.val :=
        ⟨_, h.dl_comm hζ hζ1 hζr hy (he.1 j)⟩
      have hy' : y * s j ^ (-D).val ∈ C := by
        refine ih _ (Y.mul_mem hy (Y.pow_mem (hsY j) _)) fun l hl => ?_
        have hc := h.comm (s j ^ (-D).val) (Y.pow_mem (hsY j) _) (e l) (he.1 l)
        have hc' := h.comm (s j) (hsY j) (e l) (he.1 l)
        rw [vsM_comm_mul_left (h.commute hy hc) (h.commute (he.1 l) hc),
          vsM_comm_pow_left (h.commute (hsY j) hc') (h.commute (he.1 l) hc'), hs j l]
        by_cases hlj : l = j
        · subst hlj
          rw [if_pos rfl, hD, ← vsM_zp_add hζr, add_neg_cancel, ZMod.val_zero, pow_zero]
        · rw [if_neg hlj, one_pow, mul_one]
          exact hy1 l (fun hm => (Finset.mem_insert.1 hm).elim hlj hl)
      have hsn : s j ^ (-D).val ∈ C :=
        C.pow_mem (Subgroup.mem_centralizer_singleton_iff.2 (hxs j).symm) _
      have : y = y * s j ^ (-D).val * (s j ^ (-D).val)⁻¹ := by group
      rw [this]
      exact C.mul_mem hy' (C.inv_mem hsn)
  intro y hy
  have := key Finset.univ y hy (fun j hj => absurd (Finset.mem_univ j) hj)
  exact (Subgroup.mem_centralizer_singleton_iff.1 this).symm

/-! ### The bound `|Y : Y ∩ S| ≤ r^(2k+2)` -/

theorem vsM_chi_mul {A : Subgroup 𝔼ˣ} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {a b : 𝔼ˣ}
    (ha : a ∈ vsMScal A) (hb : b ∈ vsMScal A) (m : ℕ) : (a * b) ^ m = a ^ m * b ^ m :=
  Commute.mul_pow (vsM_scal_comm hA ha hb) m

theorem vsM_chi_r {A : Subgroup 𝔼ˣ} (hdvd : r ∣ Nat.card (vsMScal A)) {c : 𝔼ˣ}
    (hc : c ∈ vsMScal A) : (c ^ (Nat.card (vsMScal A) / r)) ^ r = 1 := by
  rw [← pow_mul, Nat.div_mul_cancel hdvd, vsM_scal_pow_card hc]

theorem VsMHard.good_iff (h : VsMHard H A Y r) (hdvd : r ∣ Nat.card (vsMScal A)) {y : 𝔼ˣ}
    (hy : y ∈ Y) : vsMGood A r y ↔ (y ^ r) ^ (Nat.card (vsMScal A) / r) = 1 :=
  (vsM_good_test A h.hA h.dom).2 r (y ^ r) h.prime hdvd (h.pow y hy)

/-- A good element of `Y_⊥ = Y ∩ C(E)` lies in `W = Y_⊥ ∩ (E ⊔ S)` (maximality of `E`). -/
theorem VsMHard.good_mem (he : VsMIso A Y r e) {y : 𝔼ˣ}
    (hy : y ∈ Y ⊓ Subgroup.centralizer (Set.range e)) (hg : vsMGood A r y) :
    y ∈ (Y ⊓ Subgroup.centralizer (Set.range e)) ⊓
      (Subgroup.closure (Set.range e) ⊔ vsMScal A) :=
  ⟨hy, he.2.2.2.2 y hy.1 hg fun i => ((Subgroup.mem_centralizer_iff.1 hy.2) (e i) ⟨i, rfl⟩).symm⟩

/-- `|Y : Y_⊥| ≤ r^k`. -/
theorem VsMHard.index_perp (h : VsMHard H A Y r) (he : VsMIso A Y r e)
    (hζ : ζ ∈ vsMScal A) (hζ1 : ζ ≠ 1) (hζr : ζ ^ r = 1) :
    (Y ⊓ Subgroup.centralizer (Set.range e)).relIndex Y ≤ r ^ k := by
  classical
  haveI : NeZero r := ⟨h.prime.ne_zero⟩
  have hb := vsM_relIndex_le (Y ⊓ Subgroup.centralizer (Set.range e)) Y
    (fun y => fun j => vsMDl r ζ ⁅y, e j⁆) Set.univ Set.finite_univ
    (fun _ _ => Set.mem_univ _) ?_
  · rwa [Set.ncard_univ, Nat.card_fun, Nat.card_zmod, Nat.card_fin] at hb
  · intro y hy y' hy' hf
    refine ⟨Y.mul_mem (Y.inv_mem hy) hy', Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨j, rfl⟩
    have hj : vsMDl r ζ ⁅y, e j⁆ = vsMDl r ζ ⁅y', e j⁆ := congrFun hf j
    have heq : ⁅y, e j⁆ = ⁅y', e j⁆ := by
      calc ⁅y, e j⁆ = ζ ^ (vsMDl r ζ ⁅y, e j⁆).val := h.dl_comm hζ hζ1 hζr hy (he.1 j)
        _ = ζ ^ (vsMDl r ζ ⁅y', e j⁆).val := by rw [hj]
        _ = ⁅y', e j⁆ := (h.dl_comm hζ hζ1 hζr hy' (he.1 j)).symm
    simp only [commutatorElement_def] at heq
    calc e j * (y⁻¹ * y') = y⁻¹ * (y * e j * y⁻¹ * (e j)⁻¹) * e j * y' := by group
      _ = y⁻¹ * (y' * e j * y'⁻¹ * (e j)⁻¹) * e j * y' := by rw [heq]
      _ = y⁻¹ * y' * e j := by group

/-- `|W : W ∩ S| ≤ r^k`, by the pairing with the shifts. -/
theorem VsMHard.index_W (h : VsMHard H A Y r) (he : VsMIso A Y r e)
    (hζ : ζ ∈ vsMScal A) (hζ1 : ζ ≠ 1) (hζr : ζ ^ r = 1) :
    (vsMScal A ⊓ Y).relIndex ((Y ⊓ Subgroup.centralizer (Set.range e)) ⊓
      (Subgroup.closure (Set.range e) ⊔ vsMScal A)) ≤ r ^ k := by
  classical
  haveI : NeZero r := ⟨h.prime.ne_zero⟩
  obtain ⟨s, hsY, hs⟩ := h.shifts he hζ hζ1 hζr
  have hb := vsM_relIndex_le (vsMScal A ⊓ Y) ((Y ⊓ Subgroup.centralizer (Set.range e)) ⊓
    (Subgroup.closure (Set.range e) ⊔ vsMScal A)) (fun w => fun i => vsMDl r ζ ⁅s i, w⁆)
    Set.univ Set.finite_univ (fun _ _ => Set.mem_univ _) ?_
  · rwa [Set.ncard_univ, Nat.card_fun, Nat.card_zmod, Nat.card_fin] at hb
  · rintro w ⟨⟨hwY, -⟩, hwE⟩ w' ⟨⟨hwY', -⟩, hwE'⟩ hf
    have hxY : w⁻¹ * w' ∈ Y := Y.mul_mem (Y.inv_mem hwY) hwY'
    have hxE : w⁻¹ * w' ∈ Subgroup.closure (Set.range e) ⊔ vsMScal A :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hwE) hwE'
    have hxs : ∀ i, w⁻¹ * w' * s i = s i * (w⁻¹ * w') := by
      intro i
      have hi : vsMDl r ζ ⁅s i, w⁆ = vsMDl r ζ ⁅s i, w'⁆ := congrFun hf i
      have heq : ⁅s i, w⁆ = ⁅s i, w'⁆ := by
        calc ⁅s i, w⁆ = ζ ^ (vsMDl r ζ ⁅s i, w⁆).val := h.dl_comm hζ hζ1 hζr (hsY i) hwY
          _ = ζ ^ (vsMDl r ζ ⁅s i, w'⁆).val := by rw [hi]
          _ = ⁅s i, w'⁆ := (h.dl_comm hζ hζ1 hζr (hsY i) hwY').symm
      simp only [commutatorElement_def] at heq
      calc w⁻¹ * w' * s i = w⁻¹ * ((s i)⁻¹ * (s i * w' * (s i)⁻¹ * w'⁻¹))⁻¹ * w' := by group
        _ = w⁻¹ * ((s i)⁻¹ * (s i * w * (s i)⁻¹ * w⁻¹))⁻¹ * w' := by rw [heq]
        _ = s i * (w⁻¹ * w') := by group
    have hxp : ∀ y ∈ Y, (∀ j, y * e j = e j * y) → w⁻¹ * w' * y = y * (w⁻¹ * w') := by
      intro y hy hye
      have hle : Subgroup.closure (Set.range e) ⊔ vsMScal A ≤
          Subgroup.centralizer ({y} : Set 𝔼ˣ) := by
        refine sup_le ((Subgroup.closure_le _).2 ?_) ?_
        · rintro _ ⟨j, rfl⟩
          exact Subgroup.mem_centralizer_singleton_iff.2 (hye j).symm
        · intro c hc
          exact Subgroup.mem_centralizer_singleton_iff.2 (h.scal_comm hy hc).symm
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hxE)
    exact ⟨h.central hxY (h.comm_of_shifts he hζ hζ1 hζr s hsY hs hxp hxs), hxY⟩

/-- `|Y_⊥ : W| ≤ r^2`: for `r` odd, `y ↦ χ(y^r)` is a homomorphism whose kernel consists of
good elements; for `r = 2`, three independent non-good elements give a good product. -/
theorem VsMHard.index_mid (h : VsMHard H A Y r) (he : VsMIso A Y r e)
    (hζ : ζ ∈ vsMScal A) (hζ1 : ζ ≠ 1) (hζr : ζ ^ r = 1) :
    ((Y ⊓ Subgroup.centralizer (Set.range e)) ⊓
      (Subgroup.closure (Set.range e) ⊔ vsMScal A)).relIndex
      (Y ⊓ Subgroup.centralizer (Set.range e)) ≤ r ^ 2 := by
  classical
  set Yp := Y ⊓ Subgroup.centralizer (Set.range e) with hYp
  set W := Yp ⊓ (Subgroup.closure (Set.range e) ⊔ vsMScal A) with hW
  have hdvd := h.card_dvd hζ hζ1 hζr
  set m := Nat.card (vsMScal A) / r with hm
  have hgood : ∀ y ∈ Yp, (y ^ r) ^ m = 1 → y ∈ W := fun y hy h1 =>
    VsMHard.good_mem he hy ((h.good_iff hdvd hy.1).2 h1)
  rcases h.prime.eq_two_or_odd' with hr2 | hodd
  · subst hr2
    have hζ2 : ζ * ζ = 1 := by rw [← pow_two]; exact hζr
    have hsqW : ∀ z ∈ Yp, z ^ 2 ∈ W := fun z hz =>
      ⟨Yp.pow_mem hz 2, Subgroup.mem_sup_right (h.pow z hz.1)⟩
    have hflip : ∀ z ∈ Yp, ∀ a, z * a ∈ W → z⁻¹ * a ∈ W := by
      intro z hz a ha
      have : z⁻¹ * a = (z ^ 2)⁻¹ * (z * a) := by group
      rw [this]
      exact W.mul_mem (W.inv_mem (hsqW z hz)) ha
    have hq : ∀ a ∈ Y, ∀ b ∈ Y,
        ((a * b) ^ 2) ^ m = ⁅b, a⁆ ^ m * ((a ^ 2) ^ m * (b ^ 2) ^ m) := by
      intro a ha b hb
      have hc := h.comm b hb a ha
      rw [vsM_mul_sq (h.commute ha hc) (h.commute hb hc) (vsM_swap a b),
        vsM_chi_mul h.hA hc (mul_mem (h.pow a ha) (h.pow b hb)),
        vsM_chi_mul h.hA (h.pow a ha) (h.pow b hb)]
    have hbad : ∀ z ∈ Yp, z ∉ W → (z ^ 2) ^ m = ζ := by
      intro z hz hzW
      have hS : (z ^ 2) ^ m ∈ vsMScal A := pow_mem (h.pow z hz.1) m
      obtain ⟨j, hj, hjeq⟩ := vsM_dlog A 2 ζ _ h.hA h.dom h.prime hζ hζ1 hζr hS
        (vsM_chi_r hdvd (h.pow z hz.1))
      interval_cases j
      · exact absurd (hgood z hz (by rw [hjeq, pow_zero])) hzW
      · rw [hjeq, pow_one]
    have hcore : ∀ u ∈ Yp, ∀ v ∈ Yp, ∀ y ∈ Yp, u ∉ W → v ∉ W → y ∉ W → u * v ∉ W →
        u * y ∉ W → v * y ∉ W → u * v * y ∈ W := by
      intro u hu v hv y hy huW hvW hyW huv huy hvy
      have hu' := hbad u hu huW
      have hv' := hbad v hv hvW
      have hy' := hbad y hy hyW
      have hcu : ⁅y, u⁆ ^ m = ζ := by
        have := hq u hu.1 y hy.1
        rw [hbad _ (Yp.mul_mem hu hy) huy, hu', hy', hζ2, mul_one] at this
        exact this.symm
      have hcv : ⁅y, v⁆ ^ m = ζ := by
        have := hq v hv.1 y hy.1
        rw [hbad _ (Yp.mul_mem hv hy) hvy, hv', hy', hζ2, mul_one] at this
        exact this.symm
      apply hgood _ (Yp.mul_mem (Yp.mul_mem hu hv) hy)
      rw [hq (u * v) (Y.mul_mem hu.1 hv.1) y hy.1, hbad _ (Yp.mul_mem hu hv) huv, hy', hζ2,
        mul_one, vsM_comm_mul_right (h.commute hu.1 (h.comm y hy.1 v hv.1)),
        vsM_chi_mul h.hA (h.comm y hy.1 u hu.1) (h.comm y hy.1 v hv.1), hcu, hcv, hζ2]
    by_cases h0 : ∀ y ∈ Yp, y ∈ W
    · refine (vsM_relIndex_cosets W Yp (fun _ => 1) 1 fun y hy => ⟨0, one_pos, ?_⟩).trans
        (by norm_num)
      rw [inv_one, one_mul]
      exact h0 y hy
    push Not at h0
    obtain ⟨u, hu, huW⟩ := h0
    by_cases h1 : ∀ y ∈ Yp, y ∈ W ∨ u⁻¹ * y ∈ W
    · refine (vsM_relIndex_cosets W Yp (fun i => if i = 0 then 1 else u) 2
        fun y hy => ?_).trans (by norm_num)
      rcases h1 y hy with h1 | h1
      · exact ⟨0, by norm_num, by simpa using h1⟩
      · exact ⟨1, by norm_num, by simpa using h1⟩
    push Not at h1
    obtain ⟨v, hv, hvW, huvW⟩ := h1
    refine vsM_relIndex_cosets W Yp
      (fun i => if i = 0 then 1 else if i = 1 then u else if i = 2 then v else u * v) 4
      fun y hy => ?_
    by_contra hall
    push Not at hall
    have hy0 : y ∉ W := by simpa using hall 0 (by norm_num)
    have hy1 : u⁻¹ * y ∉ W := by simpa using hall 1 (by norm_num)
    have hy2 : v⁻¹ * y ∉ W := by simpa using hall 2 (by norm_num)
    have hy3 : (u * v)⁻¹ * y ∉ W := by simpa using hall 3 (by norm_num)
    have huv : u * v ∉ W := fun hw => huvW (hflip u hu v hw)
    have huy : u * y ∉ W := fun hw => hy1 (hflip u hu y hw)
    have hvy : v * y ∉ W := fun hw => hy2 (hflip v hv y hw)
    exact hy3 (hflip (u * v) (Yp.mul_mem hu hv) y (hcore u hu v hv y hy huW hvW hy0 huv huy hvy))
  · refine (vsM_relIndex_le W Yp (fun y => (y ^ r) ^ m) ((fun j : ℕ => ζ ^ j) '' Set.Iio r)
      ((Set.finite_Iio r).image _) ?_ ?_).trans ?_
    · intro y hy
      obtain ⟨j, hj, hjeq⟩ := vsM_dlog A r ζ _ h.hA h.dom h.prime hζ hζ1 hζr
        (pow_mem (h.pow y hy.1) m) (vsM_chi_r hdvd (h.pow y hy.1))
      exact ⟨j, hj, hjeq.symm⟩
    · intro y hy y' hy' hf
      have hf' : (y ^ r) ^ m = (y' ^ r) ^ m := hf
      apply hgood _ (Yp.mul_mem (Yp.inv_mem hy) hy')
      have hc := h.comm y' hy'.1 y⁻¹ (Y.inv_mem hy.1)
      have hS1 : y⁻¹ ^ r ∈ vsMScal A := by rw [inv_pow]; exact inv_mem (h.pow y hy.1)
      rw [vsM_mul_pow_odd (h.commute (Y.inv_mem hy.1) hc) (h.commute hy'.1 hc) (vsM_swap y⁻¹ y')
        hodd (h.comm_pow hy'.1 (Y.inv_mem hy.1)), vsM_chi_mul h.hA hS1 (h.pow y' hy'.1),
        inv_pow, inv_pow, hf', inv_mul_cancel]
    · calc ((fun j : ℕ => ζ ^ j) '' Set.Iio r).ncard ≤ (Set.Iio r).ncard :=
          Set.ncard_image_le (Set.finite_Iio r)
        _ = r := by rw [Set.ncard_eq_toFinset_card', Set.toFinset_Iio, Nat.card_Iio]
        _ ≤ r ^ 2 := Nat.le_self_pow two_ne_zero r

/-- **`|Ȳ| ≤ r^(2k+2)`.** -/
theorem VsMHard.index_le (h : VsMHard H A Y r) (he : VsMIso A Y r e) :
    (vsMScal A).relIndex Y ≤ r ^ (2 * k + 2) := by
  obtain ⟨ζ, hζ, hζ1, hζr⟩ := h.exists_zeta
  have h1 : vsMScal A ⊓ Y ≤ (Y ⊓ Subgroup.centralizer (Set.range e)) ⊓
      (Subgroup.closure (Set.range e) ⊔ vsMScal A) := fun x hx =>
    ⟨⟨hx.2, Subgroup.mem_centralizer_iff.2 (by rintro _ ⟨i, rfl⟩; exact h.scal_comm (he.1 i) hx.1)⟩,
      Subgroup.mem_sup_right hx.1⟩
  have h2 : (Y ⊓ Subgroup.centralizer (Set.range e)) ⊓
      (Subgroup.closure (Set.range e) ⊔ vsMScal A) ≤ Y ⊓ Subgroup.centralizer (Set.range e) :=
    inf_le_left
  have h3 : Y ⊓ Subgroup.centralizer (Set.range e) ≤ Y := inf_le_left
  have e1 := Subgroup.relIndex_mul_relIndex _ _ _ (h1.trans h2) h3
  have e2 := Subgroup.relIndex_mul_relIndex _ _ _ h1 h2
  rw [← Subgroup.inf_relIndex_right, ← e1, ← e2]
  calc _ ≤ r ^ k * r ^ 2 * r ^ k := Nat.mul_le_mul (Nat.mul_le_mul
        (h.index_W he hζ hζ1 hζr) (h.index_mid he hζ hζ1 hζr)) (h.index_perp he hζ hζ1 hζr)
    _ = r ^ (2 * k + 2) := by ring

/-- **`k = 0` only for `r = 2`.** For `r` odd, `y ↦ χ(y^r)` is multiplicative and, when
`E = 0`, its kernel lies in `S`; this makes two non-commuting elements commute. -/
theorem VsMHard.r_two (h : VsMHard H A Y r) (he : VsMIso A Y r e) (hk : k = 0) : r = 2 := by
  obtain ⟨ζ, hζ, hζ1, hζr⟩ := h.exists_zeta
  rcases h.prime.eq_two_or_odd' with h2 | hodd
  · exact h2
  exfalso
  subst hk
  have hdvd := h.card_dvd hζ hζ1 hζr
  have hgoodS : ∀ y ∈ Y, vsMGood A r y → y ∈ vsMScal A := fun y hy hg => by
    have := he.2.2.2.2 y hy hg (fun i => i.elim0)
    rwa [Set.range_eq_empty, Subgroup.closure_empty, bot_sup_eq] at this
  obtain ⟨x, hx, y, hy, hxy⟩ := h.nab
  have hxS : x ∉ vsMScal A := fun hxS => hxy (h.scal_comm hy hxS).symm
  have hαS : (x ^ r) ^ (Nat.card (vsMScal A) / r) ∈ vsMScal A := pow_mem (h.pow x hx) _
  have hα1 : (x ^ r) ^ (Nat.card (vsMScal A) / r) ≠ 1 := fun h1 =>
    hxS (hgoodS x hx ((h.good_iff hdvd hx).2 h1))
  obtain ⟨j, -, hβ⟩ := vsM_dlog A r _ _ h.hA h.dom h.prime hαS hα1 (vsM_chi_r hdvd (h.pow x hx))
    (pow_mem (h.pow y hy) _) (vsM_chi_r hdvd (h.pow y hy))
  have hxn : x ^ ((r - 1) * j) ∈ Y := Y.pow_mem hx _
  have hz : vsMGood A r (x ^ ((r - 1) * j) * y) := by
    rw [h.good_iff hdvd (Y.mul_mem hxn hy)]
    have hc := h.comm y hy _ hxn
    rw [vsM_mul_pow_odd (h.commute hxn hc) (h.commute hy hc) (vsM_swap _ y) hodd
      (h.comm_pow hy hxn), vsM_chi_mul h.hA (h.pow _ hxn) (h.pow y hy), hβ]
    have e1 : ((x ^ ((r - 1) * j)) ^ r) ^ (Nat.card (vsMScal A) / r) =
        ((x ^ r) ^ (Nat.card (vsMScal A) / r)) ^ ((r - 1) * j) := by
      rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul]; ring_nf
    have e2 : (r - 1) * j + j = r * j := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel h.prime.one_lt.le]
    rw [e1, ← pow_add, e2, pow_mul, vsM_chi_r hdvd (h.pow x hx), one_pow]
  have hzS := hgoodS _ (Y.mul_mem hxn hy) hz
  apply hxy
  have e1 : x * (x ^ ((r - 1) * j) * y) = (x ^ ((r - 1) * j) * y) * x := h.scal_comm hx hzS
  calc x * y = (x ^ ((r - 1) * j))⁻¹ * (x * (x ^ ((r - 1) * j) * y)) := by group
    _ = (x ^ ((r - 1) * j))⁻¹ * ((x ^ ((r - 1) * j) * y) * x) := by rw [e1]
    _ = y * x := by group

end Zeta

end GI.Proved
