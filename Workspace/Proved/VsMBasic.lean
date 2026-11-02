import Workspace.Proved.VsMStatements

/-!
# Basic facts on the scalars `S` and on commutators

* `vsM_relIndex_le`: a counting bound for indices. If `f` maps `H` into a finite set `T` and
  `f h = f h'` forces `h⁻¹ h' ∈ K`, then `|H : H ∩ K| ≤ |T|`.
* Elements of `C(A)` commute with all of `L = 𝔽_p[A]` (`vsM_comm_alg`).
* `S` (`vsMScal A`): membership (`vsM_mem_scal_iff`), normalized by `H` (`vsM_scal_norm`),
  cyclic of order `|L| - 1` (`vsM_scal_cyclic`, `vsM_card_scal`), the `r`-th power test.
* Commutator identities for groups whose commutators commute with the elements involved.
* `M4`: `A` grows (`vsM_grow`), the pairing facts (`vsM_pair`), discrete logarithm (`vsM_dlog`).
-/

namespace GI.Proved

open Module Polynomial
open scoped commutatorElement IsMulCommutative

/-! ### Group lemmas -/

/-- **Counting bound for an index.** -/
theorem vsM_relIndex_le {G X : Type*} [Group G] (K H : Subgroup G) (f : G → X) (T : Set X)
    (hT : T.Finite) (hmap : ∀ h ∈ H, f h ∈ T)
    (hfib : ∀ h ∈ H, ∀ h' ∈ H, f h = f h' → h⁻¹ * h' ∈ K) : K.relIndex H ≤ T.ncard := by
  classical
  haveI := hT.to_subtype
  unfold Subgroup.relIndex Subgroup.index
  let g : H ⧸ K.subgroupOf H → T := fun q => ⟨f ((q.out : H) : G), hmap _ q.out.2⟩
  have hg : Function.Injective g := by
    intro q q' hqq
    have h1 : f ((q.out : H) : G) = f ((q'.out : H) : G) := congrArg Subtype.val hqq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using hfib _ q.out.2 _ q'.out.2 h1
  calc Nat.card (H ⧸ K.subgroupOf H) ≤ Nat.card T := Nat.card_le_card_of_injective g hg
    _ = T.ncard := Nat.card_coe_set_eq T

theorem vsM_comm_mul_left {G : Type*} [Group G] {x y z : G} (h1 : Commute ⁅y, z⁆ x)
    (h2 : Commute ⁅y, z⁆ z) : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  set c := ⁅y, z⁆ with hcdef
  have hc : y * z * y⁻¹ = c * z := by rw [hcdef, commutatorElement_def]; group
  have hw : Commute c (x * z * x⁻¹ * z⁻¹) :=
    ((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right
  calc ⁅x * y, z⁆ = x * (y * z * y⁻¹) * x⁻¹ * z⁻¹ := by rw [commutatorElement_def]; group
    _ = x * (c * z) * x⁻¹ * z⁻¹ := by rw [hc]
    _ = c * (x * z * x⁻¹ * z⁻¹) := by
        rw [← mul_assoc x c z, ← h1.eq]; simp only [mul_assoc]
    _ = ⁅x, z⁆ * c := by rw [commutatorElement_def]; exact hw.eq

theorem vsM_comm_mul_right {G : Type*} [Group G] {x y z : G} (h1 : Commute ⁅x, z⁆ y) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  calc ⁅x, y * z⁆ = x * y * x⁻¹ * (⁅x, z⁆ * y⁻¹) := by simp only [commutatorElement_def]; group
    _ = x * y * x⁻¹ * (y⁻¹ * ⁅x, z⁆) := by rw [h1.inv_right.eq]
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by simp only [commutatorElement_def]; group

theorem vsM_comm_pow_left {G : Type*} [Group G] {x y : G} (h1 : Commute ⁅x, y⁆ x)
    (h2 : Commute ⁅x, y⁆ y) : ∀ n : ℕ, ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, vsM_comm_mul_left (x := x ^ n) (h1.pow_right n) h2, vsM_comm_pow_left h1 h2 n, pow_succ]

/-- In a subgroup `P` whose commutators lie in `S` and `S` commutes with `P`, `(xy)^n` is
`x^n y^n` up to an element of `S`. -/
theorem vsM_pow_mul {G : Type*} [Group G] (P S : Subgroup G)
    (hS : ∀ s ∈ S, ∀ x ∈ P, s * x = x * s) (hc : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ S) {x y : G}
    (hx : x ∈ P) (hy : y ∈ P) : ∀ n : ℕ, ∃ d ∈ S, (x * y) ^ n = x ^ n * y ^ n * d
  | 0 => ⟨1, S.one_mem, by simp⟩
  | n + 1 => by
    obtain ⟨d, hd, h⟩ := vsM_pow_mul P S hS hc hx hy n
    have he := hc x⁻¹ (P.inv_mem hx) (y ^ n) (P.pow_mem hy n)
    refine ⟨⁅x⁻¹, y ^ n⁆ * d, S.mul_mem he hd, ?_⟩
    set e := ⁅x⁻¹, y ^ n⁆ with hedef
    have h1 : y ^ n * x = x * e * y ^ n := by rw [hedef, commutatorElement_def]; group
    have hyy : y ^ n * y ∈ P := P.mul_mem (P.pow_mem hy n) hy
    rw [pow_succ, h, pow_succ, pow_succ]
    calc x ^ n * y ^ n * d * (x * y) = x ^ n * (y ^ n * (d * x)) * y := by
          simp only [mul_assoc]
      _ = x ^ n * (y ^ n * x) * (d * y) := by rw [hS d hd x hx]; simp only [mul_assoc]
      _ = x ^ n * (x * e * y ^ n) * (y * d) := by rw [h1, hS d hd y hy]
      _ = x ^ n * x * (e * (y ^ n * y)) * d := by simp only [mul_assoc]
      _ = x ^ n * x * ((y ^ n * y) * e) * d := by rw [hS e he _ hyy]
      _ = x ^ n * x * (y ^ n * y) * (e * d) := by simp only [mul_assoc]

/-! ### The algebra `L` and the scalars `S` -/

variable {p : ℕ} [hp : Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

local notation "𝔼" => End (ZMod p) V

theorem vsM_comm_alg {A : Subgroup 𝔼ˣ} {x : 𝔼ˣ} (hx : x ∈ Subgroup.centralizer (A : Set 𝔼ˣ))
    {l : 𝔼} (hl : l ∈ vsTAlg A) : (x : 𝔼) * l = l * x := by
  induction hl using Algebra.adjoin_induction with
  | mem l hl =>
    obtain ⟨a, ha, rfl⟩ := hl
    have := Subgroup.mem_centralizer_iff.1 hx a ha
    rw [← Units.val_mul, ← Units.val_mul, this]
  | algebraMap r => exact (Algebra.commutes r _).symm
  | add a b _ _ ha hb => rw [mul_add, add_mul, ha, hb]
  | mul a b _ _ ha hb => rw [← mul_assoc, ha, mul_assoc, hb, mul_assoc]

theorem vsM_comm_scal {A : Subgroup 𝔼ˣ} {x s : 𝔼ˣ} (hx : x ∈ Subgroup.centralizer (A : Set 𝔼ˣ))
    (hs : s ∈ vsMScal A) : x * s = s * x :=
  Units.ext (by rw [Units.val_mul, Units.val_mul]; exact vsM_comm_alg hx hs.1)

theorem vsM_scal_le_centralizer {A : Subgroup 𝔼ˣ} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    vsMScal A ≤ Subgroup.centralizer (A : Set 𝔼ˣ) := by
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  exact (vsTAlg_comm hA _ (Algebra.subset_adjoin ⟨a, ha, rfl⟩) _ hs.1).eq

theorem vsM_scal_comm {A : Subgroup 𝔼ˣ} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {s t : 𝔼ˣ}
    (hs : s ∈ vsMScal A) (ht : t ∈ vsMScal A) : s * t = t * s :=
  vsM_comm_scal (vsM_scal_le_centralizer hA hs) ht

theorem vsM_inv_mem [FiniteDimensional (ZMod p) V] {A : Subgroup 𝔼ˣ} {u : 𝔼ˣ}
    (hu : (u : 𝔼) ∈ vsTAlg A) : ((u⁻¹ : 𝔼ˣ) : 𝔼) ∈ vsTAlg A := by
  set L := vsTAlg A
  let f : L →ₗ[ZMod p] L := LinearMap.mulLeft (ZMod p) (⟨u, hu⟩ : L)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h := congrArg (fun z : L => ((u⁻¹ : 𝔼ˣ) : 𝔼) * (z : 𝔼)) hab
    simpa [f, ← mul_assoc] using h
  obtain ⟨b, hb⟩ := (LinearMap.injective_iff_surjective.1 hf) 1
  have h1 : (u : 𝔼) * b = 1 := congrArg Subtype.val hb
  have h2 : ((u⁻¹ : 𝔼ˣ) : 𝔼) = b := by
    calc ((u⁻¹ : 𝔼ˣ) : 𝔼) = ((u⁻¹ : 𝔼ˣ) : 𝔼) * ((u : 𝔼) * b) := by rw [h1, mul_one]
      _ = b := by rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [h2]
  exact b.2

theorem vsM_mem_scal_iff [FiniteDimensional (ZMod p) V] (A : Subgroup 𝔼ˣ) (u : 𝔼ˣ) :
    u ∈ vsMScal A ↔ (u : 𝔼) ∈ vsTAlg A :=
  ⟨fun h => h.1, fun h => ⟨h, vsM_inv_mem h⟩⟩

theorem vsM_scal_norm {H A : Subgroup 𝔼ˣ} (hA : VsTAbNormal H A) : VsMNorm H (vsMScal A) := by
  intro h hh s hs
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact vsT_conj_mem hA hh hs.1
  · rw [show (h * s * h⁻¹)⁻¹ = h * s⁻¹ * h⁻¹ by group, Units.val_mul, Units.val_mul]
    exact vsT_conj_mem hA hh hs.2

theorem vsM_norm_inf_centralizer {H N M : Subgroup 𝔼ˣ} (hN : VsMNorm H N) (hM : VsMNorm H M) :
    VsMNorm H (N ⊓ Subgroup.centralizer (M : Set 𝔼ˣ)) := by
  rintro h hh x ⟨hxN, hxC⟩
  refine ⟨hN h hh x hxN, ?_⟩
  have hxC' : x ∈ Subgroup.centralizer (M : Set 𝔼ˣ) := hxC
  show h * x * h⁻¹ ∈ Subgroup.centralizer (M : Set 𝔼ˣ)
  rw [Subgroup.mem_centralizer_iff] at hxC' ⊢
  intro m hm
  have h1 := hxC' _ (hM h⁻¹ (H.inv_mem hh) m hm)
  calc m * (h * x * h⁻¹) = h * ((h⁻¹ * m * h⁻¹⁻¹) * x) * h⁻¹ := by group
    _ = h * (x * (h⁻¹ * m * h⁻¹⁻¹)) * h⁻¹ := by rw [h1]
    _ = h * x * h⁻¹ * m := by group

theorem vsM_norm [FiniteDimensional (ZMod p) V] [Nontrivial V] : VsMNormStmt p V :=
  ⟨fun _ _ hA => vsM_scal_norm hA, fun _ _ _ hN hM => vsM_norm_inf_centralizer hN hM⟩

theorem vsM_scal_iff [FiniteDimensional (ZMod p) V] [Nontrivial V] : VsMScalIffStmt p V :=
  vsM_mem_scal_iff

/-! ### `L` is a field: `S` is cyclic of order `|L| - 1` -/

/-- A finite group with an injective hom into `L` (a domain) is cyclic. -/
theorem vsM_cyclic_of_hom [FiniteDimensional (ZMod p) V] [Nontrivial V] {A : Subgroup 𝔼ˣ}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hdom : vsTDom (vsTAlg A)) {G : Type*} [Group G]
    [Finite G] (f : G →* vsTAlg A) (hf : Function.Injective f) : IsCyclic G := by
  classical
  haveI : IsMulCommutative (vsTAlg A) :=
    Algebra.isMulCommutative_adjoin (ZMod p) (vsTSet_comm hA)
  haveI : Nontrivial (vsTAlg A) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h1 : ((0 : (vsTAlg A)) : 𝔼) = ((1 : (vsTAlg A)) : 𝔼) := congrArg Subtype.val h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    have h2 := congrArg (fun f : 𝔼 => f v) h1
    simpa using h2.symm
  haveI : NoZeroDivisors (vsTAlg A) := by
    refine ⟨fun {x y} hxy => ?_⟩
    rcases hdom x.1 x.2 with hx | hx
    · exact Or.inl (Subtype.ext hx)
    · right
      apply Subtype.ext
      ext v
      have h1 := congrArg (fun z : (vsTAlg A) => (z : 𝔼) v) hxy
      exact hx _ (by simpa using h1)
  haveI : IsDomain (vsTAlg A) := NoZeroDivisors.to_isDomain (vsTAlg A)
  exact isCyclic_of_injective_ringHom (R := vsTAlg A)
    { toFun := f, map_one' := f.map_one, map_mul' := f.map_mul } hf

/-- The hom `S → L`. -/
def vsMScalHom (A : Subgroup 𝔼ˣ) : vsMScal A →* vsTAlg A where
  toFun s := ⟨((s : 𝔼ˣ) : 𝔼), s.2.1⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem vsMScalHom_inj (A : Subgroup 𝔼ˣ) : Function.Injective (vsMScalHom A) := by
  intro a b h
  exact Subtype.ext (Units.ext (congrArg Subtype.val h))

theorem vsM_scal_cyclic [FiniteDimensional (ZMod p) V] [Nontrivial V] {A : Subgroup 𝔼ˣ}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hdom : vsTDom (vsTAlg A)) : IsCyclic (vsMScal A) := by
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  exact vsM_cyclic_of_hom hA hdom _ (vsMScalHom_inj A)

/-- A nonzero element of `L` is a unit lying in `S`. -/
theorem vsM_exists_scal [FiniteDimensional (ZMod p) V] {A : Subgroup 𝔼ˣ}
    (hdom : vsTDom (vsTAlg A)) {l : 𝔼} (hl : l ∈ vsTAlg A) (hl0 : l ≠ 0) :
    ∃ u ∈ vsMScal A, (u : 𝔼) = l := by
  rcases hdom l hl with h | h
  · exact absurd h hl0
  have hinj : Function.Injective l := by
    intro a b hab
    have := h (a - b) (by rw [map_sub, hab, sub_self])
    exact sub_eq_zero.1 this
  have hu : IsUnit l := (Module.End.isUnit_iff l).2
    ⟨hinj, LinearMap.injective_iff_surjective.1 hinj⟩
  refine ⟨hu.unit, (vsM_mem_scal_iff A _).2 (by simpa using hl), by simp⟩

theorem vsM_card_scal [FiniteDimensional (ZMod p) V] [Nontrivial V] {A : Subgroup 𝔼ˣ}
    (hdom : vsTDom (vsTAlg A)) : Nat.card (vsMScal A) + 1 = Nat.card (vsTAlg A) := by
  classical
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  haveI : Finite (vsTAlg A) := Finite.of_injective (fun x : vsTAlg A => (x : 𝔼)) Subtype.val_injective
  have himg : Set.range (vsMScalHom A) = Set.univ \ {0} := by
    ext l
    simp only [Set.mem_range, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    constructor
    · rintro ⟨s, rfl⟩ h0
      have h1 : ((s : 𝔼ˣ) : 𝔼) = 0 := congrArg Subtype.val h0
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      apply hv
      have := congrArg (fun f : 𝔼 => ((s⁻¹ : 𝔼ˣ) : 𝔼) (f v)) h1
      simpa [← Module.End.mul_apply] using this
    · intro h0
      have hl0 : (l : 𝔼) ≠ 0 := fun h => h0 (Subtype.ext h)
      obtain ⟨u, hu, hul⟩ := vsM_exists_scal hdom l.2 hl0
      exact ⟨⟨u, hu⟩, Subtype.ext hul⟩
  have h1 := Set.ncard_diff_singleton_add_one (Set.mem_univ (0 : vsTAlg A)) Set.finite_univ
  rw [← himg, Set.ncard_univ, Set.ncard_range_of_injective (vsMScalHom_inj A)] at h1
  exact h1

/-- In a finite cyclic group of order `n` with `r ∣ n`, `x` is an `r`-th power iff
`x ^ (n / r) = 1`. -/
theorem vsM_cyclic_pow_iff {G : Type*} [Group G] [Finite G] [IsCyclic G] {r : ℕ}
    (hr : r ∣ Nat.card G) (hr0 : 0 < r) (x : G) : (∃ y, x = y ^ r) ↔ x ^ (Nat.card G / r) = 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [← pow_mul, Nat.mul_div_cancel' hr, pow_card_eq_one']
  · intro hx
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    have hord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
    obtain ⟨m, rfl⟩ := (mem_powers_iff_mem_zpowers).2 (hg x)
    rw [← pow_mul] at hx
    have hd := orderOf_dvd_of_pow_eq_one hx
    rw [hord] at hd
    obtain ⟨t, ht⟩ := hr
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · rw [h, mul_zero] at ht; exact absurd ht (Nat.card_pos.ne')
      · exact h
    rw [ht, Nat.mul_div_cancel_left _ hr0] at hd
    have hrm : r ∣ m := Nat.dvd_of_mul_dvd_mul_right htpos hd
    obtain ⟨u, rfl⟩ := hrm
    exact ⟨g ^ u, by rw [← pow_mul, mul_comm]⟩

theorem vsM_good_test [FiniteDimensional (ZMod p) V] [Nontrivial V] : VsMGoodTestStmt p V := by
  intro A hA hdom
  haveI : Finite V := Module.finite_of_finite (ZMod p)
  refine ⟨vsM_card_scal hdom, fun r c hr hrS hc => ?_⟩
  haveI := vsM_scal_cyclic hA hdom
  have h := vsM_cyclic_pow_iff hrS hr.pos (⟨c, hc⟩ : vsMScal A)
  constructor
  · rintro ⟨l, hl, rfl⟩
    have := h.1 ⟨⟨l, hl⟩, rfl⟩
    exact congrArg Subtype.val this
  · intro hc1
    obtain ⟨⟨l, hl⟩, hl'⟩ := h.2 (Subtype.ext hc1)
    exact ⟨l, hl, congrArg Subtype.val hl'⟩

/-! ### Discrete logarithm -/

theorem vsM_dlog [FiniteDimensional (ZMod p) V] [Nontrivial V] : VsMDlogStmt p V := by
  intro A r ζ c hA hdom hr hζ hζ1 hζr hc hcr
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have hq : (X ^ r - C 1 : (ZMod p)[X]) ≠ 0 := X_pow_sub_C_ne_zero hr.pos 1
  have hcard := vsT_card_roots (vsTSet_comm hA) hdom hq
  rw [natDegree_X_pow_sub_C] at hcard
  set T := {x : 𝔼 | x ∈ Algebra.adjoin (ZMod p) (vsTSet A) ∧ aeval x (X ^ r - C 1 : (ZMod p)[X]) = 0}
  have hroot : ∀ u : 𝔼ˣ, u ∈ vsMScal A → u ^ r = 1 → (u : 𝔼) ∈ T := by
    intro u hu hur
    refine ⟨hu.1, ?_⟩
    rw [map_sub, map_pow, aeval_X, aeval_C, map_one, ← Units.val_pow_eq_pow_val, hur, Units.val_one,
      sub_self]
  set I := (fun j : ℕ => ((ζ ^ j : 𝔼ˣ) : 𝔼)) '' Set.Iio r
  have hord : orderOf ζ = r := orderOf_eq_prime hζr hζ1
  have hinj : Set.InjOn (fun j : ℕ => ((ζ ^ j : 𝔼ˣ) : 𝔼)) (Set.Iio r) := by
    intro i hi j hj hij
    have := pow_injOn_Iio_orderOf (x := ζ) (by rw [hord]; exact hi) (by rw [hord]; exact hj)
    exact this (Units.ext hij)
  have hIT : I ⊆ T := by
    rintro _ ⟨j, -, rfl⟩
    refine hroot _ ((vsMScal A).pow_mem hζ j) ?_
    rw [← pow_mul, mul_comm, pow_mul, hζr, one_pow]
  have hIcard : I.ncard = r := by
    rw [hinj.ncard_image, Set.ncard_eq_toFinset_card', Set.toFinset_Iio,
      Nat.card_Iio]
  have hTfin : T.Finite := by
    haveI : Finite V := Module.finite_of_finite (ZMod p)
    exact Set.toFinite T
  have hIeq : I = T := Set.eq_of_subset_of_ncard_le hIT (hcard.trans hIcard.ge) hTfin
  have hcT := hroot c hc hcr
  rw [← hIeq] at hcT
  obtain ⟨j, hj, hjc⟩ := hcT
  exact ⟨j, hj, Units.ext hjc.symm⟩

/-! ### `A` grows -/

theorem vsM_grow [FiniteDimensional (ZMod p) V] [Nontrivial V] : VsMGrowStmt p V := by
  intro H A N hA hNH hN hNC hNab hNA
  have hcomm : A ⊔ N ≤ Subgroup.centralizer ((A ⊔ N : Subgroup 𝔼ˣ) : Set 𝔼ˣ) := by
    have hc : Subgroup.centralizer ((A ⊔ N : Subgroup 𝔼ˣ) : Set 𝔼ˣ) =
        Subgroup.centralizer ((A : Set 𝔼ˣ) ∪ N) := by
      rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
    rw [hc]
    have hA' : A ≤ Subgroup.centralizer ((A : Set 𝔼ˣ) ∪ N) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      rintro x (hx | hx)
      · exact hA.2.2 x hx a ha
      · exact (Subgroup.mem_centralizer_iff.1 (hNC hx) a ha).symm
    have hN' : N ≤ Subgroup.centralizer ((A : Set 𝔼ˣ) ∪ N) := by
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      rintro x (hx | hx)
      · exact Subgroup.mem_centralizer_iff.1 (hNC hn) x hx
      · exact hNab x hx n hn
    exact sup_le hA' hN'
  refine ⟨⟨sup_le hA.1 hNH, ⟨fun n hn g => ?_⟩, fun a ha b hb => ?_⟩,
    lt_of_le_of_ne le_sup_left fun h => hNA (le_sup_right.trans h.symm.le)⟩
  · rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hle : (A ⊔ N).map (MulAut.conj (g : 𝔼ˣ)).toMonoidHom ≤ A ⊔ N := by
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact hA.conj_mem g.2 ha
      · rintro _ ⟨a, ha, rfl⟩
        exact hN g g.2 a ha
    exact hle ⟨n, hn, rfl⟩
  · exact Subgroup.mem_centralizer_iff.1 (hcomm hb) a ha

/-! ### The pairing -/

theorem vsM_pair [FiniteDimensional (ZMod p) V] [Nontrivial V] : VsMPairStmt p V := by
  intro A T r hT hc
  set P := Subgroup.closure T
  have hPC : P ≤ Subgroup.centralizer (A : Set 𝔼ˣ) := (Subgroup.closure_le _).2 hT
  have hSP : ∀ s ∈ vsMScal A, ∀ x ∈ P, s * x = x * s := fun s hs x hx =>
    (vsM_comm_scal (hPC hx) hs).symm
  have hcm : ∀ x ∈ P, ∀ y ∈ P, ∀ z ∈ P, Commute ⁅x, y⁆ z := fun x hx y hy z hz =>
    hSP _ (hc x hx y hy) z hz
  refine ⟨fun x hx y hy z hz => ⟨vsM_comm_mul_left (hcm y hy z hz x hx) (hcm y hy z hz z hz),
    vsM_comm_mul_right (hcm x hx z hz y hy)⟩, fun x hx y hy hxr => ?_, fun hTr x hx => ?_⟩
  · rw [← vsM_comm_pow_left (hcm x hx y hy x hx) (hcm x hx y hy y hy) r,
      commutatorElement_eq_one_iff_mul_comm]
    exact hSP _ hxr y hy
  · induction hx using Subgroup.closure_induction with
    | mem x hx => exact hTr x hx
    | one => rw [one_pow]; exact (vsMScal A).one_mem
    | mul x y hx hy ihx ihy =>
      obtain ⟨d, hd, h⟩ := vsM_pow_mul P (vsMScal A) hSP hc hx hy r
      rw [h]
      exact (vsMScal A).mul_mem ((vsMScal A).mul_mem ihx ihy) hd
    | inv x hx ih => rw [inv_pow]; exact (vsMScal A).inv_mem ih

/-- **M3** is `vsT_index_centralizer`. -/
theorem vsM_cent [FiniteDimensional (ZMod p) V] [Nontrivial V] : VsMCentStmt p V :=
  fun _ _ hA hdom => vsT_index_centralizer hA hdom

end GI.Proved
