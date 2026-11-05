module

public import Workspace.Algorithm.CitedInstances
public import Workspace.Algorithm.HierInv
public import Workspace.CameronRange
public import Mathlib.Data.Fintype.Powerset

@[expose] public section

/-!
# The dispatcher from a primitive quotient and Maróti's theorem

Section 3.3: "The standard primitive-group reduction either enumerates a group of order
`d^{O(log d)}` on an actual `d`-block quotient, or exposes a large alternating action";
"Product actions refine the actual hierarchy". Algorithm 5: "**if** enumeration or a product
refinement applies **then** apply that reduction and solve its children with `Continue`";
otherwise "Normalize the single alternating factor". Section A.5, "Selection of the quotient
and its cap": "Ordinary Cameron dispatch uses the coarsest available primitive quotient of the
whole current group … Its degree-`d` constituent is therefore an actual quotient of the acting
group: enumerating it has its stated quotient index and leaves kernel orbits of size at most
`n/d`."

## The data

A `PrimitiveQuotient` of a state is the block map `blk : Ω → [d]` of the coarsest primitive
quotient, the action `ρ : G → Sym(d)` on the blocks, with `blk` equivariant on the domain and
onto, `ρ(G)` primitive, and the exposed hierarchy (Algorithm 5: "Expose the next primitive
quotient"): a hierarchy `pre ++ top :: post` with no larger `ρ` and `Q` than the stored one,
which satisfies the hierarchy invariant, and whose interval `top` goes from the blocks of the
quotient to the whole domain (ratio `d`). It is built from the stored hierarchy in
`Workspace/Algorithm/Expose.lean`.

## The dispatcher

`PrimitiveQuotient.dispatch` decides, as the paper does:
* if `|ρ(G)| ≤ exp(a (log d)²)`, enumerate the quotient: the children run under the block
  kernel `K = ker ρ` (`DispatchStep.ofEnumeration`). The orbit fact `d |v^K| ≤ s` is proved
  here (`block_kernel_orbit`): the blocks of a transitive group have equal size `s/d`, and a
  `K`-orbit lies in one block.
* otherwise, if `ρ(G)` is in Maróti's product case with `r ≥ 2` coordinates, refine the
  product: the children run under the coordinate subgroup, whose index is at most
  `r! ≤ 2^r r!` (`index_coordinate_le`: the coordinate permutation of an element is unique when
  `binom(m,k) ≥ 2`, so it is a homomorphism `G → Sym(r)` whose kernel is the coordinate
  subgroup).
* otherwise the quotient is a single factor (`SingleFactor`): Maróti's case (i) with `r = 1`.

The recursion's dispatcher step `DispatchStep` (constructor `Run.dispatch`) carries the
primitive quotient and the case that applies (small, or not small and a product with `r ≥ 2`).
Its reduction (`DispatchStep.red`: child group, cosets, hierarchy) is computed from the
quotient, so a step is determined by its quotient (`DispatchStep.K_hier'_eq`), and every step is
proper (`DispatchStep.exists_not_mem_K`: the child group is not the whole group).

That the three cases are exhaustive is `dispatch_cases`: by Maróti's theorem
(`GI.Cited.MarotiPrimitive`), a primitive group of degree `d ≥ 25` that is not small is in
case (i); in case (i) with `m ≤ (k+1)² - 2` the group is small by the Cameron-range bound
(`GI.CameronRange.cameron_range_order`); and degrees below `25` are small. This needs
`a ≥ 128`.
-/

namespace GI.Algorithm

open Equiv Equiv.Perm
open scoped Pointwise

variable {Ω C : Type}

/-! ### The block kernel: orbits of at most `s/d` points -/

/-- **The block-kernel orbit fact** (Section 7.2, row "Primitive enumeration": "Its kernel
orbits have size at most `s/d`"). Let `G` be transitive on the domain, `blk` an equivariant
map from the domain onto `d` blocks, and `K ≤ G` fix every block. Then every `K`-orbit in the
domain has at most `s/d` points: `d |v^K| ≤ s`. The blocks have equal size, since `G` is
transitive and maps blocks to blocks. -/
theorem block_kernel_orbit [Finite Ω] (S : State Ω C) (htr : S.Transitive) {d : ℕ}
    (blk : Ω → Fin d) (ρ : S.G →* Perm (Fin d))
    (heq : ∀ (g : S.G), ∀ v ∈ S.dom, blk ((g : Perm Ω) v) = ρ g (blk v))
    (honto : ∀ i, ∃ v ∈ S.dom, blk v = i)
    (K : Subgroup (Perm Ω)) (hKG : K ≤ S.G) (hK : ∀ k ∈ K, ∀ v ∈ S.dom, blk (k v) = blk v) :
    ∀ v ∈ S.dom, d * Nat.card (orb K v) ≤ S.size := by
  classical
  haveI : Fintype Ω := Fintype.ofFinite Ω
  intro v hv
  set D : Finset Ω := S.dom.toFinset
  let fib : Fin d → Finset Ω := fun i => D.filter fun w => blk w = i
  -- The blocks have equal size.
  have hle : ∀ i j, (fib i).card ≤ (fib j).card := by
    intro i j
    obtain ⟨vi, hvi, rfl⟩ := honto i
    obtain ⟨vj, hvj, rfl⟩ := honto j
    obtain ⟨g, hg, hgv⟩ := htr vi hvi vj hvj
    refine Finset.card_le_card_of_injOn g (fun w hw => ?_) (fun a _ b _ h => g.injective h)
    simp only [fib, D, Finset.coe_filter, Set.mem_toFinset, Set.mem_setOf_eq] at hw ⊢
    refine ⟨(S.dom_inv g hg w).2 hw.1, ?_⟩
    have h1 := heq ⟨g, hg⟩ w hw.1
    have h2 := heq ⟨g, hg⟩ vi hvi
    simp only at h1 h2
    rw [h1, hw.2, ← h2, hgv]
  have hsize : S.size = ∑ i : Fin d, (fib i).card := by
    have h := Finset.card_eq_sum_card_fiberwise (f := blk) (s := D) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    change Nat.card S.dom = _
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card']
    simpa [fib, D] using h
  -- The `K`-orbit of `v` lies in the block of `v`.
  have horb : Nat.card (orb K v) ≤ (fib (blk v)).card := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard ?_ (Finset.finite_toSet _)
    rintro _ ⟨k, hk, rfl⟩
    simp only [fib, D, Finset.coe_filter, Set.mem_toFinset, Set.mem_setOf_eq]
    exact ⟨(S.dom_inv k (hKG hk) v).2 hv, hK k hk v hv⟩
  calc d * Nat.card (orb K v) ≤ d * (fib (blk v)).card := Nat.mul_le_mul_left _ horb
    _ = ∑ _i : Fin d, (fib (blk v)).card := by simp
    _ ≤ ∑ i : Fin d, (fib i).card := Finset.sum_le_sum fun i _ => hle _ _
    _ = S.size := hsize.symm

/-! ### Product actions: the coordinate permutation and the index `r!` -/

namespace Product

/-- The `k`-subsets of `[m]`. -/
abbrev KSet (m k : ℕ) := {A : Finset (Fin m) // A.card = k}

variable {n m k r : ℕ}

theorem kSetPerm_mul (a b : Perm (Fin m)) (A : KSet m k) :
    GI.Cited.kSetPerm (a * b) A = GI.Cited.kSetPerm a (GI.Cited.kSetPerm b A) := by
  apply Subtype.ext
  simp [GI.Cited.kSetPerm, Finset.map_map]
  rfl

theorem kSetPerm_one (A : KSet m k) : GI.Cited.kSetPerm (1 : Perm (Fin m)) A = A := by
  apply Subtype.ext
  ext x
  simp [GI.Cited.kSetPerm]
  rfl

/-- `g` acts in the product action as `(σ, h)`: `e(g x)_i = h_i (e(x)_{σ i})`. -/
def IsProd (e : Fin n ≃ (Fin r → KSet m k)) (g : Perm (Fin n)) (σ : Perm (Fin r))
    (h : Fin r → Perm (Fin m)) : Prop :=
  ∀ x, e (g x) = fun i => GI.Cited.kSetPerm (h i) (e x (σ i))

theorem isProd_one (e : Fin n ≃ (Fin r → KSet m k)) : IsProd e 1 1 fun _ => 1 := by
  intro x
  funext i
  simp [kSetPerm_one]

theorem isProd_mul {e : Fin n ≃ (Fin r → KSet m k)} {g₁ g₂ : Perm (Fin n)} {σ₁ σ₂ h₁ h₂}
    (h1 : IsProd e g₁ σ₁ h₁) (h2 : IsProd e g₂ σ₂ h₂) :
    IsProd e (g₁ * g₂) (σ₂ * σ₁) fun i => h₁ i * h₂ (σ₁ i) := by
  intro x
  funext i
  rw [Perm.mul_apply, h1, h2]
  simp [kSetPerm_mul]

/-- **The coordinate permutation is unique** when there are at least two `k`-subsets. -/
theorem sigma_unique {e : Fin n ≃ (Fin r → KSet m k)} (htwo : 2 ≤ m.choose k)
    {g : Perm (Fin n)} {σ σ' h h'} (hσ : IsProd e g σ h) (hσ' : IsProd e g σ' h') :
    σ = σ' := by
  classical
  have hcard : 1 < Fintype.card (KSet m k) := by
    rw [Fintype.card_finset_len, Fintype.card_fin]; omega
  obtain ⟨A, B, hAB⟩ := Fintype.exists_pair_of_one_lt_card hcard
  ext i
  by_contra hne
  have hne' : σ' i ≠ σ i := fun h => hne (congrArg Fin.val h.symm)
  have key : ∀ x : Fin r → KSet m k,
      GI.Cited.kSetPerm (h i) (x (σ i)) = GI.Cited.kSetPerm (h' i) (x (σ' i)) := by
    intro x
    have e1 := congrFun (hσ (e.symm x)) i
    have e2 := congrFun (hσ' (e.symm x)) i
    rw [e.apply_symm_apply] at e1 e2
    exact e1.symm.trans e2
  let x₀ : Fin r → KSet m k := fun _ => A
  let x₁ : Fin r → KSet m k := Function.update x₀ (σ i) B
  have k0 := key x₀
  have k1 := key x₁
  simp only [x₁, x₀, Function.update_self, Function.update_of_ne hne'] at k0 k1
  exact hAB ((GI.Cited.kSetPerm (h i)).injective (k1.trans k0.symm).symm)

variable (e : Fin n ≃ (Fin r → KSet m k)) (G : Subgroup (Perm (Fin n)))
  (hG : ∀ g ∈ G, ∃ σ h, IsProd e g σ h)

/-- The coordinate permutation of an element of `G`. -/
noncomputable def coord (g : G) : Perm (Fin r) := (hG g g.2).choose

theorem coord_spec (g : G) : ∃ h, IsProd e g (coord e G hG g) h := (hG g g.2).choose_spec

/-- `g ↦ σ_g⁻¹` is a homomorphism `G → Sym(r)` (the coordinate permutations compose in the
opposite order). -/
noncomputable def coordHom (htwo : 2 ≤ m.choose k) : G →* Perm (Fin r) where
  toFun g := (coord e G hG g)⁻¹
  map_one' := by
    obtain ⟨h, hh⟩ := coord_spec e G hG 1
    rw [sigma_unique htwo hh (isProd_one e), inv_one]
  map_mul' g₁ g₂ := by
    obtain ⟨h₁, hh₁⟩ := coord_spec e G hG g₁
    obtain ⟨h₂, hh₂⟩ := coord_spec e G hG g₂
    obtain ⟨h, hh⟩ := coord_spec e G hG (g₁ * g₂)
    rw [sigma_unique htwo hh (isProd_mul hh₁ hh₂), mul_inv_rev]

theorem coordHom_eq_one_iff (htwo : 2 ≤ m.choose k) (g : G) :
    coordHom e G hG htwo g = 1 ↔ ∃ h, IsProd e g 1 h := by
  constructor
  · intro h1
    obtain ⟨h, hh⟩ := coord_spec e G hG g
    have : coord e G hG g = 1 := inv_eq_one.1 h1
    exact ⟨h, this ▸ hh⟩
  · rintro ⟨h, hh⟩
    obtain ⟨h', hh'⟩ := coord_spec e G hG g
    change (coord e G hG g)⁻¹ = 1
    rw [sigma_unique htwo hh' hh, inv_one]

/-- **The order of a product-action group**: `|G| ≤ r! (m!)^r`, since `(σ_g, h_g)` determines
`g`. -/
theorem card_le (e : Fin n ≃ (Fin r → KSet m k)) (G : Subgroup (Perm (Fin n)))
    (hG : ∀ g ∈ G, ∃ σ h, IsProd e g σ h) :
    Nat.card G ≤ (m.factorial) ^ r * r.factorial := by
  classical
  let F : G → Perm (Fin r) × (Fin r → Perm (Fin m)) := fun g =>
    (coord e G hG g, (coord_spec e G hG g).choose)
  have hF : Function.Injective F := by
    intro g₁ g₂ hF
    have h1 := (coord_spec e G hG g₁).choose_spec
    have h2 := (coord_spec e G hG g₂).choose_spec
    simp only [F, Prod.mk.injEq] at hF
    apply Subtype.ext
    ext x
    have := (h1 x).trans ((congrArg₂ (fun σ h => fun i => GI.Cited.kSetPerm (h i) (e x (σ i)))
      hF.1 hF.2).trans (h2 x).symm)
    exact congrArg Fin.val (e.injective this)
  have := Nat.card_le_card_of_injective F hF
  simp only [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
    Fintype.card_fun] at this ⊢
  rw [mul_comm]
  exact this

end Product

/-! ### The exponent of the integer small test -/

/-- The exponent `b = ⌊a log 2⌋` of the integer small test `PrimitiveQuotient.SmallZ`. -/
noncomputable def Params.smallExp (P : Params) : ℕ := ⌊P.a * Real.log 2⌋₊

theorem Params.smallExp_le (P : Params) (ha : 0 ≤ P.a) : (P.smallExp : ℝ) ≤ P.a * Real.log 2 :=
  Nat.floor_le (mul_nonneg ha (Real.log_nonneg (by norm_num)))

/-! ### The primitive quotient of a state -/

/-- **The coarsest primitive quotient** of a state (Section A.5, "Selection of the quotient and
its cap"): the block map `blk` onto `d` blocks, the block action `ρ`, primitive on the blocks,
and the exposed hierarchy `pre ++ top :: post` (Algorithm 5: "Expose the next primitive quotient
above any retained column partition"; Section 3.3: "new invariant partitions only refine it").
The fine end of `top` is the block partition of the quotient on the domain, its coarse end
holds the whole domain, and its ratio is `d`. The exposed hierarchy satisfies the hierarchy
invariant, and its `ρ` and `Q` are at most those of the stored hierarchy (Section 7.1:
"Splitting a ratio into at least two nontrivial factors decreases `ρ`. … Splitting or
restricting intervals also cannot increase `Q`"). -/
structure PrimitiveQuotient {Ω C : Type} (S : State Ω C) where
  d : ℕ
  blk : Ω → Fin d
  ρ : S.G →* Perm (Fin d)
  equivariant : ∀ (g : S.G), ∀ v ∈ S.dom, blk ((g : Perm Ω) v) = ρ g (blk v)
  onto : ∀ i, ∃ v ∈ S.dom, blk v = i
  primitive : MulAction.IsPreprimitive ρ.range (Fin d)
  two_le : 2 ≤ d
  pre : List (Interval Ω)
  top : Interval Ω
  post : List (Interval Ω)
  rho_le : State.hierRho (pre ++ top :: post) ≤ State.hierRho S.hier
  Q_le : State.hierQ (pre ++ top :: post) ≤ State.hierQ S.hier
  /-- The exposure either splits an interval into two nontrivial factors, so `ρ` drops, or adds
  no level, so the sum of the bounds does not grow (Section 7.1: "Splitting a ratio into at least
  two nontrivial factors decreases `ρ`"; a trivial interval is not stored). -/
  drop : State.hierRho (pre ++ top :: post) < State.hierRho S.hier ∨
    ((pre ++ top :: post).map Interval.cap).sum ≤ (S.hier.map Interval.cap).sum
  ratio_eq : top.ratio = d
  /-- The fine end of `top` is the block partition on the domain. -/
  fine_eq : ∀ v ∈ S.dom, ∀ w ∈ S.dom, (fineEnd ⊥ pre).r v w ↔ blk v = blk w
  /-- The coarse end of `top` holds the whole domain. -/
  top_univ : ∀ v ∈ S.dom, ∀ w ∈ S.dom, top.part.r v w
  /-- The exposed hierarchy satisfies the hierarchy invariant. -/
  tower : HierInv S.G S.dom (pre ++ top :: post)
  /-- Every interval of the exposed hierarchy is an old interval, or a new nontrivial one whose
  ratio, bound and origin are at most those of an old interval (Section 7.1: "Only nontrivial
  interval ratios occur"; the exposure splits one old interval). -/
  from_old : ∀ I ∈ pre ++ top :: post, I ∈ S.hier ∨ ∃ J ∈ S.hier, 2 ≤ I.ratio ∧
    I.ratio ≤ J.ratio ∧ I.cap ≤ J.cap ∧ I.origin = J.origin

namespace PrimitiveQuotient

variable {S : State Ω C} (Q : PrimitiveQuotient S)

/-- The block system on the positions: two positions of the domain are related when they lie
in the same block; positions off the domain form one class. -/
def blocks : Setoid Ω where
  r v w := (v ∈ S.dom ∧ w ∈ S.dom ∧ Q.blk v = Q.blk w) ∨ (v ∉ S.dom ∧ w ∉ S.dom)
  iseqv := ⟨fun v => by
      by_cases hv : v ∈ S.dom
      exacts [Or.inl ⟨hv, hv, rfl⟩, Or.inr ⟨hv, hv⟩],
    fun h => by rcases h with ⟨a, b, c⟩ | ⟨a, b⟩; exacts [Or.inl ⟨b, a, c.symm⟩, Or.inr ⟨b, a⟩],
    fun h1 h2 => by
      rcases h1 with ⟨a, b, c⟩ | ⟨a, b⟩ <;> rcases h2 with ⟨a', b', c'⟩ | ⟨a', b'⟩
      · exact Or.inl ⟨a, b', c.trans c'⟩
      · exact absurd b a'
      · exact absurd a' b
      · exact Or.inr ⟨a, b'⟩⟩

theorem blocks_inv : ∀ g ∈ S.G, ∀ v w, Q.blocks.r (g v) (g w) ↔ Q.blocks.r v w := by
  intro g hg v w
  have hv := S.dom_inv g hg v
  have hw := S.dom_inv g hg w
  show (_ ∧ _ ∧ _) ∨ _ ↔ (_ ∧ _ ∧ _) ∨ _
  constructor
  · rintro (⟨a, b, c⟩ | ⟨a, b⟩)
    · refine Or.inl ⟨hv.1 a, hw.1 b, ?_⟩
      rw [Q.equivariant ⟨g, hg⟩ v (hv.1 a), Q.equivariant ⟨g, hg⟩ w (hw.1 b)] at c
      exact (Q.ρ ⟨g, hg⟩).injective c
    · exact Or.inr ⟨fun h => a (hv.2 h), fun h => b (hw.2 h)⟩
  · rintro (⟨a, b, c⟩ | ⟨a, b⟩)
    · refine Or.inl ⟨hv.2 a, hw.2 b, ?_⟩
      rw [Q.equivariant ⟨g, hg⟩ v a, Q.equivariant ⟨g, hg⟩ w b, c]
    · exact Or.inr ⟨fun h => a (hv.1 h), fun h => b (hw.1 h)⟩

/-- `d ≤ s`: the block map is onto from the domain. -/
theorem d_le_size [Finite Ω] : Q.d ≤ S.size := by
  classical
  choose f hf hfi using Q.onto
  have hinj : Function.Injective fun i => (⟨f i, hf i⟩ : S.dom) := by
    intro i j h
    have := congrArg (fun x : S.dom => Q.blk x.1) h
    simp only [hfi] at this
    exact this
  have := Nat.card_le_card_of_injective _ hinj
  simpa [State.size] using this

/-- The block kernel `ker ρ`, as a subgroup of `Sym(Ω)`. -/
def kernel : Subgroup (Perm Ω) := Q.ρ.ker.map S.G.subtype

theorem kernel_le : Q.kernel ≤ S.G := Subgroup.map_subtype_le _

theorem kernel_subgroupOf : Q.kernel.subgroupOf S.G = Q.ρ.ker := by
  ext g
  simp [kernel, Subgroup.mem_subgroupOf]

/-- The enumeration children run under the block kernel; its orbits have at most `s/d`
points. -/
theorem kernel_orbit [Finite Ω] (htr : S.Transitive) :
    ∀ v ∈ S.dom, Q.d * Nat.card (orb Q.kernel v) ≤ S.size := by
  refine block_kernel_orbit S htr Q.blk Q.ρ Q.equivariant Q.onto Q.kernel Q.kernel_le ?_
  rintro _ ⟨g, hg, rfl⟩ v hv
  change Q.blk ((g : Perm Ω) v) = _
  rw [Q.equivariant g v hv, MonoidHom.mem_ker.1 hg]
  rfl

/-- The quotient is **small**: its order is at most `exp(a (log d)²)`, so it is enumerated. -/
def Small (a : ℝ) : Prop := (Nat.card Q.ρ.range : ℝ) ≤ Real.exp (a * Real.log Q.d ^ 2)

/-- **The integer small test**: `|ρ(G)| ≤ d^(b ⌊log₂ d⌋)`. A program decides it from the order
of `ρ(G)` and `d`. The real test `Small a` cannot be decided exactly (its equality cases are open
transcendence questions), so `Run.normalize` asks only that this test fails. With
`b = ⌊a log 2⌋` it implies `Small a` (`small_of_smallZ`), so every quotient that fails `Small a`
also fails it (`not_smallZ_of_not_small`). -/
def SmallZ (b : ℕ) : Prop := Nat.card Q.ρ.range ≤ Q.d ^ (b * Nat.log 2 Q.d)

/-- **The integer test implies the real one** when `b ≤ a log 2`: with `L = ⌊log₂ d⌋` we have
`L log 2 ≤ log d`, so `d^(b L) = exp(b L log d) ≤ exp((b / log 2) (log d)²) ≤ exp(a (log d)²)`. -/
theorem small_of_smallZ {a : ℝ} {b : ℕ} (hb : (b : ℝ) ≤ a * Real.log 2) (h : Q.SmallZ b) :
    Q.Small a := by
  unfold Small
  unfold SmallZ at h
  have hd2 := Q.two_le
  have hdpos : (0 : ℝ) < Q.d := by exact_mod_cast (show 0 < Q.d by omega)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hld : 0 ≤ Real.log Q.d := Real.log_nonneg (by exact_mod_cast (show 1 ≤ Q.d by omega))
  -- `L log 2 ≤ log d`, from `2^L ≤ d`
  have hL : (Nat.log 2 Q.d : ℝ) * Real.log 2 ≤ Real.log Q.d := by
    have h2L : ((2 ^ Nat.log 2 Q.d : ℕ) : ℝ) ≤ Q.d := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have := Real.log_le_log (by positivity) h2L
    rwa [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at this
  have hpow : ((Q.d ^ (b * Nat.log 2 Q.d) : ℕ) : ℝ) =
      Real.exp ((b : ℝ) * Nat.log 2 Q.d * Real.log Q.d) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, Real.rpow_def_of_pos hdpos]
    push_cast; ring_nf
  -- `b L log d ≤ a (log d)²`, multiplied by `log 2 > 0`
  have hexp : (b : ℝ) * Nat.log 2 Q.d * Real.log Q.d ≤ a * Real.log Q.d ^ 2 := by
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have h1 : (b : ℝ) * Nat.log 2 Q.d * Real.log Q.d * Real.log 2 ≤ b * Real.log Q.d ^ 2 := by
      have := mul_le_mul_of_nonneg_left hL (mul_nonneg hb0 hld)
      nlinarith
    have h2 : (b : ℝ) * Real.log Q.d ^ 2 ≤ a * Real.log 2 * Real.log Q.d ^ 2 :=
      mul_le_mul_of_nonneg_right hb (sq_nonneg _)
    have h3 : (b : ℝ) * Nat.log 2 Q.d * Real.log Q.d * Real.log 2 ≤
        a * Real.log Q.d ^ 2 * Real.log 2 := by nlinarith
    exact le_of_mul_le_mul_right h3 hl2
  calc (Nat.card Q.ρ.range : ℝ) ≤ ((Q.d ^ (b * Nat.log 2 Q.d) : ℕ) : ℝ) := by exact_mod_cast h
    _ = _ := hpow
    _ ≤ _ := Real.exp_le_exp.2 hexp

/-- A quotient that fails the real test fails the integer test with `b ≤ a log 2`. -/
theorem not_smallZ_of_not_small {a : ℝ} {b : ℕ} (hb : (b : ℝ) ≤ a * Real.log 2)
    (h : ¬ Q.Small a) : ¬ Q.SmallZ b := fun hz => h (Q.small_of_smallZ hb hz)

/-- Maróti's product structure on the quotient, with `r` coordinates. -/
def ProductStructure (m k r : ℕ) (e : Fin Q.d ≃ (Fin r → Product.KSet m k)) : Prop :=
  (∀ g ∈ Q.ρ.range, ∃ σ h, Product.IsProd e g σ h) ∧
  (∀ h : Fin r → Perm (Fin m), (∀ i, h i ∈ alternatingGroup (Fin m)) →
    (e.trans ((Equiv.piCongrRight fun i => GI.Cited.kSetPerm (h i)).trans e.symm) :
      Perm (Fin Q.d)) ∈ Q.ρ.range)

/-- **The single-factor case**: Maróti's case (i) with one coordinate (Algorithm 5,
"Normalize the single alternating factor"). -/
def SingleFactor : Prop :=
  ∃ (m k : ℕ) (e : Fin Q.d ≃ (Fin 1 → Product.KSet m k)), Q.ProductStructure m k 1 e

/-- The product case with `r ≥ 2` coordinates. -/
def ProductCase : Prop :=
  ∃ (m k r : ℕ) (e : Fin Q.d ≃ (Fin r → Product.KSet m k)), 2 ≤ r ∧ Q.ProductStructure m k r e

theorem card_kset_pow {m k r : ℕ} (e : Fin Q.d ≃ (Fin r → Product.KSet m k)) :
    Q.d = m.choose k ^ r := by
  have := Fintype.card_congr e
  simpa [Fintype.card_fun, Fintype.card_finset_len] using this

/-! #### The three cases are exhaustive -/

theorem log_two_sq_gt : (0.48 : ℝ) < Real.log 2 ^ 2 := by
  have := Real.log_two_gt_d9
  nlinarith

/-- Degrees below `25` are small for `a ≥ 128`: `|ρ(G)| ≤ d! ≤ 24! < 2^80 ≤ exp(128 (log 2)²)`. -/
theorem small_of_lt_25 {a : ℝ} (ha : 128 ≤ a) (hd : Q.d < 25) : Q.Small a := by
  unfold Small
  have hcard : Nat.card Q.ρ.range ≤ (24).factorial := by
    have h1 : Nat.card Q.ρ.range ≤ Nat.card (Perm (Fin Q.d)) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    rw [Nat.card_perm, Nat.card_fin] at h1
    exact h1.trans (Nat.factorial_le (by omega))
  have h24 : (24).factorial ≤ 2 ^ 80 := by decide
  have hlog : Real.log 2 ≤ Real.log Q.d :=
    Real.log_le_log (by norm_num) (by exact_mod_cast Q.two_le)
  have hl2 := Real.log_two_gt_d9
  have hsq : Real.log 2 ^ 2 ≤ Real.log Q.d ^ 2 := pow_le_pow_left₀ (by linarith) hlog 2
  calc (Nat.card Q.ρ.range : ℝ) ≤ ((2 ^ 80 : ℕ) : ℝ) := by exact_mod_cast hcard.trans h24
    _ = Real.exp (80 * Real.log 2) := by
        rw [← Real.log_rpow (by norm_num), Real.exp_log (by positivity)]; norm_num
    _ ≤ Real.exp (a * Real.log Q.d ^ 2) := by
        apply Real.exp_le_exp.2
        have : (80 : ℝ) * Real.log 2 ≤ 128 * Real.log 2 ^ 2 := by nlinarith
        have h0 : 0 ≤ Real.log Q.d ^ 2 := sq_nonneg _
        nlinarith

/-- The Cameron range is small for `a ≥ 128` (`GI.CameronRange.cameron_range_order`). -/
theorem small_of_cameron_range {a : ℝ} (ha : 128 ≤ a) {m k r : ℕ}
    (e : Fin Q.d ≃ (Fin r → Product.KSet m k)) (hS : Q.ProductStructure m k r e)
    (hm : m + 2 ≤ (min k (m - k) + 1) ^ 2) : Q.Small a := by
  have hd := Q.card_kset_pow e
  have h2 := Q.two_le
  -- `binom(m,k) ≥ 2` and `r ≥ 1`
  have hb : 2 ≤ m.choose k := by
    by_contra h
    have : m.choose k ^ r ≤ 1 := by
      calc m.choose k ^ r ≤ 1 ^ r := Nat.pow_le_pow_left (by omega) r
        _ = 1 := one_pow r
    omega
  have hr : 1 ≤ r := by
    by_contra h
    have : r = 0 := by omega
    rw [this, pow_zero] at hd
    omega
  have hkm : k ≤ m := by
    by_contra h
    rw [Nat.choose_eq_zero_of_lt (by omega)] at hb
    omega
  have hk0 : k ≠ 0 := by rintro rfl; simp at hb
  have hkm' : k ≠ m := by rintro rfl; simp at hb
  set k' := min k (m - k) with hk'
  have hbk' : m.choose k' = m.choose k := by
    rcases min_choice k (m - k) with h | h
    · rw [hk', h]
    · rw [hk', h, Nat.choose_symm hkm]
  have hcard := Product.card_le e Q.ρ.range hS.1
  have hcam := GI.CameronRange.cameron_range_order (k := k') (r := r) (m := m)
    (by omega) (by omega) hm hr
  rw [hbk', ← hd] at hcam
  unfold Small
  have hl : 0 ≤ Real.log (Q.d : ℝ) ^ 2 := sq_nonneg _
  calc (Nat.card Q.ρ.range : ℝ) ≤ ((m.factorial ^ r * r.factorial : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ Real.exp (103 * Real.log (Q.d : ℝ) ^ 2) := hcam
    _ ≤ Real.exp (a * Real.log Q.d ^ 2) := Real.exp_le_exp.2 (by nlinarith)

/-- **The dispatcher's cases are exhaustive** (Section 3.3 and Section A.5, from
`GI.Cited.MarotiPrimitive`): with `a ≥ 128`, the quotient is small, or in the product case
with `r ≥ 2`, or a single factor. -/
theorem dispatch_cases (hM : GI.Cited.MarotiPrimitive) {a : ℝ} (ha : 128 ≤ a) :
    Q.Small a ∨ Q.ProductCase ∨ Q.SingleFactor := by
  by_cases hd : Q.d < 25
  · exact Or.inl (Q.small_of_lt_25 ha hd)
  push Not at hd
  rcases CitedInstances.maroti_dichotomy hM hd Q.ρ.range Q.primitive with h | ⟨m, k, r, e, h1, h2⟩
  · left
    unfold Small
    refine h.trans (Real.exp_le_exp.2 ?_)
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  · have hS : Q.ProductStructure m k r e := ⟨h1, h2⟩
    by_cases hm : m + 2 ≤ (min k (m - k) + 1) ^ 2
    · exact Or.inl (Q.small_of_cameron_range ha e hS hm)
    rcases Nat.lt_or_ge r 2 with hr | hr
    · -- `r = 1` (`r = 0` would give `d = 1`)
      have hdd := Q.card_kset_pow e
      have hr1 : r = 1 := by
        rcases Nat.lt_or_ge r 1 with h0 | h0
        · have : r = 0 := by omega
          rw [this, pow_zero] at hdd; omega
        · omega
      subst hr1
      exact Or.inr (Or.inr ⟨m, k, e, hS⟩)
    · exact Or.inr (Or.inl ⟨m, k, r, e, hr, hS⟩)

/-! #### The two reductions -/

/-- **Enumeration of a small quotient** (`Reduction.ofEnumeration`): the children run under
the block kernel; index `|ρ(G)| ≤ exp(a (log d)²)`; orbits of at most `s/d` points
(`kernel_orbit`); the children keep the exposed hierarchy. -/
noncomputable def enumeration [Finite Ω] (P : Params) (htr : S.Transitive)
    (hsmall : Q.Small P.a) : Reduction P S :=
  CitedInstances.Reduction.ofEnumeration P S Q.blocks Q.blocks_inv Q.kernel Q.kernel_le Q.d
    Q.two_le Q.d_le_size
    (by rw [Q.kernel_subgroupOf, Subgroup.index_ker]; exact hsmall)
    (Q.kernel_orbit htr) (Q.pre ++ Q.top :: Q.post) Q.rho_le Q.Q_le

/-- The coordinate subgroup of the product case, as a subgroup of `Sym(Ω)`: the elements whose
block action fixes every coordinate. -/
noncomputable def coordinateGroup {m k r : ℕ} (e : Fin Q.d ≃ (Fin r → Product.KSet m k))
    (hS : Q.ProductStructure m k r e) (hb : 2 ≤ m.choose k) : Subgroup (Perm Ω) :=
  ((Product.coordHom e Q.ρ.range hS.1 hb).comp Q.ρ.rangeRestrict).ker.map S.G.subtype

/-- **The index of the coordinate subgroup** is at most `r! ≤ 2^r r!` (Section 7.2, row
"Product refinement": "Its outer index is at most `2^r r!`"). -/
theorem index_coordinate_le {m k r : ℕ} (e : Fin Q.d ≃ (Fin r → Product.KSet m k))
    (hS : Q.ProductStructure m k r e) (hb : 2 ≤ m.choose k) :
    ((Q.coordinateGroup e hS hb).subgroupOf S.G).index ≤ 2 ^ r * r.factorial := by
  have h1 : (Q.coordinateGroup e hS hb).subgroupOf S.G =
      ((Product.coordHom e Q.ρ.range hS.1 hb).comp Q.ρ.rangeRestrict).ker := by
    ext g; simp [coordinateGroup, Subgroup.mem_subgroupOf]
  rw [h1, Subgroup.index_ker]
  calc Nat.card ((Product.coordHom e Q.ρ.range hS.1 hb).comp Q.ρ.rangeRestrict).range
      ≤ Nat.card (Perm (Fin r)) := Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = r.factorial := by rw [Nat.card_perm, Nat.card_fin]
    _ ≤ 2 ^ r * r.factorial := Nat.le_mul_of_pos_left _ (by positivity)

/-- The partition by the coordinates `j ≥ i` of the product structure `e` on the domain (one
class off the domain). For `i = 0` it is the block partition, and for `i ≥ r` it holds the whole
domain. -/
def coordPart {m k r : ℕ} (e : Fin Q.d ≃ (Fin r → Product.KSet m k)) (i : ℕ) : Setoid Ω where
  r v w := (v ∈ S.dom ∧ w ∈ S.dom ∧ ∀ j : Fin r, i ≤ j.val → e (Q.blk v) j = e (Q.blk w) j) ∨
    (v ∉ S.dom ∧ w ∉ S.dom)
  iseqv := ⟨fun v => by
      by_cases hv : v ∈ S.dom
      exacts [Or.inl ⟨hv, hv, fun _ _ => rfl⟩, Or.inr ⟨hv, hv⟩],
    fun h => by
      rcases h with ⟨a, b, c⟩ | ⟨a, b⟩
      exacts [Or.inl ⟨b, a, fun j hj => (c j hj).symm⟩, Or.inr ⟨b, a⟩],
    fun h1 h2 => by
      rcases h1 with ⟨a, b, c⟩ | ⟨a, b⟩ <;> rcases h2 with ⟨a', b', c'⟩ | ⟨a', b'⟩
      · exact Or.inl ⟨a, b', fun j hj => (c j hj).trans (c' j hj)⟩
      · exact absurd b a'
      · exact absurd a' b
      · exact Or.inr ⟨a, b'⟩⟩

/-- **The coordinate intervals** of the product refinement: interval `i` goes from the
coordinates `j ≥ i` to the coordinates `j ≥ i + 1`, with ratio `binom(m,k)` and the old bound
clamped by it (Section 3.3: "Product actions refine the actual hierarchy"; Section A.5:
"Refining its product coordinates gives each resulting interval cap …, clamped by any already
smaller valid cap"). -/
def coordHier {m k r : ℕ} (e : Fin Q.d ≃ (Fin r → Product.KSet m k)) : List (Interval Ω) :=
  (List.range r).map fun i =>
    ⟨Q.coordPart e (i + 1), m.choose k, min Q.top.cap (m.choose k), Q.top.origin⟩

/-- **The product refinement** (`Reduction.ofProduct`): the children run under the
coordinate subgroup, and the interval `top` of ratio `d = binom(m,k)^r` splits into the `r`
coordinate intervals `coordHier` of ratio `binom(m,k)` ("Refining its product coordinates gives
each resulting interval cap …, clamped by any already smaller valid cap"). -/
noncomputable def product [Finite Ω] (P : Params) {m k r : ℕ}
    (e : Fin Q.d ≃ (Fin r → Product.KSet m k)) (hS : Q.ProductStructure m k r e)
    (hr : 2 ≤ r) : Reduction P S :=
  have hd := Q.card_kset_pow e
  have hb : 2 ≤ m.choose k := by
    by_contra h
    have : m.choose k ^ r ≤ 1 := by
      calc m.choose k ^ r ≤ 1 ^ r := Nat.pow_le_pow_left (by omega) r
        _ = 1 := one_pow r
    have := Q.two_le
    omega
  CitedInstances.Reduction.ofProduct P S Q.blocks Q.blocks_inv (Q.coordinateGroup e hS hb)
    (Subgroup.map_subtype_le _) hb hr (Q.index_coordinate_le e hS hb)
    (by rw [← hd]; exact Q.d_le_size) Q.pre Q.post (Q.coordHier e)
    Q.top Q.rho_le Q.Q_le (by rw [Q.ratio_eq, hd]) (by simp [coordHier])
    (fun J hJ => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hJ
      rfl)
    (fun J hJ => by
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hJ
      exact min_le_left _ _)

/-- In a primitive group the block kernel is proper. -/
theorem exists_not_mem_kernel : ∃ g ∈ S.G, g ∉ Q.kernel := by
  haveI := Q.primitive
  have h2 := Q.two_le
  obtain ⟨⟨y, hy⟩, hyx⟩ := MulAction.exists_smul_eq Q.ρ.range (⟨0, by omega⟩ : Fin Q.d) ⟨1, by omega⟩
  obtain ⟨g, rfl⟩ := hy
  refine ⟨g, g.2, fun hg => ?_⟩
  obtain ⟨g', hg', hgg'⟩ := hg
  have : g' = g := Subtype.ext hgg'
  subst this
  have hg'' : Q.ρ g' = 1 := MonoidHom.mem_ker.1 hg'
  have : (Q.ρ g' : Perm (Fin Q.d)) ⟨0, by omega⟩ = ⟨1, by omega⟩ := hyx
  rw [hg''] at this
  simp at this

/-- **In the product case the coordinate subgroup is proper**: a primitive group permutes the
coordinates nontrivially. Otherwise the positions with a fixed first coordinate would form a
nontrivial block. -/
theorem exists_not_mem_coordinateGroup {m k r : ℕ} (e : Fin Q.d ≃ (Fin r → Product.KSet m k))
    (hS : Q.ProductStructure m k r e) (hb : 2 ≤ m.choose k) (hr : 2 ≤ r) :
    ∃ g ∈ S.G, g ∉ Q.coordinateGroup e hS hb := by
  classical
  by_contra hall
  push Not at hall
  -- every element of the image fixes every coordinate
  have hfix : ∀ y ∈ Q.ρ.range, ∃ h, Product.IsProd e y 1 h := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨g', hg', hgg'⟩ := hall g g.2
    have : g' = g := Subtype.ext hgg'
    subst this
    have hg'' := MonoidHom.mem_ker.1 hg'
    exact (Product.coordHom_eq_one_iff e Q.ρ.range hS.1 hb _).1 hg''
  have hcard : 1 < Fintype.card (Product.KSet m k) := by
    rw [Fintype.card_finset_len, Fintype.card_fin]; omega
  obtain ⟨A₀, A₁, hA⟩ := Fintype.exists_pair_of_one_lt_card hcard
  let i₀ : Fin r := ⟨0, by omega⟩
  let i₁ : Fin r := ⟨1, by omega⟩
  have hi : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  let B : Set (Fin Q.d) := {x | e x i₀ = A₀}
  -- the image of `B` under an element of the image is a fiber of the first coordinate
  have himg : ∀ y : Q.ρ.range, ∃ c, y • B = {x | e x i₀ = c} := by
    intro y
    obtain ⟨h, hh⟩ := hfix y y.2
    refine ⟨GI.Cited.kSetPerm (h i₀) A₀, Set.ext fun x => ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    have hx := congrFun (hh (((y⁻¹ : Q.ρ.range) : Perm (Fin Q.d)) x)) i₀
    have hyx : (y : Perm (Fin Q.d)) (((y⁻¹ : Q.ρ.range) : Perm (Fin Q.d)) x) = x := by
      simp
    change e (((y⁻¹ : Q.ρ.range) : Perm (Fin Q.d)) x) i₀ = A₀ ↔ _
    rw [hyx] at hx
    simp only [Set.mem_setOf_eq]
    rw [hx]
    simp only [Perm.one_apply]
    exact ⟨fun h1 => by rw [h1], fun h1 => (GI.Cited.kSetPerm (h i₀)).injective h1⟩
  have hblock : MulAction.IsBlock Q.ρ.range B := by
    intro y₁ y₂ hne
    obtain ⟨c₁, hc₁⟩ := himg y₁
    obtain ⟨c₂, hc₂⟩ := himg y₂
    rw [hc₁, hc₂] at hne ⊢
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    exact hne (by
      simp only [Set.mem_setOf_eq] at hx₁ hx₂
      rw [← hx₁, hx₂])
  rcases Q.primitive.isTrivialBlock_of_isBlock hblock with hsub | huniv
  · have h0 : e.symm (fun _ => A₀) ∈ B := by simp [B]
    have h1 : e.symm (Function.update (fun _ => A₀) i₁ A₁) ∈ B := by
      simp [B, Function.update_of_ne hi.symm]
    have := hsub h0 h1
    have := congrFun (e.symm.injective this) i₁
    simp at this
    exact hA this
  · have h2 : e.symm (Function.update (fun _ => A₀) i₀ A₁) ∈ B := by rw [huniv]; trivial
    simp [B] at h2
    exact hA h2.symm

/-- `binom(m,k) ≥ 2` for a product structure with at least one coordinate. -/
theorem two_le_choose {m k r : ℕ} (e : Fin Q.d ≃ (Fin r → Product.KSet m k)) :
    2 ≤ m.choose k := by
  have hd := Q.card_kset_pow e
  by_contra h
  have : m.choose k ^ r ≤ 1 := by
    calc m.choose k ^ r ≤ 1 ^ r := Nat.pow_le_pow_left (by omega) r
      _ = 1 := one_pow r
  have := Q.two_le
  omega

/-- **A product structure of the product case**: any way to write the quotient as a product
with `r ≥ 2` coordinates (Maróti's case (i)). The paper does not fix one. -/
structure ProductChoice where
  m : ℕ
  k : ℕ
  r : ℕ
  e : Fin Q.d ≃ (Fin r → Product.KSet m k)
  hS : Q.ProductStructure m k r e
  hr : 2 ≤ r

/-- The product structure that `ProductCase` supplies. -/
noncomputable def defaultProductChoice (hp : Q.ProductCase) : Q.ProductChoice where
  m := hp.choose
  k := hp.choose_spec.choose
  r := hp.choose_spec.choose_spec.choose
  e := hp.choose_spec.choose_spec.choose_spec.choose
  hS := hp.choose_spec.choose_spec.choose_spec.choose_spec.2
  hr := hp.choose_spec.choose_spec.choose_spec.choose_spec.1

/-- A product structure gives the product case. -/
theorem ProductChoice.productCase (c : Q.ProductChoice) : Q.ProductCase :=
  ⟨c.m, c.k, c.r, c.e, c.hr, c.hS⟩

/-- The product refinement of a product structure. -/
noncomputable def productRed [Finite Ω] (P : Params) (c : Q.ProductChoice) : Reduction P S :=
  Q.product P c.e c.hS c.hr

end PrimitiveQuotient

/-! ### The dispatcher step of the recursion -/

/-- **Coset representatives** of `K` in `G`: one element of `G` in each left coset. The paper
does not fix them; the children of a reduction run on the cosets `τ_j K`. -/
structure CosetReps (G K : Subgroup (Perm Ω)) where
  τ : Fin (K.subgroupOf G).index → Perm Ω
  mem : ∀ j, τ j ∈ G
  cover : (G : Set (Perm Ω)) ⊆ ⋃ j, τ j • (K : Set (Perm Ω))

/-- Coset representatives given by `exists_coset_cover`. -/
noncomputable def CosetReps.default [Finite Ω] (G K : Subgroup (Perm Ω)) : CosetReps G K :=
  ⟨(CitedInstances.exists_coset_cover G K).choose,
    (CitedInstances.exists_coset_cover G K).choose_spec.1,
    (CitedInstances.exists_coset_cover G K).choose_spec.2⟩

/-- A reduction with other coset representatives of its child group. -/
noncomputable def Reduction.withReps {P : Params} {S : State Ω C} (R : Reduction P S)
    (hn : R.n = (R.K.subgroupOf S.G).index) (c : CosetReps S.G R.K) : Reduction P S :=
  { R with
    τ := fun j => c.τ (Fin.cast hn j)
    τ_mem := fun j => c.mem _
    cover := fun g hg => by
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (c.cover hg)
      exact Set.mem_iUnion.2 ⟨Fin.cast hn.symm j, by simpa using hj⟩ }


/-- **The dispatcher step** (Algorithm 5, "**if** enumeration or a product refinement applies
**then** apply that reduction and solve its children with `Continue`"). It carries the coarsest
primitive quotient `Q` of the state (Section A.5, "Selection of the quotient and its cap") and
the case of the dispatcher that applies, in the order of `PrimitiveQuotient.dispatch`:

* `enumeration`: the quotient is small, `|ρ(G)| ≤ exp(a (log d)²)`;
* `product`: the quotient is in Maróti's product case with `r ≥ 2`. The step does not ask that
  the quotient is not small: Algorithm 5 says "if enumeration or a product refinement applies
  then apply that reduction", so either may be taken when both apply, and no proof uses the
  guard.

The reduction, its child group, its cosets and its hierarchy are computed from `Q`
(`DispatchStep.red`): the block kernel and the old hierarchy, or the coordinate subgroup and
the split hierarchy. There is no other dispatcher step.

Each step also records that the child group keeps the carrier of the retained rows with the
new hierarchy (`hkeep`), so that the children keep the row record, the floor mode and `h`
(`Run.dispatch`, `hbk`). This holds when the blocks lie above the retained columns and the
exposure keeps the old levels (`PrimitiveQuotient.kernel_keeps`, `productRed_keeps`,
`Workspace/Algorithm/DispatchKeep.lean`): the child group contains every column-fixing
element (Section A.4: "use full preimages of all quotient restrictions. This keeps the entire
kernel `J`"). -/
inductive DispatchStep (P : Params) {Ω C : Type} (S : State Ω C) : Type
  | enumeration (Q : PrimitiveQuotient S) (fin : Finite Ω) (htr : S.Transitive)
      (hsmall : Q.Small P.a) (reps : CosetReps S.G Q.kernel)
      (hkeep : CarrierOK Q.kernel S.dom S.rows (Q.pre ++ Q.top :: Q.post))
  | product (Q : PrimitiveQuotient S) (fin : Finite Ω)
      (c : Q.ProductChoice) (reps : CosetReps S.G (Q.productRed P c).K)
      (hkeep : CarrierOK (Q.productRed P c).K S.dom S.rows (Q.productRed P c).hier')

namespace DispatchStep

variable {P : Params} {S : State Ω C} (I : DispatchStep P S)

/-- The primitive quotient of the step. -/
def quotient : PrimitiveQuotient S :=
  match I with
  | .enumeration Q _ _ _ _ _ => Q
  | .product Q _ _ _ _ => Q

/-- **The reduction of the step**, computed from its primitive quotient. -/
noncomputable def red : Reduction P S :=
  match I with
  | .enumeration Q _ htr hs reps _ => (Q.enumeration P htr hs).withReps rfl reps
  | .product Q _ c reps _ => (Q.productRed P c).withReps rfl reps

/-! The data of the reduction, read off `red`. -/

/-- The kind of the reduction. -/
noncomputable def kind : DispatchKind := I.red.kind
/-- The child group. -/
noncomputable def K : Subgroup (Perm Ω) := I.red.K
theorem K_le : I.K ≤ S.G := I.red.K_le
/-- The number of cosets. -/
noncomputable def n : ℕ := I.red.n
/-- The coset representatives. -/
noncomputable def τ : Fin I.n → Perm Ω := I.red.τ
theorem τ_mem (j : Fin I.n) : I.τ j ∈ S.G := I.red.τ_mem j
theorem cover : (S.G : Set (Perm Ω)) ⊆ ⋃ j, I.τ j • (I.K : Set (Perm Ω)) := I.red.cover
/-- The hierarchy of the children. -/
noncomputable def hier' : List (Interval Ω) := I.red.hier'
theorem Q_le : State.hierQ I.hier' ≤ State.hierQ S.hier := I.red.Q_le
theorem facts : DispatchFacts P S I.K I.n I.hier' I.kind := I.red.facts

/-- **The step is determined by its quotient.** The child group is the block kernel of the
quotient and the children keep the exposed hierarchy (enumeration), or the child group is the
coordinate subgroup of the chosen product structure and the interval of the quotient is split
into its `r` coordinate intervals (product). -/
theorem K_hier'_eq :
    (∃ Q fin htr hs reps hk, I = .enumeration Q fin htr hs reps hk ∧ I.K = Q.kernel ∧
      I.hier' = Q.pre ++ Q.top :: Q.post) ∨
    (∃ Q fin c reps hk, I = .product Q fin c reps hk ∧
      ∃ (m k r : ℕ) (e : Fin Q.d ≃ (Fin r → Product.KSet m k))
        (hS : Q.ProductStructure m k r e) (hb : 2 ≤ m.choose k), 2 ≤ r ∧
        I.K = Q.coordinateGroup e hS hb ∧
        I.hier' = Q.pre ++ Q.coordHier e ++ Q.post) := by
  cases I with
  | enumeration Q fin htr hs reps hk => exact Or.inl ⟨Q, fin, htr, hs, reps, hk, rfl, rfl, rfl⟩
  | product Q fin c reps hk =>
    exact Or.inr ⟨Q, fin, c, reps, hk, rfl, _, _, _, c.e, c.hS, Q.two_le_choose c.e, c.hr, rfl, rfl⟩

/-- **Every dispatcher step is proper**: some element of the current group lies outside the
child group. For an enumeration the child group is the kernel of a primitive action on at least
two blocks; for a product refinement it is the coordinate subgroup, and a primitive group
permutes the coordinates (`PrimitiveQuotient.exists_not_mem_coordinateGroup`). -/
theorem exists_not_mem_K : ∃ g ∈ S.G, g ∉ I.K := by
  cases I with
  | enumeration Q fin htr hs reps _ => exact Q.exists_not_mem_kernel
  | product Q fin c reps _ =>
    exact Q.exists_not_mem_coordinateGroup _ c.hS (Q.two_le_choose c.e) c.hr

/-- **The child group keeps the carrier** of the retained rows with the new hierarchy. -/
theorem keeps : CarrierOK I.K S.dom S.rows I.hier' := by
  cases I with
  | enumeration Q fin htr hs reps hk => exact hk
  | product Q fin c reps hk => exact hk

end DispatchStep

/-- The outcome of the dispatcher on a primitive quotient: a reduction, or the single-factor
case of a quotient that fails the integer small test (`SmallZ`) and is not a product with at
least two coordinates, where Algorithm 5 normalizes. -/
inductive DispatchOutcome (P : Params) {Ω C : Type} (S : State Ω C) (Q : PrimitiveQuotient S) :
    Type 1
  | step (I : DispatchStep P S)
  | single (hs : ¬ Q.SmallZ P.smallExp) (hp : ¬ Q.ProductCase) (h : Q.SingleFactor)

namespace PrimitiveQuotient

variable {S : State Ω C} (Q : PrimitiveQuotient S)

open Classical in
/-- **The dispatcher** (Algorithm 5): enumerate if the quotient is small; otherwise refine the
product if it has `r ≥ 2` coordinates; otherwise it is a single factor. This dispatcher decides
with the real test `Small`; it is used only to show that runs exist. A single factor that fails
`Small` also fails the integer test `SmallZ`, which is what `Run.normalize` asks. -/
noncomputable def dispatch [hfin : Finite Ω] (hM : GI.Cited.MarotiPrimitive) (P : Params)
    (ha : 128 ≤ P.a) (htr : S.Transitive)
    (hke : CarrierOK Q.kernel S.dom S.rows (Q.pre ++ Q.top :: Q.post))
    (hkp : ∀ c : Q.ProductChoice, CarrierOK (Q.productRed P c).K S.dom S.rows (Q.productRed P c).hier') :
    DispatchOutcome P S Q :=
  if hs : Q.Small P.a then .step (.enumeration Q hfin htr hs (CosetReps.default _ _) hke)
  else if hp : Q.ProductCase then
    .step (.product Q hfin (Q.defaultProductChoice hp) (CosetReps.default _ _) (hkp _))
  else .single (Q.not_smallZ_of_not_small (P.smallExp_le (by linarith)) hs) hp (by
    rcases Q.dispatch_cases hM ha with h | h | h
    · exact absurd h hs
    · exact absurd h hp
    · exact h)

/-- The step that the dispatcher returns carries the quotient it was called on. -/
theorem dispatch_quotient [Finite Ω] (hM : GI.Cited.MarotiPrimitive) (P : Params)
    (ha : 128 ≤ P.a) (htr : S.Transitive) {hke hkp} {I : DispatchStep P S}
    (h : Q.dispatch hM P ha htr hke hkp = .step I) : I.quotient = Q := by
  unfold dispatch at h
  split_ifs at h <;> cases h <;> rfl

end PrimitiveQuotient

end GI.Algorithm
