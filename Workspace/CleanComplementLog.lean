import Workspace.CleanComplementLinear
import Workspace.Paper.SupportThresholds

/-! (LG2) of Theorem A.17 under the logarithmic threshold (LG1).

The paper's proof (`thm:logarithmic-clean-complement`, first paragraph):
for a `k`-set `T` and a block `B_j` with `j ∉ T`, the group
`L_T[B_j]` has the transitive normal subgroup `K[B_j]`, and its quotient is a
homomorphic image of `L_T/K ≅ Alt(k)`. By simplicity it is trivial or
`Alt(k)`, and Lemma A.15 excludes `Alt(k)`. Hence `L_T[B_j] = K[B_j]`, so the
pointwise stabilizer of `B_j` maps onto `Alt(T)`. Intersecting these normal
subgroups over all `j ∉ T` keeps the surjection, because `Alt(k)` is perfect.

Here `L_T` is realized as the pullback `localSource` of
`Workspace/CleanComplementLG2.lean`, which carries its map onto `Alt(Fin k)`. -/

namespace GI

open Equiv

/-- The paper's step "`L_T[B_j] = K[B_j]`, hence `(L_T)_{(B_j)}` maps onto the
alternating quotient", for an abstract group `U` with a quotient map `q` onto
`Alt(k)` (kernel playing the role of `K`) and an action `f` on one block `B`.

Lemma A.15 is applied to `E = f(U)` and its normal subgroup `f(ker q)`. -/
theorem kernel_surjects_of_transitive_kernel (hcite : GI.Cited.TransitiveAffected)
    {U : Type*} [Group U] {B : Type} [Fintype B] {k : ℕ}
    (hthr : max 8 (2 + Real.logb 2 (Fintype.card B)) < (k : ℝ))
    (q : U →* alternatingGroup (Fin k)) (hq : Function.Surjective q)
    (f : U →* Perm B) (htrans : ∀ x y : B, ∃ g : U, g ∈ q.ker ∧ f g x = y) :
    f.ker.map q = ⊤ := by
  classical
  have hk : 9 ≤ k := by
    have : (8 : ℝ) < k := lt_of_le_of_lt (le_max_left _ _) hthr
    exact_mod_cast this
  letI : IsSimpleGroup (alternatingGroup (Fin k)) := AlternatingSimple.isSimple_fin (by omega)
  -- `E = L_T[B]` and its normal subgroup `N = K[B]`.
  let E : Subgroup (Perm B) := f.range
  let N : Subgroup (Perm B) := q.ker.map f
  have hNE : N ≤ E := by
    rintro _ ⟨u, _, rfl⟩
    exact ⟨u, rfl⟩
  haveI hNn : (N.subgroupOf E).Normal := by
    constructor
    rintro ⟨x, hx⟩ hmem ⟨_, u, rfl⟩
    obtain ⟨n, hn, hfn⟩ := Subgroup.mem_subgroupOf.mp hmem
    rw [Subgroup.mem_subgroupOf]
    change f u * x * (f u)⁻¹ ∈ N
    change f n = x at hfn
    rw [← hfn, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨u * n * u⁻¹, (inferInstance : q.ker.Normal).conj_mem n hn u, rfl⟩
  -- The quotient map `U → E/N`; it kills `ker q`.
  let π : U →* E ⧸ N.subgroupOf E := (QuotientGroup.mk' _).comp f.rangeRestrict
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective _).comp f.rangeRestrict_surjective
  have hker : q.ker ≤ π.ker := by
    intro u hu
    change (QuotientGroup.mk (f.rangeRestrict u) : E ⧸ N.subgroupOf E) = 1
    rw [QuotientGroup.eq_one_iff]
    exact ⟨u, hu, rfl⟩
  -- `E/N` is a homomorphic image of `Alt(k)`.
  let ψ := HomDescent.factor q hq π hker
  have hψ : Function.Surjective ψ := HomDescent.factor_surjective q hq π hker hπ
  rcases (inferInstance : ψ.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · -- The quotient is `Alt(k)`: Lemma A.15 gives `k ≤ max 8 (2 + log₂ |B|)`.
    exfalso
    have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hbot
    haveI : MulAction.IsPretransitive N B := by
      constructor
      intro x y
      obtain ⟨g, hg, hxy⟩ := htrans x y
      exact ⟨⟨f g, g, hg, rfl⟩, hxy⟩
    let e : E ⧸ N.subgroupOf E ≃* alternatingGroup (Fin k) :=
      (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩).symm
    have hle := GI.Paper.lem_transitive_kernel_giant_threshold hcite E N hNE e
    linarith
  · -- The quotient is trivial: `L_T[B] = K[B]`.
    have hall : ∀ u : U, f u ∈ N := by
      intro u
      have hu : π u = 1 := by
        rw [← HomDescent.factor_apply q hq π hker u]
        have hmem : q u ∈ ψ.ker := htop ▸ Subgroup.mem_top (q u)
        exact hmem
      change (QuotientGroup.mk (f.rangeRestrict u) : E ⧸ N.subgroupOf E) = 1 at hu
      have hu' := (QuotientGroup.eq_one_iff _).mp hu
      exact Subgroup.mem_subgroupOf.mp hu'
    -- Match the action of `u` on `B` by an element of `K` and cancel it.
    apply eq_top_iff.mpr
    intro p _
    obtain ⟨u, rfl⟩ := hq p
    obtain ⟨n, hn, hfn⟩ := hall u
    refine ⟨u * n⁻¹, ?_, ?_⟩
    · change f (u * n⁻¹) = 1
      rw [map_mul, map_inv, hfn, mul_inv_cancel]
    · change q (u * n⁻¹) = q u
      rw [map_mul, map_inv, hn, inv_one, mul_one]

/-- Intersecting the pointwise block stabilizers: if each one maps onto `Alt(k)`,
some element with a prescribed image acts trivially on every block. The
intersection keeps the surjection because `Alt(k)` is perfect. -/
theorem simultaneous_lift_of_kernels_surject {U J : Type*} [Group U] [Fintype J]
    (B : J → Type*) {k : ℕ} (hk : 5 ≤ k)
    (q : U →* alternatingGroup (Fin k)) (hq : Function.Surjective q)
    (f : ∀ j, U →* Perm (B j)) (hm : ∀ j, (f j).ker.map q = ⊤)
    (p : alternatingGroup (Fin k)) :
    ∃ g : U, q g = p ∧ ∀ j, f j g = 1 := by
  classical
  let Ks := Finset.univ.toList.map (fun j => (f j).ker)
  have hn : ∀ K ∈ Ks, K.Normal := by
    intro K hK
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hK
    infer_instance
  have hm' : ∀ K ∈ Ks, K.map q = ⊤ := by
    intro K hK
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hK
    exact hm j
  letI : IsSimpleGroup (alternatingGroup (Fin k)) := AlternatingSimple.isSimple_fin hk
  have hmap := intersection_surjects q hq
    (simple_nonabelian_perfect (AlternatingSimple.nonabelian_fin hk)) Ks hn hm'
  have hp : p ∈ (commonKernel Ks).map q := by rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨g, hg, hgp⟩ := hp
  refine ⟨g, hgp, ?_⟩
  intro j
  exact (mem_localization_commonKernel_iff Ks g).mp hg (f j).ker
    (List.mem_map.mpr ⟨j, by simp, rfl⟩)

/-- The hypothesis of Theorem A.17 that the block kernel `K` is transitive on
each block. -/
def CleanBlockAction.KernelTransitive {I V : Type*} [Fintype I] [DecidableEq I]
    {G : Subgroup (Perm V)} (A : CleanBlockAction G I) : Prop :=
  ∀ x y : V, A.label x = A.label y → ∃ g : G, A.top g = 1 ∧ g.val x = y

namespace CleanLocalization

variable {I : Type*} {V : Type} [Fintype I] [DecidableEq I]
variable {G : Subgroup (Perm V)} (A : CleanBlockAction G I)

/-- (LG2) for one `k`-set `T` under the logarithmic threshold: every even top
permutation supported on `T` lifts to an element fixing every point outside
the blocks of `T`. The threshold is needed only for the blocks outside `T`. -/
theorem localLiftAvailable_of_transitive_kernel (hcite : GI.Cited.TransitiveAffected)
    [Fintype V] (hker : A.KernelTransitive) (T : Finset I) {k : ℕ} (e : Fin k ≃ T)
    (hk : 5 ≤ k) (hthr : ∀ i, i ∉ T →
      max 8 (2 + Real.logb 2 (Fintype.card {x : V // A.label x = i})) < (k : ℝ)) :
    LocalLiftAvailable A (T : Set I) := by
  classical
  intro p hp
  obtain ⟨s, hs⟩ := supportedTop_covers T e p hp
  obtain ⟨g, hg, hfix⟩ := simultaneous_lift_of_kernels_surject
    (fun j : {i : I // i ∉ T} => {x : V // A.label x = j.val}) hk
    (localTop A T e) (localTop_surjective A T e) (outsideAction A T e)
    (fun j => kernel_surjects_of_transitive_kernel hcite (hthr j.val j.property)
      (localTop A T e) (localTop_surjective A T e) (outsideAction A T e j) (by
        intro x y
        obtain ⟨g, hg1, hgxy⟩ := hker x.val y.val (x.property.trans y.property.symm)
        refine ⟨⟨(g, 1), ?_⟩, rfl, ?_⟩
        · change A.top g = supportedTop T e 1
          rw [hg1, map_one]
        · exact Subtype.ext hgxy)) s
  change g.val.2 = s at hg
  refine ⟨g.val.1, ?_, ?_⟩
  · exact g.property.trans ((congrArg (supportedTop T e) hg).trans hs)
  · intro x hx
    let j : {i : I // i ∉ T} := ⟨A.label x, hx⟩
    have he := congrArg
      (fun f : Perm {y : V // A.label y = j.val} => (f ⟨x, rfl⟩).val) (hfix j)
    exact he

end CleanLocalization
end GI
